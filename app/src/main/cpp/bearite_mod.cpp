/*
 * Встроенный мод Bearite (libbearite_mod.so). Собирается вместе с лаунчером и грузится в игру как обычный
 * нативный мод, подтверждать его не нужно.
 *
 * Делает движок карт: читает файлы <filesDir>/maps/<id>.map, которые правятся во вкладке «Карты» меню Bearite,
 * и строит по ним объекты в текущей сцене (примитивы Unity с цветом и коллайдером). Изменения файла
 * применяются на лету. Состояние движка пишется в maps/_state.txt (сцена, позиция камеры, ошибки),
 * его читает редактор.
 *
 * Карта может быть «отдельным миром» (world=1): тогда остальной мир скрывается (рендереры и коллайдеры
 * выключаются), игрок переносится на точку появления карты, небо заливается цветом карты. При выходе всё
 * возвращается. У объектов могут быть свои текстуры: сырые RGBA-файлы из maps/textures/<id>.tex.
 *
 * Все вызовы Unity должны идти из главного потока, поэтому движок «тикает» из хуков на Time.get_*,
 * которые игра вызывает каждый кадр. Camera.get_main не трогаем: его перехватывают другие моды (например зум),
 * а Dobby не умеет вешать два хука на одну функцию.
 */
#include <cmath>
#include <algorithm>
#include <dirent.h>
#include <sys/stat.h>
#include <time.h>
#include <unistd.h>

#include <atomic>
#include <cstdarg>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <map>
#include <mutex>
#include <string>
#include <unordered_set>
#include <vector>

#include "bearite_api.h"
#include "bearite_il2cpp.h"

namespace {

const BeariteApi* A = nullptr;
const char* ID = "bearite";

// ------------------------------------------------------------------ IL2CPP

// в Unity 6 GC-handle - 64-битное значение (указатель), uint32 его обрезает и ломает
uintptr_t (*gch_new)(void*, int);
void* (*gch_target)(uintptr_t);
void (*gch_free)(uintptr_t);
void* (*obj_unbox)(void*);
void* (*obj_class)(void*);
const char* (*class_name)(void*);
const uint16_t* (*str_chars)(void*);
int (*str_len)(void*);
void* (*class_type)(void*);
void* (*type_object)(void*);
void* (*class_methods)(void*, void**);
const char* (*method_name)(void*);
uint32_t (*method_pcount)(void*);
void* (*method_param)(void*, uint32_t);
void* (*class_from_type)(void*);
void* (*obj_new)(void*);
void* (*arr_new)(void*, uintptr_t);
void* (*get_corlib)();

template <typename T>
T sym(const char* n) { return reinterpret_cast<T>(A->il2cpp_symbol(n)); }

void logf_(const char* fmt, ...) __attribute__((format(printf, 1, 2)));
void logf_(const char* fmt, ...) {
    char buf[400];
    va_list ap;
    va_start(ap, fmt);
    vsnprintf(buf, sizeof buf, fmt, ap);
    va_end(ap);
    A->log(ID, buf);
}

int g_exc_logged = 0;
bool g_in_sync = false;       // идёт построение объектов: каждый вызов пишем в _guard
// Il2CppArray на 64 битах: заголовок объекта 16 + bounds 8 + max_length 8, дальше элементы
inline uintptr_t arr_len(void* a) { return *(const uintptr_t*)((const uint8_t*)a + 24); }
inline void* arr_elem(void* a, size_t size, uintptr_t i) { return (uint8_t*)a + 32 + size * i; }
bool g_crumbs = true;         // false: в длинных циклах не пишем хлебную крошку на каждый вызов
std::string g_guardPath;      // maps/_guard
std::string g_ctx;            // "карта/объект" для хлебных крошек

/** Пишет, что именно вызываем сейчас. Если игра упадёт, файл покажет последний шаг. */
void breadcrumb(void* m, void* obj) {
    if (!g_in_sync || !g_crumbs || g_guardPath.empty() || !m) return;
    FILE* f = fopen(g_guardPath.c_str(), "w");
    if (!f) return;
    void* k = obj ? obj_class(obj) : nullptr;
    fprintf(f, "%s::%s | %s", k ? class_name(k) : "static", method_name(m), g_ctx.c_str());
    fclose(f);
}

/** Вызов управляемого метода. ok=false при исключении (первые несколько пишем в лог). */
void* inv(void* m, void* obj, void** args = nullptr, bool* ok = nullptr) {
    void* exc = nullptr;
    void* r = nullptr;
    breadcrumb(m, obj);
    if (m) r = bearite_il2.runtime_invoke(m, obj, args, &exc);
    if (ok) *ok = m != nullptr && exc == nullptr;
    if (exc && g_exc_logged < 12) {
        ++g_exc_logged;
        void* k = obj_class(exc);
        logf_("исключение в управляемом методе: %s", k ? class_name(k) : "?");
    }
    return exc ? nullptr : r;
}

void* find_method_p0(void* klass, const char* name, int argc, const char* p0) {
    if (!klass) return nullptr;
    void* it = nullptr;
    while (void* m = class_methods(klass, &it)) {
        if (strcmp(method_name(m), name) != 0 || (int)method_pcount(m) != argc) continue;
        if (!p0) return m;
        void* k = class_from_type(method_param(m, 0));
        if (k && strcmp(class_name(k), p0) == 0) return m;
    }
    return nullptr;
}

/** Метод по имени и именам типов всех параметров (.ctor для конструкторов). */
void* find_method_types(void* klass, const char* name, std::initializer_list<const char*> types) {
    if (!klass) return nullptr;
    void* it = nullptr;
    while (void* m = class_methods(klass, &it)) {
        if (strcmp(method_name(m), name) != 0 || method_pcount(m) != types.size()) continue;
        bool ok = true;
        uint32_t i = 0;
        for (const char* t : types) {
            void* k = class_from_type(method_param(m, i++));
            if (!k || strcmp(class_name(k), t) != 0) { ok = false; break; }
        }
        if (ok) return m;
    }
    return nullptr;
}

void dump_class(const char* ns, const char* name) {
    void* k = bearite_find_class(ns, name);
    if (!k) {
        logf_("класса %s.%s нет в игре", ns, name);
        return;
    }
    std::string s;
    void* it = nullptr;
    int n = 0;
    while (void* m = class_methods(k, &it)) {
        if (n++ > 60) break;
        s += method_name(m);
        s += '/';
        s += std::to_string(method_pcount(m));
        s += ' ';
    }
    logf_("методы %s.%s: %s", ns, name, s.c_str());
}

/** Разведка: классы игры, в имени которых есть слова про уровни, запуск, переходы, окна. Пишет в лог методы и поля. */
void scan_classes() {
    auto img_count = sym<size_t (*)(void*)>("il2cpp_image_get_class_count");
    auto img_class = sym<void* (*)(void*, size_t)>("il2cpp_image_get_class");
    auto cls_ns = sym<const char* (*)(void*)>("il2cpp_class_get_namespace");
    auto cls_parent = sym<void* (*)(void*)>("il2cpp_class_get_parent");
    auto cls_fields = sym<void* (*)(void*, void**)>("il2cpp_class_get_fields");
    auto fld_name = sym<const char* (*)(void*)>("il2cpp_field_get_name");
    auto fld_type = sym<void* (*)(void*)>("il2cpp_field_get_type");
    auto type_name = sym<const char* (*)(void*)>("il2cpp_type_get_name");
    auto asm_image = sym<void* (*)(void*)>("il2cpp_assembly_get_image");
    auto img_name = sym<const char* (*)(void*)>("il2cpp_image_get_name");
    auto dom_get = sym<void* (*)()>("il2cpp_domain_get");
    auto dom_asms = sym<void** (*)(void*, size_t*)>("il2cpp_domain_get_assemblies");
    if (!img_count || !img_class || !cls_ns || !dom_get || !dom_asms || !asm_image) { logf_("разведка классов: нет функций il2cpp"); return; }
    static const char* words[] = {"launch", "vote", "level", "transition", "fade", "loading", "scene", "portal", "popup",
                                  "dialog", "panel", "select", "travel", "teleport", "warp", "curtain", "wipe", "cutscene",
                                  "worldmap", "stage", "player", "pause", "ingamemenu", "gamemenu", "mainmenu"};
    static const char* deep[] = {"PauseMenuManager", "PauseUI", "PauseManager", "PauseWindow", "PauseController", "GameManager", "LaunchPlatform", "VoteTrigger", "LevelStartUI", "LevelLoader", "LevelEntrance", "TranslateUI", "LevelData", "LevelTransitionTrigger"};
    size_t na = 0;
    void** asms = dom_asms(dom_get(), &na);
    int shown = 0;
    auto chunked = [&](const std::string& head, const std::string& body) {
        // длинные строки режем на куски, чтобы лог их не обрезал
        size_t pos = 0;
        int part = 0;
        do {
            std::string piece = body.substr(pos, 300);
            logf_("%s%s: %s", head.c_str(), part ? " (продолжение)" : "", piece.c_str());
            pos += 300; ++part;
        } while (pos < body.size() && part < 14);
    };
    for (size_t i = 0; i < na && asms; ++i) {
        void* img = asm_image(asms[i]);
        if (!img) continue;
        const char* iname = img_name ? img_name(img) : "?";
        if (!iname || strstr(iname, "Assembly-CSharp") == nullptr) continue;
        size_t n = img_count(img);
        logf_("разведка классов: сборка %s, классов %zu", iname, n);
        for (size_t c = 0; c < n && shown < 300; ++c) {
            void* k = img_class(img, c);
            if (!k) continue;
            const char* nm = class_name(k);
            if (!nm) continue;
            std::string low = nm;
            for (auto& ch : low) ch = (char)tolower((unsigned char)ch);
            bool hit = false, isDeep = false;
            for (auto w : words) if (low.find(w) != std::string::npos) { hit = true; break; }
            for (auto dn : deep) if (strcmp(nm, dn) == 0) isDeep = true;
            if (!hit && !isDeep) continue;
            if (nm[0] == '<') continue;
            ++shown;
            void* par = cls_parent ? cls_parent(k) : nullptr;
            std::string head = std::string("класс ") + (cls_ns ? cls_ns(k) : "") + "." + nm + " : " + (par ? class_name(par) : "-");
            std::string body;
            void* it = nullptr;
            int mc = 0;
            while (void* m = class_methods(k, &it)) {
                if (mc++ >= (isDeep ? 120 : 30)) { body += "…"; break; }
                body += method_name(m);
                if (isDeep && type_name && method_param) {
                    body += '(';
                    for (uint32_t pi = 0; pi < method_pcount(m); ++pi) {
                        void* pt = method_param(m, pi);
                        body += pt ? type_name(pt) : "?";
                        if (pi + 1 < method_pcount(m)) body += ',';
                    }
                    body += ')';
                } else {
                    body += '/';
                    body += std::to_string(method_pcount(m));
                }
                body += ' ';
            }
            if (cls_fields && fld_name && fld_type && type_name) {
                body += "| поля: ";
                void* fit = nullptr;
                int fc = 0;
                while (void* f = cls_fields(k, &fit)) {
                    if (fc++ >= (isDeep ? 90 : 14)) { body += "…"; break; }
                    void* ft = fld_type(f);
                    body += fld_name(f);
                    body += ':';
                    body += ft && type_name ? type_name(ft) : "?";
                    body += ' ';
                }
            }
            chunked(head, body);
        }
    }
    logf_("разведка классов: показано %d", shown);
}

std::string utf8(void* il2str) {
    std::string out;
    if (!il2str) return out;
    const uint16_t* c = str_chars(il2str);
    int n = str_len(il2str);
    for (int i = 0; i < n; ++i) {
        uint32_t u = c[i];
        if (u >= 0xD800 && u < 0xDC00 && i + 1 < n) u = 0x10000 + ((u - 0xD800) << 10) + (c[++i] - 0xDC00);
        if (u < 0x80) out += (char)u;
        else if (u < 0x800) { out += (char)(0xC0 | (u >> 6)); out += (char)(0x80 | (u & 63)); }
        else if (u < 0x10000) { out += (char)(0xE0 | (u >> 12)); out += (char)(0x80 | ((u >> 6) & 63)); out += (char)(0x80 | (u & 63)); }
        else { out += (char)(0xF0 | (u >> 18)); out += (char)(0x80 | ((u >> 12) & 63)); out += (char)(0x80 | ((u >> 6) & 63)); out += (char)(0x80 | (u & 63)); }
    }
    return out;
}

// Методы Unity
struct Fns {
    void *create_primitive, *get_transform, *go_transform, *set_position, *set_scale, *set_euler, *get_position, *get_forward;
    void *cam_main, *set_name, *destroy, *get_active, *set_layer, *get_component, *get_material, *set_color,
        *collider_enabled, *get_scene, *scene_name;
    void *type_renderer, *type_collider;
    void* get_root;
    // текстуры
    void *tex2d, *set_main_tex, *set_main_tex_scale, *set_hideflags, *image_conv;
    // отдельный мир
    void *get_iid, *get_parent, *get_child_count, *get_gameobject, *find_tag, *find_obj, *find_objs, *find_objs_sorted;
    void *rend_set_enabled, *rend_get_enabled, *col_get_enabled, *cam_set_flags, *cam_get_flags, *cam_set_bg, *cam_get_bg;
    void *type_cc, *type_kcm, *kcm_set_pos;
    void *instantiate, *get_local_scale, *get_layer, *load_scene;
    int load_arity;
    void *go_ctor_str, *set_active, *set_parent, *instantiate_parent, *destroy_imm;
    void *type_mono, *get_comps_children, *beh_get_enabled, *beh_set_enabled, *col_is_trigger;
    // диагностика и запасной путь для текстур
    void *mat_has_prop, *mat_set_tex, *mat_set_scale, *mat_get_shader, *get_name, *mat_get_main_tex, *shader_find,
        *rend_set_material, *mat_class, *mat_ctor_shader, *rend_bounds;
} F{};

struct V3 { float x, y, z; };
struct Col { float r, g, b, a; };

long long now_ms_fwd();

// ------------------------------------------------------------------ карты

struct Obj {
    std::string name, shape;
    float p[3] = {0, 0, 0}, s[3] = {1, 1, 1}, r[3] = {0, 0, 0};
    unsigned color = 0x8D5338;
    bool solid = true;
    std::string tex;
    float tile[2] = {1, 1};
    std::string dest;       // круг телепорта: "" = точка этой карты, "@exit" = выход из мира, иначе id карты
    float dp[3] = {0, 0, 0};
    bool clone = false;     // с bind: поставить копию платформы на месте круга, а не занимать оригинал
    std::string bind;       // имя родного объекта игры, который этот круг «занимает» (пусто = свой круг)
};

struct MapSpec {
    std::string id, name, scene;
    std::string cover, desc;  // обложка (id текстуры) и описание для окна уровня
    bool enabled = true;
    float off[3] = {0, 0, 0};
    float scale = 1;
    int layer = 0;
    bool world = false;
    unsigned sky = 0x87B8E8;
    float spawn[3] = {0, 2, 0};
    std::vector<Obj> objs;
};

/** То, что реально применено к объекту в сцене. */
struct Live {
    uintptr_t h = 0;  // GC-handle на GameObject, 0 = объекта нет
    std::string shape;
    bool solid = true;
    int layer = 0;
    std::string name;
    float pos[3] = {1e9f, 0, 0}, size[3] = {0, 0, 0}, rot[3] = {1e9f, 0, 0};
    unsigned color = 0xFFFFFFFF;
    std::string tex;
    float tile[2] = {0, 0};
    int tid = 0;  // instance id Transform объекта: по нему отличаем свои объекты от чужих
    // привязка к родному объекту игры
    uintptr_t nat = 0;                                  // handle на Transform родного круга
    std::vector<std::pair<uintptr_t, int>> natOff;      // что мы выключили у него: (handle, 0 = скрипт, 1 = триггер)
    long long natTry = 0;
    bool natHidden = false, natMiss = false, natClone = false;
    bool nativeFull = false;  // копия платформы с родными скриптами: окно, анимацию и загрузку уровня ведёт сама игра
};

std::map<int, std::string> g_cloneWorld;  // instance id корня копии платформы → id мира, куда она ведёт

std::string g_mapsDir;
std::vector<MapSpec> g_specs;
std::map<std::string, std::vector<Live>> g_live;
std::string g_dirStamp = "?";
std::string g_scene;
bool g_dirty = true;
std::string g_status = "unknown";
std::string g_msg;
int g_liveCount = 0;
bool g_engineOk = false;
std::string g_worldWant;  // id карты-мира, которая должна быть активна ("" = нет)
std::string g_worldFile;  // мир, включённый переключателем в файлах
std::string g_pendingWorld;       // мир, который надо открыть после загрузки сцены-хозяина
std::string g_returnScene;        // откуда пришли в сцену-хозяина (туда вернёмся при выходе из мира)
bool g_wantRedirect = false;      // мир только что включили (переключатель/круг): можно перейти в сцену level_1
long long g_lastLoad = 0;
const char* const HOST_SCENE = "level_1";  // сцена, в которой строится любой мир: свежая, без хаба и его скриптов видимости
std::string g_worldRt;    // выбор круга телепорта: "" нет, "@exit" выйти из мира, иначе id мира

/** Мир из файлов: включённый и привязанный к этой сцене (или ни к какой). Мир со сценой level_1 открывается, когда игра сама загрузит уровень. */
void pick_world_file() {
    g_worldFile.clear();
    for (const auto& m : g_specs) if (m.world && m.enabled && (m.scene.empty() || m.scene == g_scene)) { g_worldFile = m.id; break; }
    static std::string lastLogged;
    std::string key = g_scene + "|" + g_worldFile;
    if (key != lastLogged) {
        lastLogged = key;
        std::string all;
        for (const auto& m : g_specs) if (m.world) all += " «" + m.name + "» (" + (m.enabled ? "вкл" : "выкл") + ", сцена: " + (m.scene.empty() ? "любая" : m.scene) + ")";
        logf_("сцена «%s»: мир из файлов = %s; миров всего:%s", g_scene.c_str(), g_worldFile.empty() ? "нет" : g_worldFile.c_str(), all.empty() ? " нет" : all.c_str());
    }
}

void refresh_world_want() {
    std::string w = g_worldRt == "@exit" ? "" : !g_worldRt.empty() ? g_worldRt : g_worldFile;
    if (w != g_worldWant) { g_worldWant = w; g_dirty = true; }
}

float num(const std::string& s, float d) {
    char* e = nullptr;
    double v = strtod(s.c_str(), &e);
    return e && e != s.c_str() ? (float)v : d;
}

std::vector<std::string> split_tab(const std::string& s) {
    std::vector<std::string> out;
    size_t st = 0;
    while (true) {
        size_t p = s.find('\t', st);
        if (p == std::string::npos) { out.push_back(s.substr(st)); break; }
        out.push_back(s.substr(st, p - st));
        st = p + 1;
    }
    return out;
}

bool parse_map(const std::string& id, const std::string& path, MapSpec& m) {
    FILE* f = fopen(path.c_str(), "r");
    if (!f) return false;
    m.id = id;
    m.name = id;
    char line[1024];
    while (fgets(line, sizeof line, f)) {
        std::string l = line;
        while (!l.empty() && (l.back() == '\n' || l.back() == '\r')) l.pop_back();
        if (l.empty()) continue;
        if (l.compare(0, 2, "O\t") == 0) {
            auto p = split_tab(l);
            if (p.size() < 14) continue;
            Obj o;
            o.name = p[1];
            o.shape = p[2];
            for (int i = 0; i < 3; ++i) { o.p[i] = num(p[3 + i], 0); o.s[i] = num(p[6 + i], 1); o.r[i] = num(p[9 + i], 0); }
            o.color = (unsigned)strtoul(p[12].c_str(), nullptr, 16) & 0xFFFFFF;
            o.solid = p[13] == "1";
            if (p.size() > 14) o.tex = p[14];
            if (p.size() > 16) { o.tile[0] = num(p[15], 1); o.tile[1] = num(p[16], 1); }
            if (p.size() > 17) o.dest = p[17];
            if (p.size() > 20) for (int i = 0; i < 3; ++i) o.dp[i] = num(p[18 + i], 0);
            if (p.size() > 21) o.bind = p[21];
            if (p.size() > 22) o.clone = p[22] == "1";
            m.objs.push_back(o);
            continue;
        }
        size_t eq = l.find('=');
        if (eq == std::string::npos) continue;
        std::string k = l.substr(0, eq), v = l.substr(eq + 1);
        if (k == "name") m.name = v;
        else if (k == "enabled") m.enabled = v == "1" || v == "true";
        else if (k == "scene") m.scene = v;
        else if (k == "cover") m.cover = v;
        else if (k == "desc") m.desc = v;
        else if (k == "ox") m.off[0] = num(v, 0);
        else if (k == "oy") m.off[1] = num(v, 0);
        else if (k == "oz") m.off[2] = num(v, 0);
        else if (k == "scale") m.scale = num(v, 1);
        else if (k == "layer") m.layer = atoi(v.c_str());
        else if (k == "world") m.world = v == "1" || v == "true";
        else if (k == "sky") m.sky = (unsigned)strtoul(v.c_str(), nullptr, 16) & 0xFFFFFF;
        else if (k == "spx") m.spawn[0] = num(v, 0);
        else if (k == "spy") m.spawn[1] = num(v, 2);
        else if (k == "spz") m.spawn[2] = num(v, 0);
    }
    fclose(f);
    if (m.scale < 0.01f) m.scale = 0.01f;
    return true;
}

/** Перечитывает папку карт, если файлы изменились. */
void reload_maps() {
    DIR* d = opendir(g_mapsDir.c_str());
    if (!d) return;
    std::vector<std::string> names;
    std::string stamp;
    while (dirent* e = readdir(d)) {
        size_t n = strlen(e->d_name);
        if (n < 5 || strcmp(e->d_name + n - 4, ".map") != 0 || e->d_name[0] == '.') continue;
        struct stat st;
        std::string path = g_mapsDir + "/" + e->d_name;
        if (stat(path.c_str(), &st) != 0) continue;
        names.push_back(e->d_name);
        stamp += e->d_name;
        stamp += ':' + std::to_string((long long)st.st_mtim.tv_sec * 1000000000LL + st.st_mtim.tv_nsec) + ':' +
                 std::to_string((long long)st.st_size) + ';';
    }
    closedir(d);
    if (stamp == g_dirStamp) return;
    g_dirStamp = stamp;
    std::vector<MapSpec> specs;
    for (const auto& n : names) {
        MapSpec m;
        if (parse_map(n.substr(0, n.size() - 4), g_mapsDir + "/" + n, m)) specs.push_back(std::move(m));
    }
    g_specs = std::move(specs);
    {
        std::string before = g_worldFile;
        pick_world_file();
        if (!g_worldFile.empty() && g_worldFile != before) g_wantRedirect = true;
    }
    g_worldRt.clear();  // карты правили: выбор круга телепорта сбрасывается
    refresh_world_want();
    g_dirty = true;
}

// ------------------------------------------------------------- объекты в сцене

void* target(uintptr_t h) { return h ? gch_target(h) : nullptr; }

/** Показывает или прячет собственный диск круга (когда его место занимает родная платформа). */
void set_disc(Live& L, bool visible) {
    void* go = L.h ? target(L.h) : nullptr;
    if (!go || !F.type_renderer || !F.get_component || !F.rend_set_enabled) return;
    void* b[1] = {F.type_renderer};
    void* rend = inv(F.get_component, go, b);
    if (!rend) return;
    uint8_t on = visible ? 1 : 0;
    void* c[1] = {&on};
    inv(F.rend_set_enabled, rend, c);
    L.natHidden = !visible;
}

int inst_id(void* o);
void release_native(Live& L, bool restore) {
    for (auto& e : L.natOff) {
        if (restore) {
            void* o = target(e.first);
            void* fn = e.second == 0 ? F.beh_set_enabled : F.collider_enabled;
            if (o && fn) { uint8_t on = 1; void* a[1] = {&on}; inv(fn, o, a); }
        }
        gch_free(e.first);
    }
    L.natOff.clear();
    if (L.nat) {
        if (L.natClone && restore && F.destroy && F.get_gameobject) {  // копию платформы убираем вместе с картой
            void* tr = target(L.nat);
            if (tr) g_cloneWorld.erase(inst_id(tr));
            void* go = tr ? inv(F.get_gameobject, tr) : nullptr;
            if (go) { void* a[1] = {go}; inv(F.destroy, nullptr, a); }
        }
        gch_free(L.nat);
        L.nat = 0;
    }
    L.natClone = false;
    L.nativeFull = false;
    if (L.natHidden && restore) set_disc(L, true);
    L.natHidden = false;
}

void destroy_live(Live& L) {
    if (!L.h) return;
    release_native(L, true);  // копию платформы убираем и возвращаем диск, пока объект ещё жив
    void* go = target(L.h);
    if (go && F.destroy) {
        void* a[1] = {go};
        inv(F.destroy, nullptr, a);
    }
    gch_free(L.h);
    L = Live();
    if (g_liveCount > 0) --g_liveCount;
}

void drop_live(Live& L) {  // объект уже уничтожен Unity (смена сцены): только освобождаем handle
    release_native(L, false);
    if (L.h) { gch_free(L.h); if (g_liveCount > 0) --g_liveCount; }
    L = Live();
}


int inst_id(void* o) {
    if (!o || !F.get_iid) return 0;
    void* r = inv(F.get_iid, o);
    return r ? *(const int*)obj_unbox(r) : 0;
}

// ------------------------------------------------------------------ текстуры

std::map<std::string, uintptr_t> g_tex;  // id -> handle (0 = не удалось загрузить)

void* byte_array(const unsigned char* data, size_t n) {
    static void* byteK = nullptr;
    if (!byteK && get_corlib && bearite_il2.class_from_name) byteK = bearite_il2.class_from_name(get_corlib(), "System", "Byte");
    if (!byteK) byteK = bearite_find_class("System", "Byte");
    if (!byteK || !arr_new) return nullptr;
    void* arr = arr_new(byteK, n);
    if (!arr) return nullptr;
    memcpy(arr_elem(arr, 1, 0), data, n);
    return arr;
}

bool read_file(const std::string& path, std::vector<unsigned char>& out) {
    FILE* f = fopen(path.c_str(), "rb");
    if (!f) return false;
    fseek(f, 0, SEEK_END);
    long n = ftell(f);
    fseek(f, 0, SEEK_SET);
    if (n <= 0 || n > 64 * 1024 * 1024) { fclose(f); return false; }
    out.resize((size_t)n);
    bool ok = fread(out.data(), 1, out.size(), f) == out.size();
    fclose(f);
    return ok;
}

/** Создаёт Texture2D из maps/textures/<id>.tex (сырой RGBA32). Если нет нужных методов, пробует PNG через ImageConversion. */
void* make_texture(const std::string& id) {
    void* k = F.tex2d;
    if (!k || !obj_new) { logf_("текстуры недоступны: нет Texture2D или il2cpp_object_new"); return nullptr; }
    std::vector<unsigned char> raw;
    if (!read_file(g_mapsDir + "/textures/" + id + ".tex", raw) || raw.size() < 8) { logf_("текстура %s: файл не найден", id.c_str()); return nullptr; }
    int w = 0, h = 0;
    memcpy(&w, raw.data(), 4);
    memcpy(&h, raw.data() + 4, 4);
    if (w < 1 || h < 1 || w > 4096 || h > 4096 || raw.size() != (size_t)8 + (size_t)w * h * 4) { logf_("текстура %s: повреждённый файл", id.c_str()); return nullptr; }
    const unsigned char* px = raw.data() + 8;
    size_t pxn = (size_t)w * h * 4;

    void* tex = obj_new(k);
    if (!tex) return nullptr;
    bool ok = false;
    int fmt = 4;      // TextureFormat.RGBA32
    uint8_t mip = 0;  // без мипов: LoadRawTextureData ждёт ровно w*h*4 байт
    if (void* c4 = find_method_types(k, ".ctor", {"Int32", "Int32", "TextureFormat", "Boolean"})) {
        void* a[4] = {&w, &h, &fmt, &mip};
        inv(c4, tex, a, &ok);
    } else if (void* c2 = find_method_types(k, ".ctor", {"Int32", "Int32"})) {
        void* a[2] = {&w, &h};
        inv(c2, tex, a, &ok);
    }
    if (!ok) { logf_("текстура %s: не создался Texture2D", id.c_str()); return nullptr; }

    bool loaded = false;
    const char* how = "";
    if (void* m = find_method_types(k, "LoadRawTextureData", {"Byte[]"})) {
        if (void* arr = byte_array(px, pxn)) { void* a[1] = {arr}; inv(m, tex, a, &loaded); how = "LoadRawTextureData(byte[])"; }
    }
    if (!loaded) if (void* m = find_method_types(k, "LoadRawTextureData", {"IntPtr", "Int32"})) {
        const void* ptr = px;
        int n = (int)pxn;
        void* a[2] = {&ptr, &n};
        inv(m, tex, a, &loaded);
        how = "LoadRawTextureData(IntPtr)";
    }
    if (!loaded) {
        std::vector<unsigned char> png;
        void* ic = F.image_conv;
        void* m = ic ? find_method_types(ic, "LoadImage", {"Texture2D", "Byte[]"}) : nullptr;
        if (m && read_file(g_mapsDir + "/textures/" + id + ".png", png)) {
            if (void* arr = byte_array(png.data(), png.size())) {
                void* a[2] = {tex, arr};
                void* r = inv(m, nullptr, a, &loaded);
                if (loaded && r) loaded = *(const uint8_t*)obj_unbox(r) != 0;
                how = "ImageConversion.LoadImage";
            }
        }
    }
    if (!loaded) { logf_("текстура %s: в игре нет методов загрузки пикселей", id.c_str()); return nullptr; }
    bool applied = false;
    if (void* ap = find_method_types(k, "Apply", {"Boolean", "Boolean"})) {
        uint8_t a1 = 0, a2 = 0;
        void* a[2] = {&a1, &a2};
        inv(ap, tex, a, &applied);
    } else if (void* ap1 = find_method_types(k, "Apply", {"Boolean"})) {
        uint8_t a1 = 0;
        void* a[1] = {&a1};
        inv(ap1, tex, a, &applied);
    } else if (void* ap0 = bearite_il2.class_get_method_from_name(k, "Apply", 0)) {
        inv(ap0, tex, nullptr, &applied);
    }
    if (F.set_hideflags) { int hf = 61; void* a[1] = {&hf}; inv(F.set_hideflags, tex, a); }  // HideAndDontSave: не выгружать при смене сцены
    {
        unsigned long long sr = 0, sg = 0, sb = 0, sa = 0;
        size_t cnt = (size_t)w * h;
        for (size_t i = 0; i < cnt; ++i) { sr += px[i * 4]; sg += px[i * 4 + 1]; sb += px[i * 4 + 2]; sa += px[i * 4 + 3]; }
        logf_("текстура %s загружена (%dx%d, %s, Apply %s), средний цвет RGBA %llu %llu %llu %llu", id.c_str(), w, h, how, applied ? "ok" : "нет",
              sr / cnt, sg / cnt, sb / cnt, sa / cnt);
    }
    return tex;
}

void* get_texture(const std::string& id) {
    auto it = g_tex.find(id);
    if (it != g_tex.end()) return it->second ? target(it->second) : nullptr;
    void* t = make_texture(id);
    g_tex[id] = t ? gch_new(t, 0) : 0;
    return t;
}

void drop_textures() {
    for (auto& kv : g_tex) if (kv.second) gch_free(kv.second);
    g_tex.clear();
}

bool mat_has(void* mat, const char* name) {
    if (!F.mat_has_prop) return false;
    void* a[1] = {bearite_il2.string_new(name)};
    void* r = inv(F.mat_has_prop, mat, a);
    return r && *(const uint8_t*)obj_unbox(r) != 0;
}

void mat_set_tex_named(void* mat, const char* name, void* tx, const Obj& o) {
    if (!F.mat_set_tex) return;
    void* a[2] = {bearite_il2.string_new(name), tx};
    inv(F.mat_set_tex, mat, a);
    if (tx && F.mat_set_scale) {
        struct { float x, y; } v{o.tile[0], o.tile[1]};
        void* c[2] = {bearite_il2.string_new(name), &v};
        inv(F.mat_set_scale, mat, c);
    }
}

std::string shader_name(void* mat) {
    void* sh = F.mat_get_shader ? inv(F.mat_get_shader, mat) : nullptr;
    void* nm = sh && F.get_name ? inv(F.get_name, sh) : nullptr;
    return nm ? utf8(nm) : "?";
}

/** У материала примитива нет слота под текстуру: делаем свой материал на любом подходящем шейдере игры. */
void* texture_material(void* rend, const Obj& o) {
    static const char* names[] = {"Universal Render Pipeline/Lit", "Universal Render Pipeline/Simple Lit", "Universal Render Pipeline/Unlit",
                                  "Standard", "Unlit/Texture", "Mobile/Diffuse", "Legacy Shaders/Diffuse", "Sprites/Default"};
    if (!F.shader_find || !F.mat_class || !F.mat_ctor_shader || !F.rend_set_material || !obj_new) return nullptr;
    for (const char* n : names) {
        void* a[1] = {bearite_il2.string_new(n)};
        void* sh = inv(F.shader_find, nullptr, a);
        if (!sh) continue;
        void* m = obj_new(F.mat_class);
        bool ok = false;
        void* b[1] = {sh};
        inv(F.mat_ctor_shader, m, b, &ok);
        if (!ok || !(mat_has(m, "_BaseMap") || mat_has(m, "_MainTex"))) continue;
        Col c{((o.color >> 16) & 255) / 255.f, ((o.color >> 8) & 255) / 255.f, (o.color & 255) / 255.f, 1.f};
        void* d[1] = {&c};
        if (F.set_color) inv(F.set_color, m, d);
        void* e[1] = {m};
        inv(F.rend_set_material, rend, e);
        logf_("материал с текстурой: свой на шейдере «%s»", n);
        return m;
    }
    logf_("не нашёл шейдер с текстурой среди известных, текстуры на этом материале не видны");
    return nullptr;
}

void apply_texture(Live& L, void* go, const Obj& o) {
    L.tex = o.tex;
    L.tile[0] = o.tile[0];
    L.tile[1] = o.tile[1];
    if (!F.get_component || !F.get_material || !F.type_renderer || !F.set_main_tex) return;
    void* b[1] = {F.type_renderer};
    void* rend = inv(F.get_component, go, b);
    void* mat = rend ? inv(F.get_material, rend) : nullptr;
    if (!mat) return;
    void* tx = o.tex.empty() ? nullptr : get_texture(o.tex);
    if (!o.tex.empty() && !tx) return;  // не загрузилась: повторять при каждом тике не будем
    bool hb = mat_has(mat, "_BaseMap"), hm = mat_has(mat, "_MainTex");
    static bool logged = false;
    if (!logged) {
        logged = true;
        logf_("материал примитива: шейдер «%s», _BaseMap=%d _MainTex=%d", shader_name(mat).c_str(), hb, hm);
    }
    if (tx && !hb && !hm) {
        void* nm = texture_material(rend, o);
        if (nm) { mat = nm; hb = mat_has(mat, "_BaseMap"); hm = mat_has(mat, "_MainTex"); }
    }
    void* a[1] = {tx};
    inv(F.set_main_tex, mat, a);
    if (tx && F.set_main_tex_scale) {
        struct { float x, y; } v{o.tile[0], o.tile[1]};
        void* c[1] = {&v};
        inv(F.set_main_tex_scale, mat, c);
    }
    // на всякий случай задаём слоты явно: mainTexture указывает на один из них, но не у всех шейдеров
    if (hb) mat_set_tex_named(mat, "_BaseMap", tx, o);
    if (hm) mat_set_tex_named(mat, "_MainTex", tx, o);
    static int checks = 0;
    if (tx && checks < 3 && F.mat_get_main_tex) {
        ++checks;
        void* back = inv(F.mat_get_main_tex, mat);
        logf_("текстура %s на объекте: mainTexture после установки %s (_BaseMap=%d _MainTex=%d)", o.tex.c_str(), back ? "задана" : "ПУСТО", hb, hm);
    }
}

int primitive_id(const std::string& s) {
    // UnityEngine.PrimitiveType: Sphere=0, Capsule=1, Cylinder=2, Cube=3, Plane=4, Quad=5
    if (s == "sphere") return 0;
    if (s == "capsule") return 1;
    if (s == "cylinder" || s == "portal") return 2;  // круг телепорта: плоский цилиндр
    if (s == "plane") return 4;
    return 3;
}

bool create_live(Live& L, const Obj& o, const MapSpec& m, const std::string& fullName) {
    int t = primitive_id(o.shape);
    void* a[1] = {&t};
    bool ok = false;
    void* go = inv(F.create_primitive, nullptr, a, &ok);
    if (!go) return false;
    L.h = gch_new(go, 0);
    ++g_liveCount;
    L.shape = o.shape;
    L.solid = o.solid && o.shape != "portal";
    L.layer = m.layer;
    L.name = "";
    L.pos[0] = 1e9f; L.rot[0] = 1e9f; L.size[0] = 0;
    L.color = 0xFFFFFFFF;
    L.tex.clear();
    L.tile[0] = L.tile[1] = 0;
    L.tid = 0;
    if (F.set_layer) { int ly = m.layer; void* b[1] = {&ly}; inv(F.set_layer, go, b); }
    if ((!o.solid || o.shape == "portal") && F.type_collider && F.get_component && F.collider_enabled) {
        void* b[1] = {F.type_collider};
        void* col = inv(F.get_component, go, b);
        if (col) { uint8_t off = 0; void* c[1] = {&off}; inv(F.collider_enabled, col, c); }
    }
    (void)fullName;
    if (F.go_transform) L.tid = inst_id(inv(F.go_transform, go));
    return true;
}

void apply_live(Live& L, const Obj& o, const MapSpec& m, const std::string& fullName) {
    void* go = target(L.h);
    if (!go) return;
    if (L.name != fullName && F.set_name) {
        void* a[1] = {bearite_il2.string_new(fullName.c_str())};
        inv(F.set_name, go, a);
        L.name = fullName;
    }
    void* tr = inv(F.go_transform, go);  // у GameObject свой get_transform, не Component'ский
    if (!tr) return;
    V3 pos{m.off[0] + m.scale * o.p[0], m.off[1] + m.scale * o.p[1], m.off[2] + m.scale * o.p[2]};
    V3 size{m.scale * o.s[0], m.scale * o.s[1], m.scale * o.s[2]};
    V3 rot{o.r[0], o.r[1], o.r[2]};
    if (memcmp(L.pos, &pos, sizeof pos) != 0) {
        void* a[1] = {&pos};
        inv(F.set_position, tr, a);
        memcpy(L.pos, &pos, sizeof pos);
        if (L.natClone && L.nat) if (void* ct = target(L.nat)) inv(F.set_position, ct, a);
    }
    if (memcmp(L.size, &size, sizeof size) != 0) { void* a[1] = {&size}; inv(F.set_scale, tr, a); memcpy(L.size, &size, sizeof size); }
    if (memcmp(L.rot, &rot, sizeof rot) != 0) { void* a[1] = {&rot}; inv(F.set_euler, tr, a); memcpy(L.rot, &rot, sizeof rot); }
    unsigned eff = o.tex.empty() ? o.color : 0xFFFFFFu;  // с текстурой цвет не красит её (иначе картинка тонет в коричневом)
    if (L.color != eff && F.type_renderer && F.get_component && F.get_material && F.set_color) {
        void* b[1] = {F.type_renderer};
        void* rend = inv(F.get_component, go, b);
        void* mat = rend ? inv(F.get_material, rend) : nullptr;
        if (mat) {
            Col c{((eff >> 16) & 255) / 255.f, ((eff >> 8) & 255) / 255.f, (eff & 255) / 255.f, 1.f};
            void* a[1] = {&c};
            inv(F.set_color, mat, a);
            L.color = eff;
        }
    }
    if (L.nat && !L.natHidden) set_disc(L, false);  // свой диск не нужен, пока на его месте родная платформа или её копия
    if (L.tex != o.tex || (!o.tex.empty() && (L.tile[0] != o.tile[0] || L.tile[1] != o.tile[1]))) apply_texture(L, go, o);
}

/** Приводит объекты в сцене в соответствие с картами. */
void sync_all() {
    g_in_sync = true;
    // карты, которых больше нет в файлах
    for (auto it = g_live.begin(); it != g_live.end();) {
        bool found = false;
        for (const auto& s : g_specs) if (s.id == it->first) { found = true; break; }
        if (!found) {
            for (auto& L : it->second) destroy_live(L);
            it = g_live.erase(it);
        } else ++it;
    }
    for (const auto& m : g_specs) {
        auto& live = g_live[m.id];
        bool want = g_engineOk &&
                    (m.world ? m.id == g_worldWant : (m.enabled && g_worldWant.empty() && (m.scene.empty() || m.scene == g_scene)));
        if (!want) {
            for (auto& L : live) destroy_live(L);
            live.clear();
            continue;
        }
        while (live.size() > m.objs.size()) { destroy_live(live.back()); live.pop_back(); }
        live.resize(m.objs.size());
        for (size_t i = 0; i < m.objs.size(); ++i) {
            const Obj& o = m.objs[i];
            Live& L = live[i];
            if (L.h && (L.shape != o.shape || L.solid != (o.solid && o.shape != "portal") || L.layer != m.layer)) destroy_live(L);
            g_ctx = m.id + " объект " + std::to_string(i + 1);
            std::string full = "Bearite/" + m.name + "/" + (o.name.empty() ? std::to_string(i + 1) : o.name);
            if (!L.h && !create_live(L, o, m, full)) {
                g_status = "error";
                g_msg = "не удалось создать объект (см. вкладку «Лог»)";
                continue;
            }
            apply_live(L, o, m, full);
        }
    }
}

// -------------------------------------------------------------- отдельный мир

struct World {
    bool active = false;
    std::string id;
    uintptr_t player = 0;       // handle на Transform игрока
    int protect[3] = {0, 0, 0}; // instance id игрока, его родителя и корня: их потомков не прячем
    float saved[3] = {0, 0, 0};
    std::vector<uintptr_t> hr, hc;  // спрятанные рендереры и коллайдеры
    std::unordered_set<int> hidden;
    std::unordered_set<int> kept;  // уже проверенные и оставленные (игрок, свои объекты, мелочь рядом): повторно не разбираем
    bool camSaved = false;
    int camFlags = 1;
    float camBg[4] = {0, 0, 0, 1};
    long long lastScan = 0, lastTry = 0;
    int tries = 0;
    float here[3] = {0, 0, 0};  // где игрок сейчас: рядом с ним ничего не прячем (его модель может быть не в иерархии игрока)
    int nearKept = 0;
    long long enteredAt = 0, lastCheck = 0;  // игра при загрузке уровня может вернуть игрока на свою стартовую точку: первые секунды следим
    float sp[3] = {0, 0, 0};
    int fixes = 0;
} W;
bool g_hasPending = false;  // круг телепорта задал точку входа в мир
bool g_noReturnLoad = false;  // арена мини-игры: при выходе не возвращаемся загрузкой сцены
bool g_inPlace = false;     // мир (арена мини-игры) строится в текущей сцене без перехода в level_1: в комнате все остаются в одной сцене
V3 g_pending{0, 0, 0};

std::unordered_set<int> g_ownIds;

void* find_objects(void* type) {
    if (!type) return nullptr;
    if (F.find_objs) { void* a[1] = {type}; return inv(F.find_objs, nullptr, a); }
    if (F.find_objs_sorted) { int mode = 0; void* a[2] = {type, &mode}; return inv(F.find_objs_sorted, nullptr, a); }
    return nullptr;
}

bool is_protected(void* tr) {
    for (int i = 0; i < 10 && tr; ++i) {
        int id = inst_id(tr);
        for (int k = 0; k < 3; ++k) if (W.protect[k] && id == W.protect[k]) return true;
        tr = F.get_parent ? inv(F.get_parent, tr) : nullptr;
    }
    return false;
}

int g_uiKept = 0;
std::string name_of(void* o);
void* goClass_();
void* type_of(const char* ns, const char* name);

/** Элемент интерфейса (значок монеты в углу и т.п.): слой UI или под объектом с «canvas/hud» в имени. Такое не прячем. */
bool is_ui(void* rend, void* tr) {
    void* go = F.get_gameobject ? inv(F.get_gameobject, rend) : nullptr;
    if (go && F.get_layer) {
        void* l = inv(F.get_layer, go);
        if (l && *(const int*)obj_unbox(l) == 5) return true;
    }
    void* t = tr;
    for (int k = 0; k < 8 && t; ++k) {
        std::string n = name_of(t);
        for (auto& c : n) c = (char)tolower((unsigned char)c);
        if (n.find("canvas") != std::string::npos || n.find("hud") != std::string::npos || n.find("overlay") != std::string::npos) return true;
        t = F.get_parent ? inv(F.get_parent, t) : nullptr;
    }
    return false;
}

/** Выключает все рендереры и коллайдеры сцены, кроме игрока и объектов Bearite. Возвращает, сколько выключено. */
int hide_world() {
    g_ownIds.clear();
    W.nearKept = 0;
    g_uiKept = 0;
    if (W.active && W.player) {  // повторный обход: берём текущее место игрока
        void* ptr = target(W.player);
        void* pos = ptr ? inv(F.get_position, ptr) : nullptr;
        if (pos) memcpy(W.here, obj_unbox(pos), sizeof W.here);
    }
    for (auto& kv : g_live) for (auto& L : kv.second) {
        if (L.tid) g_ownIds.insert(L.tid);
        if (L.natClone && L.nat) if (void* ct = target(L.nat)) g_ownIds.insert(inst_id(ct));
    }
    if (void* npcT = type_of("", "NetworkPlayerController")) {  // другие игроки комнаты остаются видимыми
        if (void* na = find_objects(npcT)) {
            uintptr_t nn = arr_len(na);
            for (uintptr_t i = 0; i < nn && i < 64; ++i) {
                void* c = *(void**)arr_elem(na, sizeof(void*), i);
                void* tr = c ? inv(F.get_transform, c) : nullptr;
                void* root = tr && F.get_root ? inv(F.get_root, tr) : tr;
                if (root) g_ownIds.insert(inst_id(root));
            }
        }
    }
    int n = 0;
    for (int pass = 0; pass < 2; ++pass) {
        void* arr = find_objects(pass == 0 ? F.type_renderer : F.type_collider);
        if (!arr) continue;
        void* getEn = pass == 0 ? F.rend_get_enabled : F.col_get_enabled;
        void* setEn = pass == 0 ? F.rend_set_enabled : F.collider_enabled;
        if (!getEn || !setEn) continue;
        uintptr_t cnt = arr_len(arr);
        if (cnt > 200000) cnt = 200000;
        for (uintptr_t i = 0; i < cnt; ++i) {
            void* o = *(void**)arr_elem(arr, sizeof(void*), i);
            if (!o) continue;
            int id = inst_id(o);
            if (id && (W.hidden.count(id) || W.kept.count(id))) continue;
            void* tr = inv(F.get_transform, o);
            if (!tr) continue;
            {
                bool own = false;
                void* t = tr;
                for (int k = 0; k < 12 && t && !own; ++k) {
                    own = g_ownIds.count(inst_id(t)) != 0;
                    if (!own) t = F.get_parent ? inv(F.get_parent, t) : nullptr;
                }
                if (own) { if (id) W.kept.insert(id); continue; }
            }
            if (is_protected(tr)) { if (id) W.kept.insert(id); continue; }
            if (pass == 0 && is_ui(o, tr)) { if (id) W.kept.insert(id); ++g_uiKept; continue; }
            if (pass == 0 && F.rend_bounds) {  // небольшие рендереры рядом с игроком (его модель) оставляем
                void* bb = inv(F.rend_bounds, o);
                if (bb) {
                    const float* f = (const float*)obj_unbox(bb);  // центр xyz, размеры xyz (половина)
                    float dx = f[0] - W.here[0], dy = f[1] - W.here[1], dz = f[2] - W.here[2];
                    if (dx * dx + dy * dy + dz * dz < 12.f && f[3] < 3.f && f[4] < 3.f && f[5] < 3.f) { ++W.nearKept; if (id) W.kept.insert(id); continue; }
                }
            }
            void* en = inv(getEn, o);
            if (!en || !*(const uint8_t*)obj_unbox(en)) continue;
            uint8_t off = 0;
            void* a[1] = {&off};
            bool ok = false;
            inv(setEn, o, a, &ok);
            if (!ok) continue;
            (pass == 0 ? W.hr : W.hc).push_back(gch_new(o, 0));
            if (id) W.hidden.insert(id);
            ++n;
        }
    }
    return n;
}

void show_world() {
    for (int pass = 0; pass < 2; ++pass) {
        auto& v = pass == 0 ? W.hr : W.hc;
        void* setEn = pass == 0 ? F.rend_set_enabled : F.collider_enabled;
        for (uintptr_t h : v) {
            void* o = target(h);
            if (o && setEn) { uint8_t on = 1; void* a[1] = {&on}; inv(setEn, o, a); }
            gch_free(h);
        }
        v.clear();
    }
    W.hidden.clear();
    W.kept.clear();
}

std::string name_of(void* o) {
    void* nm = o && F.get_name ? inv(F.get_name, o) : nullptr;
    return nm ? utf8(nm) : std::string("?");
}

// ---- поиск игрока: кандидатов несколько (тег, CharacterController, объекты «…player…»), настоящий тот, что двигается
bool g_debug = false;  // есть файл maps/_debug: тяжёлая диагностика (списки объектов, кандидаты) включена
long long g_candBuild = 0;
struct Cand { uintptr_t h = 0; int id = 0; float last[3] = {0, 0, 0}; float path = 0; std::string name, how; };
std::vector<Cand> g_cands;
long long g_candPoll = 0, g_candLog = 0;
void* g_typeTransform = nullptr;

bool bad_name(std::string n) {
    for (auto& c : n) c = (char)tolower((unsigned char)c);
    static const char* bad[] = {"photo", "camera", "audio", "music", "bearite/", "replay", "canvas", "hud", "ui ", "(ui", "menu", "shadow", "spawn", "marker", "icon", "label", "text"};
    for (const char* b : bad) if (n.find(b) != std::string::npos) return true;
    return false;
}

void cand_add(void* tr, const char* how) {
    if (!tr) return;
    int id = inst_id(tr);
    for (auto& c : g_cands) if (c.id == id) return;
    std::string nm = name_of(tr);
    if (bad_name(nm)) return;
    void* pv = inv(F.get_position, tr);
    if (!pv) return;
    Cand c;
    c.h = gch_new(tr, 0);
    c.id = id;
    memcpy(c.last, obj_unbox(pv), sizeof c.last);
    c.name = nm;
    c.how = how;
    g_cands.push_back(c);
}

void cands_rebuild() {
    std::vector<Cand> old;
    old.swap(g_cands);
    bool oc = g_crumbs;
    g_crumbs = false;
    if (F.type_kcm) if (void* arr = find_objects(F.type_kcm)) {
        uintptr_t n = arr_len(arr);
        for (uintptr_t i = 0; i < n && i < 50; ++i) {
            void* m = *(void**)arr_elem(arr, sizeof(void*), i);
            cand_add(m ? inv(F.get_transform, m) : nullptr, "KCC");
        }
    }
    if (F.find_tag && F.go_transform) {
        void* a[1] = {bearite_il2.string_new("Player")};
        void* go = inv(F.find_tag, nullptr, a);
        cand_add(go ? inv(F.go_transform, go) : nullptr, "тег Player");
    }
    if (void* arr = find_objects(F.type_cc)) {
        uintptr_t n = arr_len(arr);
        for (uintptr_t i = 0; i < n && i < 200; ++i) {
            void* cc = *(void**)arr_elem(arr, sizeof(void*), i);
            cand_add(cc ? inv(F.get_transform, cc) : nullptr, "CharacterController");
        }
    }
    bool haveKcc = false;
    for (auto& c : g_cands) if (c.how == "KCC") haveKcc = true;
    if (g_typeTransform && (g_debug || !haveKcc)) if (void* arr = find_objects(g_typeTransform)) {  // перебор всех объектов дорогой: только если мотора нет
        uintptr_t n = arr_len(arr);
        if (n > 100000) n = 100000;
        int added = 0;
        for (uintptr_t i = 0; i < n && added < 24; ++i) {
            void* tr = *(void**)arr_elem(arr, sizeof(void*), i);
            if (!tr) continue;
            std::string nm = name_of(tr);
            std::string l = nm;
            for (auto& c : l) c = (char)tolower((unsigned char)c);
            if (l.find("player") == std::string::npos && l.find("bear") == std::string::npos && l.find("character") == std::string::npos) continue;
            size_t before = g_cands.size();
            cand_add(tr, "имя");
            if (g_cands.size() > before) ++added;
        }
    }
    g_crumbs = oc;
    for (auto& c : g_cands) for (auto& o : old) if (o.id == c.id) c.path = o.path;  // накопленный путь не теряем
    for (auto& o : old) gch_free(o.h);
}

/** Раз в секунду обновляет пути кандидатов; возвращает того, кто реально двигался (иначе первого). */
void* pick_player(long long now, bool force = false) {
    if (force || g_cands.empty() || now - g_candBuild > ((g_debug || g_cands.empty()) ? 5000 : 20000)) { g_candBuild = now; cands_rebuild(); }
    Cand* best = nullptr;
    float bestScore = 0;
    for (auto& c : g_cands) {
        void* tr = target(c.h);
        void* pv = tr ? inv(F.get_position, tr) : nullptr;
        if (!pv) { c.path = -1; continue; }
        float f[3];
        memcpy(f, obj_unbox(pv), sizeof f);
        float d = sqrtf((f[0] - c.last[0]) * (f[0] - c.last[0]) + (f[1] - c.last[1]) * (f[1] - c.last[1]) + (f[2] - c.last[2]) * (f[2] - c.last[2]));
        if (c.path >= 0 && d < 40.f) c.path += d;
        memcpy(c.last, f, sizeof f);
        float score = c.path + (c.how == "KCC" ? 100000.f : 0.f);  // мотор KCC — это сам игрок; остальные только если мотора нет
        if (c.path >= 0 && (!best || score > bestScore + 0.5f)) { best = &c; bestScore = score; }
    }
    if (g_debug && now - g_candLog > 15000 && !g_cands.empty()) {
        g_candLog = now;
        logf_("кандидаты в игроки: %d", (int)g_cands.size());
        for (size_t i = 0; i < g_cands.size() && i < 12; ++i)
            logf_("  «%s» (%s) поз %.1f %.1f %.1f, пройдено %.1f%s", g_cands[i].name.c_str(), g_cands[i].how.c_str(), g_cands[i].last[0], g_cands[i].last[1],
                  g_cands[i].last[2], g_cands[i].path, &g_cands[i] == best ? "  ← выбран" : "");
    }
    return best ? target(best->h) : nullptr;
}

void* find_player(const char** how = nullptr) {
    long long now = 0;
    { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); now = (long long)ts.tv_sec * 1000 + ts.tv_nsec / 1000000; }
    void* tr = pick_player(now, true);
    if (tr) { if (how) *how = "по движению"; return tr; }
    if (!g_cands.empty()) { if (how) *how = "первый кандидат"; return target(g_cands[0].h); }
    return nullptr;
}

void teleport(void* tr, V3 pos) {
    void* go = F.get_gameobject ? inv(F.get_gameobject, tr) : nullptr;
    if (go && F.type_kcm && F.kcm_set_pos && F.get_component) {  // KCC каждый тик возвращает объект на свою позицию — двигаем через мотор
        void* b[1] = {F.type_kcm};
        void* motor = inv(F.get_component, go, b);
        if (motor) {
            uint8_t bypass = 1;
            void* a[2] = {&pos, &bypass};
            bool ok = false;
            inv(F.kcm_set_pos, motor, a, &ok);
            if (ok) return;
        }
    }
    void* cc = nullptr;
    if (go && F.type_cc && F.get_component) { void* b[1] = {F.type_cc}; cc = inv(F.get_component, go, b); }
    uint8_t off = 0, on = 1;
    if (cc && F.collider_enabled) { void* a[1] = {&off}; inv(F.collider_enabled, cc, a); }  // CharacterController иначе возвращает себя на место
    void* a[1] = {&pos};
    inv(F.set_position, tr, a);
    if (cc && F.collider_enabled) { void* c[1] = {&on}; inv(F.collider_enabled, cc, c); }
}

void set_sky(unsigned rgb) {
    if (!F.cam_main || !F.cam_set_flags || !F.cam_set_bg) return;
    void* cam = inv(F.cam_main, nullptr);
    if (!cam) return;
    if (!W.camSaved) {
        if (F.cam_get_flags) { void* r = inv(F.cam_get_flags, cam); if (r) W.camFlags = *(const int*)obj_unbox(r); }
        if (F.cam_get_bg) { void* r = inv(F.cam_get_bg, cam); if (r) memcpy(W.camBg, obj_unbox(r), sizeof W.camBg); }
        W.camSaved = true;
    }
    int fl = 2;  // CameraClearFlags.SolidColor
    void* a[1] = {&fl};
    inv(F.cam_set_flags, cam, a);
    Col c{((rgb >> 16) & 255) / 255.f, ((rgb >> 8) & 255) / 255.f, (rgb & 255) / 255.f, 1.f};
    void* b[1] = {&c};
    inv(F.cam_set_bg, cam, b);
}

void restore_sky() {
    if (!W.camSaved) return;
    W.camSaved = false;
    if (!F.cam_main || !F.cam_set_flags || !F.cam_set_bg) return;
    void* cam = inv(F.cam_main, nullptr);
    if (!cam) return;
    void* a[1] = {&W.camFlags};
    inv(F.cam_set_flags, cam, a);
    Col c{W.camBg[0], W.camBg[1], W.camBg[2], W.camBg[3]};
    void* b[1] = {&c};
    inv(F.cam_set_bg, cam, b);
}

bool world_enter(const MapSpec& m) {
    void* tr = find_player();
    if (!tr) {
        if (W.tries++ == 0) logf_("мир «%s»: игрок не найден (нет тега Player и CharacterController), жду", m.name.c_str());
        return false;
    }
    if (!F.type_renderer || !F.type_collider || !F.get_transform || !F.get_iid || (!F.find_objs && !F.find_objs_sorted)) {
        g_status = "error";
        g_msg = "отдельный мир недоступен: в игре вырезаны методы поиска объектов";
        logf_("%s", g_msg.c_str());
        W.lastTry = 1LL << 60;  // больше не пробуем
        return false;
    }
    g_ctx = m.id + " мир: вход";
    W.player = gch_new(tr, 0);
    W.protect[0] = inst_id(tr);
    // защищаем игрока, его родителя и корень; слишком «толстый» контейнер (весь уровень) не трогаем
    auto few = [](void* t) { void* c = F.get_child_count ? inv(F.get_child_count, t) : nullptr; return c && *(const int*)obj_unbox(c) <= 40; };
    void* par = F.get_parent ? inv(F.get_parent, tr) : nullptr;
    W.protect[1] = par && few(par) ? inst_id(par) : 0;
    void* root = tr;
    for (int i = 0; i < 12 && F.get_parent; ++i) { void* p2 = inv(F.get_parent, root); if (!p2) break; root = p2; }
    W.protect[2] = root != tr && few(root) ? inst_id(root) : 0;
    if (void* pos = inv(F.get_position, tr)) memcpy(W.saved, obj_unbox(pos), sizeof W.saved);
    memcpy(W.here, W.saved, sizeof W.here);
    {
        void* nm = F.get_name ? inv(F.get_name, tr) : nullptr;
        logf_("мир «%s»: игрок найден: «%s» (защита: сам=%d родитель=%d корень=%d)", m.name.c_str(), nm ? utf8(nm).c_str() : "?",
              W.protect[0] != 0, W.protect[1] != 0, W.protect[2] != 0);
    }

    g_crumbs = false;
    int n = hide_world();
    g_crumbs = true;
    set_sky(m.sky);
    V3 sp{m.off[0] + m.scale * m.spawn[0], m.off[1] + m.scale * m.spawn[1], m.off[2] + m.scale * m.spawn[2]};
    if (g_hasPending) { sp = g_pending; g_hasPending = false; }
    teleport(tr, sp);
    memcpy(W.here, &sp, sizeof W.here);
    W.active = true;
    W.id = m.id;
    W.tries = 0;
    W.lastScan = now_ms_fwd();
    W.enteredAt = W.lastScan;
    W.lastCheck = 0;
    W.fixes = 0;
    memcpy(W.sp, &sp, sizeof W.sp);
    logf_("мир «%s»: вход, скрыто объектов %d (рядом с игроком оставлено %d, интерфейса %d), игрок в (%.1f %.1f %.1f)", m.name.c_str(), n, W.nearKept, g_uiKept, sp.x, sp.y, sp.z);
    return true;
}

/** Выход из мира. restore=false: сцена сменилась, объекты уже уничтожены, трогать их нельзя. */
void world_exit(bool restore) {
    if (!W.active && W.hr.empty() && W.hc.empty()) return;
    g_ctx = "мир: выход";
    if (restore) {
        g_crumbs = false;
        show_world();
        g_crumbs = true;
        restore_sky();
        void* tr = target(W.player);
        if (tr) teleport(tr, V3{W.saved[0], W.saved[1], W.saved[2]});
        logf_("мир: выход, всё возвращено на место");
    } else {
        for (uintptr_t h : W.hr) gch_free(h);
        for (uintptr_t h : W.hc) gch_free(h);
        W.hr.clear(); W.hc.clear(); W.hidden.clear(); W.kept.clear();
        W.camSaved = false;
    }
    if (W.player) { gch_free(W.player); W.player = 0; }
    W.active = false;
    W.id.clear();
}

bool load_scene(const std::string& name) {
    if (!F.load_scene) return false;
    bool ok = false;
    if (F.load_arity == 2) {
        int mode = 0;  // LoadSceneMode.Single
        void* a[2] = {bearite_il2.string_new(name.c_str()), &mode};
        inv(F.load_scene, nullptr, a, &ok);
    } else {
        void* a[1] = {bearite_il2.string_new(name.c_str())};
        inv(F.load_scene, nullptr, a, &ok);
    }
    logf_("загрузка сцены «%s»: %s", name.c_str(), ok ? "запрошена" : "не удалась");
    return ok;
}

void world_update(long long now) {
    const MapSpec* want = nullptr;
    for (const auto& m : g_specs) if (m.world && m.id == g_worldWant && g_engineOk) { want = &m; break; }
    if (W.active && (!want || want->id != W.id)) {
        world_exit(true);
        if (!want && g_scene == HOST_SCENE && !g_noReturnLoad && now - g_lastLoad > 5000) {  // вышли из мира: возвращаемся туда, откуда пришли
            g_lastLoad = now;
            load_scene(g_returnScene.empty() ? "hub" : g_returnScene);
            g_returnScene.clear();
        }
    }
    if (!want) return;
    if (!W.active) {
        if ((want->scene.empty() || want->scene == HOST_SCENE) && g_scene != HOST_SCENE && !g_inPlace) {
            // мир без привязки живёт только в сцене level_1: свежая сцена без скриптов хаба, без мерцания и лагов
            if (!F.load_scene) goto enter_here;  // загрузка сцен недоступна: мир строится прямо в текущей сцене
            if (!g_wantRedirect || (g_scene != "hub" && g_scene != "backrooms")) return;
            if (now - g_lastLoad < 8000) return;
            g_lastLoad = now;
            g_wantRedirect = false;
            g_returnScene = g_scene;
            g_pendingWorld = want->id;
            logf_("мир «%s»: перехожу в сцену «%s» (вернусь в «%s»)", want->name.c_str(), HOST_SCENE, g_returnScene.c_str());
            load_scene(HOST_SCENE);
            return;
        }
        enter_here:
        if (now - W.lastTry < 1000) return;
        W.lastTry = now;
        // карта должна быть уже построена, иначе игрок упадёт в пустоту
        auto it = g_live.find(want->id);
        if (it == g_live.end() || it->second.empty()) return;
        world_enter(*want);
    } else {
      if (now - W.enteredAt < 12000 && now - W.lastCheck > 400 && W.fixes < 8 && W.player) {
        W.lastCheck = now;
        void* ptr = target(W.player);
        void* pv = ptr ? inv(F.get_position, ptr) : nullptr;
        if (pv) {
            float pp[3];
            memcpy(pp, obj_unbox(pv), sizeof pp);
            float dx = pp[0] - W.sp[0], dy = pp[1] - W.sp[1], dz = pp[2] - W.sp[2];
            if (dx * dx + dy * dy + dz * dz > 25.f * 25.f) {  // игру вернула на старт уровня или игрок упал: ставим обратно
                ++W.fixes;
                teleport(ptr, V3{W.sp[0], W.sp[1], W.sp[2]});
                logf_("мир: игрок оказался в (%.1f %.1f %.1f), возвращаю на точку появления (%d)", pp[0], pp[1], pp[2], W.fixes);
            }
        }
      }
      if (now - W.lastScan > 3000) {
        W.lastScan = now;
        g_crumbs = false;
        hide_world();  // то, что игра успела создать после входа (враги, эффекты)
        g_crumbs = true;
      }
    }
}

// ------------------------------------------------------------ круги телепорта

uintptr_t g_player = 0;       // handle на Transform игрока (для кругов)
bool g_portalLatched = true;  // игрок стоит в круге после телепорта: сработает снова, только когда выйдет и зайдёт
long long g_portalCool = 0, g_lastFind = 0;

void drop_player() {
    if (g_player) { gch_free(g_player); g_player = 0; }
    g_candBuild = 0;  // кандидатов пересоберём заново: в новой сцене старые объекты уничтожены
    g_portalLatched = true;
}

const MapSpec* find_spec(const std::string& id) {
    for (const auto& m : g_specs) if (m.id == id) return &m;
    return nullptr;
}

/** Что игра держит рядом с игроком (до 8 м): помогает найти родной круг телепорта. */
void scan_near(const float* pp, int pid) {
    if (!F.type_renderer || !F.rend_bounds || !F.get_transform) return;
    void* arr = find_objects(F.type_renderer);
    if (!arr) return;
    struct Hit { float d; std::string desc; };
    std::vector<Hit> hits;
    uintptr_t cnt = arr_len(arr);
    if (cnt > 200000) cnt = 200000;
    bool oc = g_crumbs;
    g_crumbs = false;
    for (uintptr_t i = 0; i < cnt; ++i) {
        void* o = *(void**)arr_elem(arr, sizeof(void*), i);
        if (!o) continue;
        void* bb = inv(F.rend_bounds, o);
        if (!bb) continue;
        const float* f = (const float*)obj_unbox(bb);
        float dx = f[0] - pp[0], dy = f[1] - pp[1], dz = f[2] - pp[2];
        float d = sqrtf(dx * dx + dy * dy + dz * dz);
        if (d > 8.f || f[3] > 15.f || f[5] > 15.f) continue;
        void* tr = inv(F.get_transform, o);
        if (!tr) continue;
        bool mine = false;  // части самого игрока (тело, тень, следы) не показываем: они забивают список
        {
            void* t = tr;
            for (int k = 0; k < 14 && t && !mine; ++k) {
                if (pid && inst_id(t) == pid) mine = true;
                t = F.get_parent ? inv(F.get_parent, t) : nullptr;
            }
        }
        if (mine) continue;
        std::string nm0 = name_of(tr);
        if (nm0 == "Shadow" || nm0.rfind("Footstep", 0) == 0 || nm0.rfind("Jump VFX", 0) == 0 || nm0.rfind("Bearite/", 0) == 0) continue;
        void* par = F.get_parent ? inv(F.get_parent, tr) : nullptr;
        char buf[320];
        snprintf(buf, sizeof buf, "«%s» (родитель «%s») центр %.1f %.1f %.1f размер %.1f×%.1f×%.1f",
                 name_of(tr).c_str(), par ? name_of(par).c_str() : "-", f[0], f[1], f[2], f[3] * 2, f[4] * 2, f[5] * 2);
        hits.push_back({d, buf});
    }
    g_crumbs = oc;
    std::sort(hits.begin(), hits.end(), [](const Hit& a, const Hit& b) { return a.d < b.d; });
    logf_("рядом с игроком (до 8 м): %d рендереров, ближайшие:", (int)hits.size());
    for (size_t i = 0; i < hits.size() && i < 25; ++i) logf_("  %.1f м: %s", hits[i].d, hits[i].desc.c_str());
}

void* goClass_() { static void* k = bearite_find_class("UnityEngine", "GameObject"); return k; }

void* find_native(const std::string& name) {
    if (!g_typeTransform || !F.get_transform) return nullptr;
    void* arr = find_objects(g_typeTransform);
    if (!arr) return nullptr;
    bool oc = g_crumbs;
    g_crumbs = false;
    void* found = nullptr;
    uintptr_t n = arr_len(arr);
    if (n > 100000) n = 100000;
    for (uintptr_t i = 0; i < n && !found; ++i) {
        void* tr = *(void**)arr_elem(arr, sizeof(void*), i);
        if (tr && name_of(tr) == name) found = tr;
    }
    g_crumbs = oc;
    return found;
}

/** Выключает скрипты и триггеры внутри объекта (платформа перестаёт запускать уровень). */
void disable_scripts(Live& L, void* go, const std::string& what) {
    int nb = 0, nt = 0;
    std::string names;
    if (go && F.get_comps_children) {
        for (int pass = 0; pass < 2; ++pass) {
            void* type = pass == 0 ? F.type_mono : F.type_collider;
            void* getEn = pass == 0 ? F.beh_get_enabled : F.col_get_enabled;
            void* setEn = pass == 0 ? F.beh_set_enabled : F.collider_enabled;
            if (!type || !getEn || !setEn) continue;
            uint8_t inc = 1;
            void* a[2] = {type, &inc};
            void* comps = inv(F.get_comps_children, go, a);
            if (!comps) continue;
            uintptr_t cn = arr_len(comps);
            for (uintptr_t i = 0; i < cn && i < 200; ++i) {
                void* c = *(void**)arr_elem(comps, sizeof(void*), i);
                if (!c) continue;
                if (pass == 1) {  // у коллайдеров гасим только триггеры: твёрдую платформу оставляем
                    void* it = F.col_is_trigger ? inv(F.col_is_trigger, c) : nullptr;
                    if (!it || !*(const uint8_t*)obj_unbox(it)) continue;
                }
                void* en = inv(getEn, c);
                if (!en || !*(const uint8_t*)obj_unbox(en)) continue;
                uint8_t off = 0;
                void* b[1] = {&off};
                bool ok = false;
                inv(setEn, c, b, &ok);
                if (!ok) continue;
                L.natOff.push_back({gch_new(c, 0), pass});
                if (pass == 0) { ++nb; void* k = obj_class ? obj_class(c) : nullptr; if (k && names.size() < 200) names += std::string(names.empty() ? "" : ", ") + class_name(k); }
                else ++nt;
            }
        }
    }
    logf_("%s: выключено скриптов %d, триггеров %d%s%s", what.c_str(), nb, nt, names.empty() ? "" : " — ", names.c_str());
}

/** Ищет родной объект по имени и занимает его: выключает то, что запускает уровень. */
bool bind_native(Live& L, const std::string& name) {
    void* found = find_native(name);
    if (!found) return false;
    L.nat = gch_new(found, 0);
    void* go = F.get_gameobject ? inv(F.get_gameobject, found) : nullptr;
    disable_scripts(L, go, "родной круг «" + name + "» найден и занят");
    set_disc(L, false);
    return true;
}

/** Делает копию родного объекта (платформа запуска уровня) на месте круга; оригинал не трогает.
 *  Копия создаётся под выключенным родителем: пока он выключен, Awake/OnEnable не вызываются, поэтому PhotonView и прочие скрипты
 *  не успевают зарегистрироваться (иначе «Duplicate key» у Photon). Скрипты удаляются до включения. */
bool clone_native(Live& L, const std::string& name, const V3& pos, float k, const std::string& worldId = "") {
    void* tmpl = find_native(name);
    if (!tmpl || !F.go_transform) return false;
    void* tgo = F.get_gameobject ? inv(F.get_gameobject, tmpl) : nullptr;
    if (!tgo) return false;
    void* holder = nullptr;
    void* cgo = nullptr;
    bool safe = F.instantiate_parent && F.go_ctor_str && F.set_active && F.set_parent && F.destroy_imm && F.get_comps_children && F.type_mono && goClass_();
    if (safe) {
        holder = obj_new(goClass_());
        bool ok = false;
        void* na[1] = {bearite_il2.string_new("Bearite/holder")};
        inv(F.go_ctor_str, holder, na, &ok);
        if (ok) {
            uint8_t off = 0;
            void* sa[1] = {&off};
            inv(F.set_active, holder, sa);
            void* htr = inv(F.go_transform, holder);
            void* ia[2] = {tgo, htr};
            cgo = inv(F.instantiate_parent, nullptr, ia);
        }
        if (!cgo) { safe = false; holder = nullptr; }
    }
    if (!cgo) {  // запасной путь: прямая копия (скрипты выключаем после; Photon может ругнуться)
        if (!F.instantiate) return false;
        void* a[1] = {tgo};
        cgo = inv(F.instantiate, nullptr, a);
        if (!cgo) return false;
    }
    void* ctr = inv(F.go_transform, cgo);
    if (!ctr) return false;
    L.nat = gch_new(ctr, 0);
    L.natClone = true;
    // то, что мир спрятал у оригинала, в копии должно быть включено
    if (F.get_comps_children) for (int pass = 0; pass < 2; ++pass) {
        void* type = pass == 0 ? F.type_renderer : F.type_collider;
        void* setEn = pass == 0 ? F.rend_set_enabled : F.collider_enabled;
        if (!type || !setEn) continue;
        uint8_t inc = 1;
        void* b1[2] = {type, &inc};
        void* b2[2] = {type, &inc};
        void* tc = inv(F.get_comps_children, tgo, b1);
        void* cc = inv(F.get_comps_children, cgo, b2);
        if (!tc || !cc) continue;
        uintptr_t n = arr_len(tc);
        if (arr_len(cc) < n) n = arr_len(cc);
        for (uintptr_t i = 0; i < n && i < 400; ++i) {
            void* t1 = *(void**)arr_elem(tc, sizeof(void*), i);
            void* c1 = *(void**)arr_elem(cc, sizeof(void*), i);
            if (t1 && c1 && W.hidden.count(inst_id(t1))) { uint8_t on = 1; void* e[1] = {&on}; inv(setEn, c1, e); }
        }
    }
    bool full = false;
    if (safe && !worldId.empty()) {
        // копия остаётся настоящей платформой: свой PhotonView-id, чтобы не было «Duplicate key», остальное родное
        void* pvT = type_of("Photon.Pun", "PhotonView");
        void* pvK = bearite_find_class("Photon.Pun", "PhotonView");
        void* setId = pvK ? bearite_il2.class_get_method_from_name(pvK, "set_ViewID", 1) : nullptr;
        if (pvT && setId && F.get_comps_children) {
            uint8_t inc = 1;
            void* a[2] = {pvT, &inc};
            void* arr = inv(F.get_comps_children, cgo, a);
            static int nextId = 960;
            int cnt = 0;
            if (arr) for (uintptr_t i = 0; i < arr_len(arr) && i < 8; ++i) {
                void* pv = *(void**)arr_elem(arr, sizeof(void*), i);
                if (!pv) continue;
                int nid = nextId--;
                void* ia[1] = {&nid};
                bool ok = false;
                inv(setId, pv, ia, &ok);
                if (ok) ++cnt;
            }
            full = cnt > 0;
            logf_("копия платформы: PhotonView переназначено %d", cnt);
        } else {
            logf_("копия платформы: нет PhotonView.set_ViewID (type=%d set=%d), делаю без скриптов", pvT != nullptr, setId != nullptr);
        }
    }
    if (full) {
        void* pa[1] = {nullptr};
        inv(F.set_parent, ctr, pa);
        if (holder) { void* da[1] = {holder}; inv(F.destroy, nullptr, da); }
        L.nativeFull = true;
        g_cloneWorld[inst_id(ctr)] = worldId;
        logf_("копия платформы «%s» создана с родными скриптами (мир «%s»)", name.c_str(), worldId.c_str());
    } else if (safe) {
        // скрипты и триггеры удаляем целиком, пока копия выключена
        int nb = 0, nt = 0;
        std::string names;
        for (int pass = 0; pass < 2; ++pass) {
            void* type = pass == 0 ? F.type_mono : F.type_collider;
            uint8_t inc = 1;
            void* a[2] = {type, &inc};
            void* comps = inv(F.get_comps_children, cgo, a);
            if (!comps) continue;
            uintptr_t cn = arr_len(comps);
            for (uintptr_t i = 0; i < cn && i < 200; ++i) {
                void* c = *(void**)arr_elem(comps, sizeof(void*), i);
                if (!c) continue;
                if (pass == 1) {
                    void* it = F.col_is_trigger ? inv(F.col_is_trigger, c) : nullptr;
                    if (!it || !*(const uint8_t*)obj_unbox(it)) continue;
                }
                if (pass == 0) { void* kl = obj_class ? obj_class(c) : nullptr; if (kl && names.size() < 200) names += std::string(names.empty() ? "" : ", ") + class_name(kl); }
                void* da[1] = {c};
                bool ok = false;
                inv(F.destroy_imm, nullptr, da, &ok);
                if (ok) (pass == 0 ? nb : nt)++;
            }
        }
        void* pa[1] = {nullptr};
        inv(F.set_parent, ctr, pa);  // отцепляем от выключенного родителя: копия становится активной уже без скриптов
        if (holder) { void* da[1] = {holder}; inv(F.destroy, nullptr, da); }
        logf_("копия платформы «%s» создана без скриптов: удалено скриптов %d, триггеров %d — %s", name.c_str(), nb, nt, names.c_str());
    } else {
        disable_scripts(L, cgo, "копия платформы «" + name + "» создана (запасной путь)");
    }
    void* sc = F.get_local_scale ? inv(F.get_local_scale, tmpl) : nullptr;
    if (sc) {
        float v[3];
        memcpy(v, obj_unbox(sc), sizeof v);
        V3 ns{v[0] * k, v[1] * k, v[2] * k};
        void* c[1] = {&ns};
        inv(F.set_scale, ctr, c);
    }
    void* pp[1] = {const_cast<V3*>(&pos)};
    inv(F.set_position, ctr, pp);
    set_disc(L, false);
    return true;
}

/** Один раз за сцену: ищет по имени объекты, похожие на круг/портал/вход (чтобы найти родной круг телепорта). */
void scan_names() {
    if (!g_typeTransform || !F.get_transform) return;
    void* arr = find_objects(g_typeTransform);
    if (!arr) return;
    static const char* kw[] = {"portal", "teleport", "circle", "pad", "warp", "entrance", "entry", "door", "gate", "exit", "enter", "ring", "disc", "lobby", "level select", "arcade", "travel", "zone"};
    bool oc = g_crumbs;
    g_crumbs = false;
    uintptr_t n = arr_len(arr);
    if (n > 100000) n = 100000;
    std::vector<std::string> seen;
    int shown = 0;
    logf_("поиск круга/портала по имени (объектов в сцене %d):", (int)n);
    for (uintptr_t i = 0; i < n && shown < 70; ++i) {
        void* tr = *(void**)arr_elem(arr, sizeof(void*), i);
        if (!tr) continue;
        std::string nm = name_of(tr), l = nm;
        for (auto& c : l) c = (char)tolower((unsigned char)c);
        if (l.rfind("bearite/", 0) == 0) continue;
        bool hit = false;
        for (const char* k : kw) if (l.find(k) != std::string::npos) { hit = true; break; }
        if (!hit) continue;
        void* par = F.get_parent ? inv(F.get_parent, tr) : nullptr;
        std::string pn = par ? name_of(par) : "-";
        std::string key = nm + "|" + pn;
        if (std::find(seen.begin(), seen.end(), key) != seen.end()) continue;
        seen.push_back(key);
        void* pv = inv(F.get_position, tr);
        const float* f = pv ? (const float*)obj_unbox(pv) : nullptr;
        logf_("  «%s» (родитель «%s») поз %.1f %.1f %.1f", nm.c_str(), pn.c_str(), f ? f[0] : 0.f, f ? f[1] : 0.f, f ? f[2] : 0.f);
        ++shown;
    }
    g_crumbs = oc;
}

/** Центр круга: свой — по координатам карты, родной — там, где сейчас стоит занятый объект игры. */
bool portal_center(const MapSpec& m, const Obj& o, Live& L, long long now, float* c) {
    if (!o.bind.empty() && o.clone) {  // копия платформы на месте круга: центр — координаты круга
        for (int k = 0; k < 3; ++k) c[k] = m.off[k] + m.scale * o.p[k];
        {   // назначение круга могли поменять после создания копии: пересоздаём в нужном виде
            const MapSpec* wt0 = o.dest.empty() || o.dest[0] == '@' ? nullptr : find_spec(o.dest);
            bool needFull = wt0 && wt0->world;
            if (L.nat && L.natClone && L.nativeFull != needFull) { release_native(L, true); L.natTry = 0; }
        }
        if (!L.nat && now - L.natTry >= 3000) {
            L.natTry = now;
            float kk = m.scale * (o.s[0] > o.s[2] ? o.s[0] : o.s[2]) / 3.0f;
            const MapSpec* wt = o.dest.empty() || o.dest[0] == '@' ? nullptr : find_spec(o.dest);
            std::string wid = wt && wt->world ? wt->id : "";
            if (!clone_native(L, o.bind, V3{c[0], c[1], c[2]}, kk < 0.05f ? 0.05f : kk, wid) && !L.natMiss) {
                L.natMiss = true;
                logf_("платформа «%s» для копии в этой сцене не найдена (повторю, когда сменится сцена)", o.bind.c_str());
            }
        }
        return true;
    }
    if (o.bind.empty()) {
        for (int k = 0; k < 3; ++k) c[k] = m.off[k] + m.scale * o.p[k];
        return true;
    }
    if (!L.nat) {
        if (now - L.natTry < 3000) return false;
        L.natTry = now;
        if (!bind_native(L, o.bind)) {
            if (!L.natMiss) { L.natMiss = true; logf_("родной круг «%s» в этой сцене не найден (повторю поиск, когда сменится сцена)", o.bind.c_str()); }
            return false;
        }
    }
    void* tr = target(L.nat);
    void* pv = tr ? inv(F.get_position, tr) : nullptr;
    if (!pv) { release_native(L, false); return false; }
    memcpy(c, obj_unbox(pv), 3 * sizeof(float));
    return true;
}

bool g_promptOpen = false;
long long g_promptT = 0;
std::string g_promptId;

/** Вход в мир после ответа «Вперёд!» в окне уровня. */
void enter_world_from_prompt(const MapSpec* t) {
    V3 sp{t->off[0] + t->scale * t->spawn[0], t->off[1] + t->scale * t->spawn[1], t->off[2] + t->scale * t->spawn[2]};
    if (W.active && W.id == t->id) {
        void* tr = g_player ? target(g_player) : nullptr;
        if (tr) teleport(tr, sp);
        return;
    }
    g_noReturnLoad = false;
    g_pending = sp;
    g_hasPending = true;
    g_wantRedirect = true;
    g_worldRt = t->id;
    refresh_world_want();
    logf_("окно уровня: вход в мир «%s»", t->name.c_str());
}

/** Окно уровня рисует лаунчер (процесс игры, GameActivity): мы кладём maps/_prompt и ждём maps/_answer. */
void prompt_poll(long long now) {
    if (!g_promptOpen) return;
    std::string ans = g_mapsDir + "/_answer";
    if (FILE* f = fopen(ans.c_str(), "r")) {
        char buf[200] = {0};
        size_t n = fread(buf, 1, sizeof buf - 1, f);
        fclose(f);
        (void)n;
        unlink((g_mapsDir + "/_prompt").c_str());
        unlink(ans.c_str());
        g_promptOpen = false;
        if (strncmp(buf, "go", 2) == 0) {
            if (const MapSpec* t = find_spec(g_promptId)) enter_world_from_prompt(t);
        } else {
            logf_("окно уровня: отмена");
        }
    } else if (now - g_promptT > 180000) {
        unlink((g_mapsDir + "/_prompt").c_str());
        g_promptOpen = false;
        logf_("окно уровня: ответа не было, закрываю");
    }
}

void prompt_open(const MapSpec* t, long long now) {
    std::string tmp = g_mapsDir + "/_prompt.tmp";
    FILE* f = fopen(tmp.c_str(), "w");
    if (!f) { logf_("окно уровня: не удалось записать файл"); return; }
    auto clean = [](std::string s) { for (auto& c : s) if (c == '\t' || c == '\n' || c == '\r') c = ' '; return s; };
    fprintf(f, "%s\t%s\t%s\t%s\n", t->id.c_str(), clean(t->name).c_str(), clean(t->cover).c_str(), clean(t->desc).c_str());
    fclose(f);
    rename(tmp.c_str(), (g_mapsDir + "/_prompt").c_str());
    unlink((g_mapsDir + "/_answer").c_str());
    g_promptOpen = true;
    g_promptT = now;
    g_promptId = t->id;
    logf_("окно уровня «%s»: показываю", t->name.c_str());
}

void portals_tick(long long now) {
    bool any = false;
    for (const auto& m : g_specs) {
        auto it = g_live.find(m.id);
        if (it == g_live.end()) continue;
        for (size_t i = 0; i < m.objs.size() && i < it->second.size(); ++i)
            if (m.objs[i].shape == "portal" && it->second[i].h) { any = true; break; }
        if (any) break;
    }
    if (!any) return;
    static long long lastDiag = 0;
    bool diag = false;
    if (now - lastDiag > 3000) {
        lastDiag = now;
        g_debug = access((g_mapsDir + "/_debug").c_str(), F_OK) == 0;  // подробная диагностика только по файлу maps/_debug
        diag = g_debug;
    }
    void* tr = g_player ? target(g_player) : nullptr;
    if (!tr || now - g_lastFind >= 1000) {  // перепроверяем раз в секунду: выбираем того кандидата, кто двигается
        g_lastFind = now;
        void* nt = pick_player(now);
        if (!nt && !tr) {
            if (diag) logf_("круги: игрок не найден (нет кандидатов)");
            return;
        }
        if (nt && (!tr || inst_id(nt) != inst_id(tr))) {
            if (g_player) gch_free(g_player);
            g_player = gch_new(nt, 0);
            tr = nt;
            logf_("круги: игрок = «%s»", name_of(nt).c_str());
        }
    }
    void* pv = tr ? inv(F.get_position, tr) : nullptr;
    if (!pv) { if (g_player) { gch_free(g_player); g_player = 0; } return; }
    float pp[3];
    memcpy(pp, obj_unbox(pv), sizeof pp);
    if (diag) {
        static std::string scNames;
        static long long scSince = 0;
        if (scNames != g_scene) { scNames = g_scene; scSince = now; }
        if (scSince && now - scSince > 5000) { scSince = 0; scan_names(); }
    }
    if (diag) {
        static float lastScan[3] = {1e9f, 0, 0};
        static long long lastScanT = 0;
        float mx = pp[0] - lastScan[0], my = pp[1] - lastScan[1], mz = pp[2] - lastScan[2];
        if (mx * mx + my * my + mz * mz > 9.f || now - lastScanT > 12000) { lastScanT = now; memcpy(lastScan, pp, sizeof lastScan); { void* ptr = g_player ? target(g_player) : nullptr; scan_near(pp, ptr ? inst_id(ptr) : 0); } }
        float best = 1e30f, bdy = 0, br = 0; std::string bn;
        for (const auto& m : g_specs) {
            auto it = g_live.find(m.id);
            if (it == g_live.end()) continue;
            for (size_t i = 0; i < m.objs.size() && i < it->second.size(); ++i) {
                const Obj& o = m.objs[i];
                if (o.shape != "portal" || !it->second[i].h) continue;
                float cc[3];
                if (!portal_center(m, o, it->second[i], now, cc)) continue;
                float dx = pp[0] - cc[0], dz = pp[2] - cc[2];
                float d = sqrtf(dx * dx + dz * dz);
                if (d < best) { best = d; bdy = pp[1] - cc[1]; br = 0.5f * m.scale * (o.s[0] > o.s[2] ? o.s[0] : o.s[2]); bn = o.name; }
            }
        }
        logf_("круги: игрок (%.1f %.1f %.1f), ближайший «%s»: расстояние %.1f, радиус %.1f, dy %.1f, защёлка %d",
              pp[0], pp[1], pp[2], bn.c_str(), best, br, bdy, (int)g_portalLatched);
    }
    const MapSpec* hit = nullptr;
    const Obj* hitObj = nullptr;
    for (const auto& m : g_specs) {
        auto it = g_live.find(m.id);
        if (it == g_live.end()) continue;
        for (size_t i = 0; i < m.objs.size() && i < it->second.size(); ++i) {
            const Obj& o = m.objs[i];
            if (o.shape != "portal" || !it->second[i].h) continue;
            float cc[3];
            if (!portal_center(m, o, it->second[i], now, cc)) continue;
            if (it->second[i].nativeFull) continue;  // такой круг обрабатывает сама игра
            float cx = cc[0], cy = cc[1], cz = cc[2];
            float r = 0.5f * m.scale * (o.s[0] > o.s[2] ? o.s[0] : o.s[2]);
            float dx = pp[0] - cx, dz = pp[2] - cz, dy = pp[1] - cy;
            if (dx * dx + dz * dz < r * r && dy > -1.0f * m.scale && dy < (2.5f + o.s[1]) * m.scale) { hit = &m; hitObj = &o; break; }
        }
        if (hit) break;
    }
    if (!hit) { g_portalLatched = false; return; }
    if (g_portalLatched || now < g_portalCool) return;
    g_portalLatched = true;
    g_portalCool = now + 1500;
    const std::string& d = hitObj->dest;
    g_ctx = hit->id + " круг телепорта";
    if (d == "@exit") {
        if (W.active) { g_worldRt = "@exit"; refresh_world_want(); logf_("круг телепорта «%s»: выход из мира", hitObj->name.c_str()); }
    } else if (d.empty()) {
        teleport(tr, V3{hit->off[0] + hit->scale * hitObj->dp[0], hit->off[1] + hit->scale * hitObj->dp[1], hit->off[2] + hit->scale * hitObj->dp[2]});
        logf_("круг телепорта «%s»: в точку этой карты", hitObj->name.c_str());
    } else if (const MapSpec* t = find_spec(d)) {
        V3 sp{t->off[0] + t->scale * t->spawn[0], t->off[1] + t->scale * t->spawn[1], t->off[2] + t->scale * t->spawn[2]};
        if (t->world && !(W.active && W.id == t->id)) {
            if (!g_promptOpen) prompt_open(t, now);  // как у родной платформы: окно с названием и «Вперёд!»
        } else {
            teleport(tr, sp);
            logf_("круг телепорта «%s»: на точку появления карты «%s»", hitObj->name.c_str(), t->name.c_str());
        }
    } else {
        logf_("круг телепорта «%s»: карта «%s» не найдена", hitObj->name.c_str(), d.c_str());
    }
}

/** Проверка, что объекты ещё живы (сцена могла смениться и уничтожить их). */
bool check_alive() {
    if (!F.get_active) return true;
    for (auto& kv : g_live)
        for (auto& L : kv.second) {
            if (!L.h) continue;
            void* go = target(L.h);
            bool ok = false;
            if (go && F.get_active) inv(F.get_active, go, nullptr, &ok);
            return ok;
        }
    return true;
}

void drop_all_live() {
    for (auto& kv : g_live) { for (auto& L : kv.second) drop_live(L); kv.second.clear(); }
}

// -------------------------------------------------------- состояние для редактора

void write_state(const std::string& cam) {
    std::string path = g_mapsDir + "/_state.txt";
    std::string tmp = g_mapsDir + "/.state.tmp";
    FILE* f = fopen(tmp.c_str(), "w");
    if (!f) return;
    fprintf(f, "status=%s\nmsg=%s\nscene=%s\nobjects=%d\nworld=%s\n", g_status.c_str(), g_msg.c_str(), g_scene.c_str(), g_liveCount,
            W.active ? W.id.c_str() : "");
    if (!cam.empty()) fprintf(f, "cam=%s\n", cam.c_str());
    fclose(f);
    rename(tmp.c_str(), path.c_str());
}

std::string read_scene() {
    if (!F.get_scene || !F.scene_name) return "";
    void* sc = inv(F.get_scene, nullptr);  // boxed Scene: единственное поле - int handle
    if (!sc) return "";
    int handle = *(const int*)obj_unbox(sc);
    void* a[1] = {&handle};
    return utf8(inv(F.scene_name, nullptr, a));  // статический Scene.GetNameInternal(int): без this-указателя
}

std::string read_camera() {
    if (!F.cam_main || !F.get_transform || !F.get_position || !F.get_forward) return "";
    void* cam = inv(F.cam_main, nullptr);
    if (!cam) return "";
    void* tr = inv(F.get_transform, cam);
    if (!tr) return "";
    void* p = inv(F.get_position, tr);
    void* f = inv(F.get_forward, tr);
    if (!p || !f) return "";
    const float* a = (const float*)obj_unbox(p);
    const float* b = (const float*)obj_unbox(f);
    char buf[200];
    snprintf(buf, sizeof buf, "%.3f %.3f %.3f %.3f %.3f %.3f", a[0], a[1], a[2], b[0], b[1], b[2]);
    return buf;
}

// ------------------------------------------------------------------- тик

long long now_ms() {
    timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (long long)ts.tv_sec * 1000 + ts.tv_nsec / 1000000;
}
long long now_ms_fwd() { return now_ms(); }

/** Имя текущей комнаты Photon (для чата лаунчера): пишем в maps/_room, пусто = игрок не в комнате. */
void publish_room() {
    static void *pnK = nullptr, *getRoom = nullptr, *getName = nullptr;
    static bool tried = false;
    static std::string last = "?";
    if (!tried) {
        tried = true;
        pnK = bearite_find_class("Photon.Pun", "PhotonNetwork");
        getRoom = pnK ? bearite_il2.class_get_method_from_name(pnK, "get_CurrentRoom", 0) : nullptr;
        logf_("чат: PhotonNetwork=%d get_CurrentRoom=%d", pnK != nullptr, getRoom != nullptr);
    }
    if (!getRoom) return;
    std::string name;
    if (void* room = inv(getRoom, nullptr)) {
        if (!getName) {
            void* rk = obj_class(room);
            getName = rk ? bearite_il2.class_get_method_from_name(rk, "get_Name", 0) : nullptr;
        }
        if (getName) name = utf8(inv(getName, room));
    }
    if (name == last) return;
    last = name;
    std::string path = g_mapsDir + "/_room", tmp = g_mapsDir + "/.room.tmp";
    if (FILE* f = fopen(tmp.c_str(), "w")) { fputs(name.c_str(), f); fclose(f); rename(tmp.c_str(), path.c_str()); }
    logf_("чат: комната «%s»", name.c_str());
}

/** Игроки комнаты Photon: maps/_players = «число\tмакс», дальше «актёр\tник\tсвой(0/1)». Для списка TAB и мини-игр. */
void publish_players() {
    static void *pnK = nullptr, *getList = nullptr, *getRoom = nullptr, *getMax = nullptr;
    static bool tried = false;
    static std::string last = "?";
    if (!tried) {
        tried = true;
        pnK = bearite_find_class("Photon.Pun", "PhotonNetwork");
        getList = pnK ? bearite_il2.class_get_method_from_name(pnK, "get_PlayerList", 0) : nullptr;
        getRoom = pnK ? bearite_il2.class_get_method_from_name(pnK, "get_CurrentRoom", 0) : nullptr;
        logf_("игроки: get_PlayerList=%d", getList != nullptr);
    }
    if (!getList || !getRoom) return;
    std::string out;
    void* room = inv(getRoom, nullptr);
    if (room) {
        if (!getMax) { void* rk = obj_class(room); getMax = rk ? bearite_il2.class_get_method_from_name(rk, "get_MaxPlayers", 0) : nullptr; }
        int mx = 0;
        if (getMax) { void* r = inv(getMax, room); if (r) { void* ub = obj_unbox(r); mx = *(const uint8_t*)ub; if (mx == 0) mx = 0; } }
        void* arr = inv(getList, nullptr);
        uintptr_t n = arr ? arr_len(arr) : 0;
        if (n > 200) n = 200;
        std::string body;
        for (uintptr_t i = 0; i < n; ++i) {
            void* pl = *(void**)arr_elem(arr, sizeof(void*), i);
            if (!pl) continue;
            void* pk = obj_class(pl);
            static void *gA = nullptr, *gN = nullptr, *gL = nullptr;
            if (!gA && pk) { gA = bearite_il2.class_get_method_from_name(pk, "get_ActorNumber", 0); gN = bearite_il2.class_get_method_from_name(pk, "get_NickName", 0); gL = bearite_il2.class_get_method_from_name(pk, "get_IsLocal", 0); }
            int actor = 0, local = 0;
            if (gA) if (void* r = inv(gA, pl)) actor = *(const int*)obj_unbox(r);
            if (gL) if (void* r = inv(gL, pl)) local = *(const uint8_t*)obj_unbox(r) ? 1 : 0;
            std::string nick = gN ? utf8(inv(gN, pl)) : "";
            for (auto& ch : nick) if (ch == '\t' || ch == '\n' || ch == '\r') ch = ' ';
            body += std::to_string(actor) + "\t" + nick + "\t" + std::to_string(local) + "\n";
        }
        out = std::to_string((int)n) + "\t" + std::to_string(mx) + "\n" + body;
    }
    if (out == last) return;
    last = out;
    std::string path = g_mapsDir + "/_players", tmp = g_mapsDir + "/.players.tmp";
    if (FILE* f = fopen(tmp.c_str(), "w")) { fputs(out.c_str(), f); fclose(f); rename(tmp.c_str(), path.c_str()); }
}

/** Позиции игроков комнаты в мировых координатах (для мини-игр): maps/_pos = «актёр\tник\tсвой\tx\ty\tz». Пишется, пока есть maps/_mg. */
void publish_positions(long long now) {
    static long long lastT = 0;
    if (now - lastT < 250) return;
    lastT = now;
    if (access((g_mapsDir + "/_mg").c_str(), F_OK) != 0) return;
    static void *npcT = nullptr, *pvT = nullptr, *pvK = nullptr, *getOwner = nullptr;
    if (!npcT) { npcT = type_of("", "NetworkPlayerController"); pvT = type_of("Photon.Pun", "PhotonView"); pvK = bearite_find_class("Photon.Pun", "PhotonView"); getOwner = pvK ? bearite_il2.class_get_method_from_name(pvK, "get_Owner", 0) : nullptr; }
    if (!npcT) return;
    void* arr = find_objects(npcT);
    uintptr_t n = arr ? arr_len(arr) : 0;
    std::string out;
    for (uintptr_t i = 0; i < n && i < 64; ++i) {
        void* c = *(void**)arr_elem(arr, sizeof(void*), i);
        if (!c) continue;
        void* tr = inv(F.get_transform, c);
        void* pv = tr ? inv(F.get_position, tr) : nullptr;
        if (!pv) continue;
        float f3[3];
        memcpy(f3, obj_unbox(pv), sizeof f3);
        int actor = 0, local = 0;
        std::string nick;
        void* go = F.get_gameobject ? inv(F.get_gameobject, c) : nullptr;
        if (go && pvT && getOwner && F.get_component) {
            void* a[1] = {pvT};
            if (void* view = inv(F.get_component, go, a)) if (void* owner = inv(getOwner, view)) {
                void* pk = obj_class(owner);
                void *gA = bearite_il2.class_get_method_from_name(pk, "get_ActorNumber", 0), *gN = bearite_il2.class_get_method_from_name(pk, "get_NickName", 0), *gL = bearite_il2.class_get_method_from_name(pk, "get_IsLocal", 0);
                if (gA) if (void* r = inv(gA, owner)) actor = *(const int*)obj_unbox(r);
                if (gL) if (void* r = inv(gL, owner)) local = *(const uint8_t*)obj_unbox(r) ? 1 : 0;
                if (gN) nick = utf8(inv(gN, owner));
            }
        }
        for (auto& ch : nick) if (ch == '\t' || ch == '\n') ch = ' ';
        char buf[160];
        snprintf(buf, sizeof buf, "\t%d\t%.2f\t%.2f\t%.2f\n", local, f3[0], f3[1], f3[2]);
        out += std::to_string(actor) + "\t" + nick + buf;
    }
    std::string path = g_mapsDir + "/_pos", tmp = g_mapsDir + "/.pos.tmp";
    if (FILE* f = fopen(tmp.c_str(), "w")) { fputs(out.c_str(), f); fclose(f); rename(tmp.c_str(), path.c_str()); }
}

/** Команды лаунчера (maps/_cmd): «enter\tid» — войти в мир-арену в текущей сцене, «exit», «tp\tx\ty\tz» — в координатах активного мира. */
void cmd_poll() {
    std::string path = g_mapsDir + "/_cmd";
    FILE* f = fopen(path.c_str(), "r");
    if (!f) return;
    std::string text;
    char buf[256];
    size_t n;
    while ((n = fread(buf, 1, sizeof buf, f)) > 0) text.append(buf, n);
    fclose(f);
    unlink(path.c_str());
    size_t st = 0;
    while (st < text.size()) {
        size_t e = text.find('\n', st);
        if (e == std::string::npos) e = text.size();
        auto parts = split_tab(text.substr(st, e - st));
        st = e + 1;
        if (parts.empty()) continue;
        if (parts[0] == "enter" && parts.size() >= 2) {
            if (const MapSpec* t = find_spec(parts[1])) {
                g_inPlace = true;
                g_noReturnLoad = true;
                g_pending = V3{t->off[0] + t->scale * t->spawn[0], t->off[1] + t->scale * t->spawn[1], t->off[2] + t->scale * t->spawn[2]};
                g_hasPending = true;
                g_worldRt = t->id;
                refresh_world_want();
                logf_("команда: вход в арену «%s» (в текущей сцене)", t->name.c_str());
            } else logf_("команда: арена «%s» не найдена", parts[1].c_str());
        } else if (parts[0] == "exit") {
            g_inPlace = false;
            if (W.active) { g_worldRt = "@exit"; refresh_world_want(); logf_("команда: выход из арены"); }
        } else if (parts[0] == "tp" && parts.size() >= 4 && W.active && W.player) {
            if (const MapSpec* t = find_spec(W.id)) {
                V3 v{t->off[0] + t->scale * num(parts[1], 0), t->off[1] + t->scale * num(parts[2], 0), t->off[2] + t->scale * num(parts[3], 0)};
                if (void* tr = target(W.player)) teleport(tr, v);
            }
        }
    }
}

bool set_room_max(void* opts) {
    std::string v;
    if (FILE* f = fopen((g_mapsDir + "/_maxplayers").c_str(), "r")) { char b[32] = {0}; fread(b, 1, sizeof b - 1, f); fclose(f); v = b; }
    if (v.empty() || !opts) return false;
    int mx = atoi(v.c_str());
    if (mx < 0) return false;
    if (mx > 255) mx = 255;
    void* k = obj_class(opts);
    static void *fieldFn = nullptr, *offFn = nullptr, *ftypeFn = nullptr, *tnameFn = nullptr;
    if (!fieldFn) {
        fieldFn = A->il2cpp_symbol("il2cpp_class_get_field_from_name");
        offFn = A->il2cpp_symbol("il2cpp_field_get_offset");
        ftypeFn = A->il2cpp_symbol("il2cpp_field_get_type");
        tnameFn = A->il2cpp_symbol("il2cpp_type_get_name");
    }
    if (!k || !fieldFn || !offFn) return false;
    for (const char* nm : {"MaxPlayers", "maxPlayers"}) {
        void* fl = reinterpret_cast<void* (*)(void*, const char*)>(fieldFn)(k, nm);
        if (!fl) continue;
        int off = reinterpret_cast<int (*)(void*)>(offFn)(fl);
        std::string tn;
        if (ftypeFn && tnameFn) if (void* ft = reinterpret_cast<void* (*)(void*)>(ftypeFn)(fl)) { const char* c = reinterpret_cast<const char* (*)(void*)>(tnameFn)(ft); if (c) tn = c; }
        char* base = (char*)opts + off;
        if (tn == "System.Byte" || tn == "System.SByte") *(uint8_t*)base = (uint8_t)mx;
        else if (tn == "System.Int32") *(int32_t*)base = mx;
        else if (tn == "System.Int16") *(int16_t*)base = (int16_t)mx;
        else { logf_("лимит комнаты: поле %s типа %s не поддерживается", nm, tn.c_str()); return false; }
        logf_("лимит игроков комнаты: поле %s (%s) = %d", nm, tn.c_str(), mx);
        return true;
    }
    logf_("лимит комнаты: поля MaxPlayers у RoomOptions нет");
    return false;
}
int read_room_limit() {
    std::string v;
    if (FILE* f = fopen((g_mapsDir + "/_maxplayers").c_str(), "r")) { char b[32] = {0}; fread(b, 1, sizeof b - 1, f); fclose(f); v = b; }
    if (v.empty()) return -1;
    int mx = atoi(v.c_str());
    // сервер Photon игры не принимает комнаты больше 4 игроков («Max Players Peer Room value is too big, limit:4»):
    // выше лимита, 0 и мусор не трогаем, переопределяем только 1..3
    return (mx >= 1 && mx <= 3) ? mx : -1;
}
void (*o_ro_max_b)(void*, uint32_t, const void*) = nullptr;
void h_ro_max_b(void* self, uint32_t v, const void* mi) {
    int mx = read_room_limit();
    if (mx >= 0 && (v & 0xFF) != (uint32_t)mx) { logf_("лимит игроков: игра ставила %u, ставлю %d", v & 0xFF, mx); v = (uint32_t)mx; }
    if (o_ro_max_b) o_ro_max_b(self, v, mi);
}
void (*o_ro_max_i)(void*, int32_t, const void*) = nullptr;
void h_ro_max_i(void* self, int32_t v, const void* mi) {
    int mx = read_room_limit();
    if (mx >= 0 && v != mx) { logf_("лимит игроков: игра ставила %d, ставлю %d", v, mx); v = mx; }
    if (o_ro_max_i) o_ro_max_i(self, v, mi);
}
bool hook_max_setter(const char* cls) {
    void* k = bearite_find_class("Photon.Realtime", cls);
    void* m = k ? bearite_il2.class_get_method_from_name(k, "set_MaxPlayers", 1) : nullptr;
    if (!m) { logf_("лимит: у %s нет set_MaxPlayers (поле или другой класс)", cls); return false; }
    auto type_name = sym<const char* (*)(void*)>("il2cpp_type_get_name");
    void* pt = method_param ? method_param(m, 0) : nullptr;
    std::string tn = pt && type_name ? type_name(pt) : "";
    void* code = bearite_method_code(m);
    if (!code) return false;
    bool isByte = tn == "System.Byte" || tn == "System.SByte";
    int rc = isByte ? A->hook(code, (void*)h_ro_max_b, (void**)&o_ro_max_b) : A->hook(code, (void*)h_ro_max_i, (void**)&o_ro_max_i);
    logf_("лимит: перехват %s.set_MaxPlayers(%s): %s", cls, tn.c_str(), rc == 0 ? "готово" : "не удался");
    return rc == 0;
}

uint8_t (*o_create_room)(void*, void*, void*, void*, const void*) = nullptr;
uint8_t h_create_room(void* name, void* opts, void* lobby, void* friends, const void* mi) {
    try { set_room_max(opts); } catch (...) {}
    return o_create_room ? o_create_room(name, opts, lobby, friends, mi) : 0;
}
uint8_t (*o_join_create_room)(void*, void*, void*, void*, const void*) = nullptr;
uint8_t h_join_create_room(void* name, void* opts, void* lobby, void* friends, const void* mi) {
    try { set_room_max(opts); } catch (...) {}
    return o_join_create_room ? o_join_create_room(name, opts, lobby, friends, mi) : 0;
}

long long g_lastTick = 0, g_lastSlow = 0;
std::string g_lastCam;

void update() {
    long long now = now_ms();
    reload_maps();
    cmd_poll();
    publish_positions(now);
    bool slow = now - g_lastSlow >= 500;
    if (slow) {
        g_lastSlow = now;
        publish_room();
        publish_players();
        std::string sc = read_scene();
        if (!sc.empty() && sc != g_scene) {
            logf_("сцена: «%s» → «%s»", g_scene.c_str(), sc.c_str());
            g_scene = sc;
            world_exit(false);  // объекты прошлой сцены уже уничтожены
            drop_all_live();    // Unity сам уничтожил объекты прошлой сцены
            drop_textures();
            drop_player();
            g_worldRt.clear();
            pick_world_file();
            if (!g_pendingWorld.empty()) {
                if (g_scene == HOST_SCENE) g_worldRt = g_pendingWorld;
                g_pendingWorld.clear();
            }
            refresh_world_want();
            g_dirty = true;
        } else if (!check_alive()) {
            logf_("объекты карт пропали без смены сцены, строю заново");
            world_exit(true);  // сцена та же: возвращаем спрятанное
            drop_all_live();
            drop_textures();
            g_dirty = true;
        }
    }
    if (g_dirty && g_engineOk) {
        g_dirty = false;
        if (g_status != "ok") { g_status = "ok"; g_msg.clear(); }
        // защита от цикла падений: файл остаётся, если игра упала внутри sync_all
        std::string guard = g_mapsDir + "/_guard";
        if (FILE* gf = fopen(guard.c_str(), "w")) { fputs("sync", gf); fclose(gf); }
        sync_all();
        g_in_sync = false;
        unlink(guard.c_str());
    }
    prompt_poll(now);
    if (g_engineOk && !g_dirty) portals_tick(now);
    if (slow && g_engineOk) {
        std::string guard = g_mapsDir + "/_guard";
        if (FILE* gf = fopen(guard.c_str(), "w")) { fputs("мир", gf); fclose(gf); }
        g_in_sync = true;
        world_update(now);
        g_in_sync = false;
        unlink(guard.c_str());
    }
    if (slow) {
        std::string cam = read_camera();
        write_state(cam);
    }
}

std::atomic<pid_t> g_main{0};
std::mutex g_latchMu;
pid_t g_ids[8];
int g_cnt[8];
int g_nids = 0, g_total = 0;

void latch(pid_t me) {
    std::lock_guard<std::mutex> lk(g_latchMu);
    if (g_main.load() != 0) return;
    int i = 0;
    for (; i < g_nids; ++i) if (g_ids[i] == me) break;
    if (i == g_nids) { if (g_nids >= 8) return; g_ids[g_nids++] = me; g_cnt[i] = 0; }
    ++g_cnt[i];
    if (++g_total >= 300) {
        int best = 0;
        for (int k = 1; k < g_nids; ++k) if (g_cnt[k] > g_cnt[best]) best = k;
        g_main.store(g_ids[best]);
        logf_("главный поток Unity: tid=%d (%d из %d вызовов)", (int)g_ids[best], g_cnt[best], g_total);
    }
}

thread_local bool t_busy = false;

void on_tick() {
    pid_t me = gettid();
    pid_t m = g_main.load(std::memory_order_relaxed);
    if (m == 0) { latch(me); return; }
    if (m != me || t_busy) return;
    long long now = now_ms();
    if (now - g_lastTick < 100) return;
    g_lastTick = now;
    t_busy = true;
    update();
    t_busy = false;
}

float (*o_dt)(const void*);
float (*o_udt)(const void*);
float (*o_time)(const void*);
float (*o_utime)(const void*);
float h_dt(const void* mi) { float r = o_dt(mi); on_tick(); return r; }
float h_udt(const void* mi) { float r = o_udt(mi); on_tick(); return r; }
float h_time(const void* mi) { float r = o_time(mi); on_tick(); return r; }
float h_utime(const void* mi) { float r = o_utime(mi); on_tick(); return r; }


bool bind_il2cpp() {
    gch_new = sym<uintptr_t (*)(void*, int)>("il2cpp_gchandle_new");
    gch_target = sym<void* (*)(uintptr_t)>("il2cpp_gchandle_get_target");
    gch_free = sym<void (*)(uintptr_t)>("il2cpp_gchandle_free");
    obj_unbox = sym<void* (*)(void*)>("il2cpp_object_unbox");
    obj_class = sym<void* (*)(void*)>("il2cpp_object_get_class");
    class_name = sym<const char* (*)(void*)>("il2cpp_class_get_name");
    str_chars = sym<const uint16_t* (*)(void*)>("il2cpp_string_chars");
    str_len = sym<int (*)(void*)>("il2cpp_string_length");
    class_type = sym<void* (*)(void*)>("il2cpp_class_get_type");
    type_object = sym<void* (*)(void*)>("il2cpp_type_get_object");
    class_methods = sym<void* (*)(void*, void**)>("il2cpp_class_get_methods");
    method_name = sym<const char* (*)(void*)>("il2cpp_method_get_name");
    method_pcount = sym<uint32_t (*)(void*)>("il2cpp_method_get_param_count");
    method_param = sym<void* (*)(void*, uint32_t)>("il2cpp_method_get_param");
    class_from_type = sym<void* (*)(void*)>("il2cpp_class_from_type");
    obj_new = sym<void* (*)(void*)>("il2cpp_object_new");
    arr_new = sym<void* (*)(void*, uintptr_t)>("il2cpp_array_new");
    get_corlib = sym<void* (*)()>("il2cpp_get_corlib");
    return gch_new && gch_target && gch_free && obj_unbox && obj_class && class_name && str_chars && str_len &&
           class_type && type_object && class_methods && method_name && method_pcount && method_param && class_from_type;
}

void* type_of(const char* ns, const char* name) {
    void* k = bearite_find_class(ns, name);
    if (!k) return nullptr;
    void* o = type_object(class_type(k));
    if (o) gch_new(o, 0);  // держим объект Type живым навсегда
    return o;
}

void bind_unity() {
    void* go = bearite_find_class("UnityEngine", "GameObject");
    void* tr = bearite_find_class("UnityEngine", "Transform");
    void* cm = bearite_find_class("UnityEngine", "Component");
    void* ob = bearite_find_class("UnityEngine", "Object");
    void* rd = bearite_find_class("UnityEngine", "Renderer");
    void* mt = bearite_find_class("UnityEngine", "Material");
    void* co = bearite_find_class("UnityEngine", "Collider");
    void* ca = bearite_find_class("UnityEngine", "Camera");
    void* sm = bearite_find_class("UnityEngine.SceneManagement", "SceneManager");
    void* sc = bearite_find_class("UnityEngine.SceneManagement", "Scene");
    auto m0 = [](void* k, const char* n, int argc) { return k ? bearite_il2.class_get_method_from_name(k, n, argc) : nullptr; };
    F.create_primitive = m0(go, "CreatePrimitive", 1);
    F.get_transform = m0(cm, "get_transform", 0);  // для компонентов (камера)
    F.go_transform = m0(go, "get_transform", 0);   // для GameObject
    F.set_position = m0(tr, "set_position", 1);
    F.set_scale = m0(tr, "set_localScale", 1);
    F.set_euler = m0(tr, "set_eulerAngles", 1);
    F.get_position = m0(tr, "get_position", 0);
    F.get_forward = m0(tr, "get_forward", 0);
    F.cam_main = m0(ca, "get_main", 0);
    F.set_name = m0(ob, "set_name", 1);
    F.destroy = m0(ob, "Destroy", 1);
    F.get_active = m0(go, "get_activeSelf", 0);
    F.set_layer = m0(go, "set_layer", 1);
    F.get_layer = m0(go, "get_layer", 0);
    if (void* smk = bearite_find_class("UnityEngine.SceneManagement", "SceneManager")) {
        // методы загрузки сцены в сборке могли вырезать: пробуем все известные варианты
        const char* names[] = {"LoadScene", "LoadSceneAsync"};
        for (const char* n : names) {
            if (!F.load_scene) { F.load_scene = find_method_types(smk, n, {"String"}); if (F.load_scene) { F.load_arity = 1; logf_("загрузка сцен: %s(String)", n); } }
        }
        for (const char* n : names) {
            if (!F.load_scene) { F.load_scene = find_method_types(smk, n, {"String", "LoadSceneMode"}); if (F.load_scene) { F.load_arity = 2; logf_("загрузка сцен: %s(String, LoadSceneMode)", n); } }
        }
        if (!F.load_scene) dump_class("UnityEngine.SceneManagement", "SceneManager");
    }
    logf_("загрузка сцен: метод=%d, get_layer=%d", F.load_scene != nullptr, F.get_layer != nullptr);
    F.go_ctor_str = find_method_types(go, ".ctor", {"String"});
    F.set_active = m0(go, "SetActive", 1);
    if (void* trk = bearite_find_class("UnityEngine", "Transform")) F.set_parent = find_method_types(trk, "SetParent", {"Transform"});
    F.instantiate_parent = find_method_types(ob, "Instantiate", {"Object", "Transform"});
    F.destroy_imm = m0(ob, "DestroyImmediate", 1);
    scan_classes();
    F.get_component = find_method_p0(go, "GetComponent", 1, "Type");
    F.get_material = m0(rd, "get_material", 0);
    F.set_color = m0(mt, "set_color", 1);
    F.collider_enabled = m0(co, "set_enabled", 1);
    F.col_is_trigger = m0(co, "get_isTrigger", 0);
    F.instantiate = find_method_types(ob, "Instantiate", {"Object"});
    F.get_local_scale = m0(tr, "get_localScale", 0);
    F.type_mono = type_of("UnityEngine", "MonoBehaviour");
    if (void* bh = bearite_find_class("UnityEngine", "Behaviour")) {
        F.beh_get_enabled = m0(bh, "get_enabled", 0);
        F.beh_set_enabled = m0(bh, "set_enabled", 1);
    }
    F.get_comps_children = find_method_types(go, "GetComponentsInChildren", {"Type", "Boolean"});
    F.get_scene = m0(sm, "GetActiveScene", 0);
    F.scene_name = m0(sc, "GetNameInternal", 1);
    F.tex2d = bearite_find_class("UnityEngine", "Texture2D");
    F.set_main_tex = find_method_p0(mt, "set_mainTexture", 1, "Texture");
    F.set_main_tex_scale = find_method_p0(mt, "set_mainTextureScale", 1, "Vector2");
    F.set_hideflags = m0(ob, "set_hideFlags", 1);
    F.image_conv = bearite_find_class("UnityEngine", "ImageConversion");
    F.get_iid = m0(ob, "GetInstanceID", 0);
    F.get_parent = m0(tr, "get_parent", 0);
    F.get_child_count = m0(tr, "get_childCount", 0);
    F.get_gameobject = m0(cm, "get_gameObject", 0);
    F.get_root = m0(tr, "get_root", 0);
    F.find_tag = find_method_p0(go, "FindWithTag", 1, "String");
    F.find_obj = find_method_p0(ob, "FindObjectOfType", 1, "Type");
    F.find_objs = find_method_p0(ob, "FindObjectsOfType", 1, "Type");
    F.find_objs_sorted = find_method_types(ob, "FindObjectsByType", {"Type", "FindObjectsSortMode"});
    F.rend_set_enabled = m0(rd, "set_enabled", 1);
    F.rend_get_enabled = m0(rd, "get_enabled", 0);
    F.col_get_enabled = m0(co, "get_enabled", 0);
    F.cam_set_flags = m0(ca, "set_clearFlags", 1);
    F.cam_get_flags = m0(ca, "get_clearFlags", 0);
    F.cam_set_bg = m0(ca, "set_backgroundColor", 1);
    F.cam_get_bg = m0(ca, "get_backgroundColor", 0);
    F.type_cc = type_of("UnityEngine", "CharacterController");
    g_typeTransform = type_of("UnityEngine", "Transform");
    F.type_kcm = type_of("KinematicCharacterController", "KinematicCharacterMotor");
    if (void* kk = bearite_find_class("KinematicCharacterController", "KinematicCharacterMotor"))
        F.kcm_set_pos = find_method_types(kk, "SetPosition", {"Vector3", "Boolean"});
    logf_("KinematicCharacterMotor: тип=%d SetPosition=%d", F.type_kcm != nullptr, F.kcm_set_pos != nullptr);
    void* shd = bearite_find_class("UnityEngine", "Shader");
    F.mat_has_prop = find_method_types(mt, "HasProperty", {"String"});
    F.mat_set_tex = find_method_types(mt, "SetTexture", {"String", "Texture"});
    F.mat_set_scale = find_method_types(mt, "SetTextureScale", {"String", "Vector2"});
    F.mat_get_shader = m0(mt, "get_shader", 0);
    F.get_name = m0(ob, "get_name", 0);
    F.mat_get_main_tex = m0(mt, "get_mainTexture", 0);
    F.shader_find = find_method_p0(shd, "Find", 1, "String");
    F.rend_set_material = m0(rd, "set_material", 1);
    F.mat_class = mt;
    F.mat_ctor_shader = find_method_types(mt, ".ctor", {"Shader"});
    F.rend_bounds = m0(rd, "get_bounds", 0);
    F.type_renderer = type_of("UnityEngine", "Renderer");
    F.type_collider = type_of("UnityEngine", "Collider");
}

void (*o_pause_menu)(void*, uint8_t, const void*) = nullptr;
/** Меню паузы игры открыто/закрыто (в мультиплеере время при этом не останавливается): пишем maps/_menu для кнопки «Моды». */
void h_pause_menu(void* self, uint8_t en, const void* mi) {
    static int lastV = -1;
    int v = en ? 1 : 0;
    if (v != lastV) {
        lastV = v;
        std::string path = g_mapsDir + "/_menu", tmp = g_mapsDir + "/.menu.tmp";
        if (FILE* f = fopen(tmp.c_str(), "w")) { fputs(v ? "1" : "0", f); fclose(f); rename(tmp.c_str(), path.c_str()); }
        logf_("меню паузы игры: %s", v ? "открыто" : "закрыто");
    }
    if (o_pause_menu) o_pause_menu(self, en, mi);
}

void (*o_load_level)(void*, const void*) = nullptr;
/** Родная платформа запускает уровень. Если это наша копия — запоминаем мир: игра сама загрузит level_1 (с родным окном и переходом),
 *  а движок откроет в нём мир, как только сцена сменится. */
void h_load_level(void* self, const void* mi) {
    try {
        void* go = self && F.get_gameobject ? inv(F.get_gameobject, self) : nullptr;
        void* tr = go && F.go_transform ? inv(F.go_transform, go) : nullptr;
        void* root = tr && F.get_root ? inv(F.get_root, tr) : nullptr;
        auto it = root ? g_cloneWorld.find(inst_id(root)) : g_cloneWorld.end();
        if (it != g_cloneWorld.end()) {
            if (const MapSpec* t = find_spec(it->second)) {
                g_noReturnLoad = false;
                g_pendingWorld = t->id;
                g_returnScene = g_scene;
                g_pending = V3{t->off[0] + t->scale * t->spawn[0], t->off[1] + t->scale * t->spawn[1], t->off[2] + t->scale * t->spawn[2]};
                g_hasPending = true;
                logf_("платформа запускает уровень: после загрузки открою мир «%s» (вернусь в «%s»)", t->name.c_str(), g_scene.c_str());
            }
        }
    } catch (...) {}
    if (o_load_level) o_load_level(self, mi);
}

int hook_time(const char* name, void* repl, void** orig) {
    return bearite_hook_method(A, ID, "UnityEngine", "Time", name, 0, repl, orig);
}

}  // namespace

extern "C" __attribute__((visibility("default"))) void bearite_mod_init(const BeariteApi* api, const char* mod_id) {
    A = api;
    ID = mod_id;
    if (api->version != BEARITE_API_VERSION || !api->data_dir) {
        api->log(mod_id, "несовместимая версия API лаунчера");
        return;
    }
    char msg[200];
    snprintf(msg, sizeof msg, "встроенный мод Bearite запущен (сборка %s %s, круги v2), libil2cpp: база=%p", __DATE__, __TIME__, api->module_base("libil2cpp.so"));
    api->log(mod_id, msg);

    g_mapsDir = std::string(api->data_dir()) + "/maps";
    g_guardPath = g_mapsDir + "/_guard";
    mkdir(g_mapsDir.c_str(), 0775);

    if (!bearite_il2cpp_init(api) || !bind_il2cpp()) {
        g_status = "error";
        g_msg = "не найдены функции IL2CPP";
        write_state("");
        return;
    }
    bind_unity();

    std::string missing;
    if (!F.create_primitive) missing += " GameObject.CreatePrimitive";
    if (!F.go_transform) missing += " GameObject.get_transform";
    if (!F.set_position) missing += " Transform.set_position";
    if (!F.set_scale) missing += " Transform.set_localScale";
    if (!F.set_euler) missing += " Transform.set_eulerAngles";
    if (!F.destroy) missing += " Object.Destroy";
    g_engineOk = missing.empty();
    std::string guard = g_mapsDir + "/_guard";
    if (g_engineOk && access(guard.c_str(), F_OK) == 0) {
        g_engineOk = false;
        g_status = "error";
        g_msg = "в прошлый раз игра упала при построении карты, карты отключены (во вкладке «Карты» есть кнопка сброса)";
        logf_("%s", g_msg.c_str());
    } else if (!g_engineOk) {
        g_status = "error";
        g_msg = "в игре вырезаны методы Unity:" + missing;
        logf_("движок карт не запущен, нет методов:%s", missing.c_str());
        dump_class("UnityEngine", "GameObject");
        dump_class("UnityEngine", "Transform");
    } else {
        g_status = "ok";
        if (!F.get_component || !F.get_material || !F.set_color || !F.type_renderer)
            logf_("цвет объектов недоступен (нет Renderer/Material в игре)");
        if (!F.get_scene || !F.scene_name) logf_("имя сцены недоступно, привязка карт к сцене не работает");
        if (!F.cam_main || !F.get_position || !F.get_forward) logf_("позиция камеры недоступна, «перед камерой» не работает");
        logf_("текстуры: Texture2D=%d mainTexture=%d объект_new=%d; мир: поиск=%d%d%d тег=%d CharacterController=%d небо=%d",
              F.tex2d != nullptr, F.set_main_tex != nullptr, obj_new != nullptr, F.find_objs != nullptr, F.find_objs_sorted != nullptr,
              F.find_obj != nullptr, F.find_tag != nullptr, F.type_cc != nullptr, F.cam_set_bg != nullptr);
    }

    int hooks = 0;
    if (hook_time("get_deltaTime", (void*)h_dt, (void**)&o_dt) == 0) ++hooks;
    if (hook_time("get_unscaledDeltaTime", (void*)h_udt, (void**)&o_udt) == 0) ++hooks;
    if (hook_time("get_time", (void*)h_time, (void**)&o_time) == 0) ++hooks;
    if (hook_time("get_unscaledTime", (void*)h_utime, (void**)&o_utime) == 0) ++hooks;
    {
        int rc = bearite_hook_method(A, ID, "", "LevelEntrance", "LoadLevel", 0, (void*)h_load_level, (void**)&o_load_level);
        if (rc != 0) logf_("перехват запуска уровня платформой: не вышло (%d)", rc);
    }
    {
        int rc = bearite_hook_method(A, ID, "", "PauseMenuManager", "EnablePauseMenu", 1, (void*)h_pause_menu, (void**)&o_pause_menu);
        if (rc != 0) logf_("перехват меню паузы: не вышло (%d)", rc);
    }
    {
        int r1 = bearite_hook_method(A, ID, "Photon.Pun", "PhotonNetwork", "CreateRoom", 4, (void*)h_create_room, (void**)&o_create_room);
        int r2 = bearite_hook_method(A, ID, "Photon.Pun", "PhotonNetwork", "JoinOrCreateRoom", 4, (void*)h_join_create_room, (void**)&o_join_create_room);
        if (r1 != 0 && r2 != 0) logf_("перехват создания комнаты: не вышло (%d, %d)", r1, r2);
    }
    dump_class("Photon.Realtime", "RoomOptions");
    dump_class("Photon.Realtime", "Room");
    hook_max_setter("RoomOptions");
    logf_("движок карт: хуков кадра %d, карты читаются из %s", hooks, g_mapsDir.c_str());
    if (hooks == 0) {
        g_status = "error";
        g_msg = "не удалось повесить хуки кадра";
    }
    write_state("");
}
