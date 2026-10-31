package com.bearite.patcher

import android.app.Activity
import android.content.Context
import android.graphics.Color
import android.graphics.Typeface
import android.graphics.drawable.GradientDrawable
import android.os.Handler
import android.os.Looper
import android.view.Gravity
import android.view.View
import android.view.ViewGroup
import android.widget.FrameLayout
import android.widget.LinearLayout
import android.widget.TextView
import org.json.JSONObject
import java.io.File
import java.net.HttpURLConnection
import java.net.URL
import java.security.MessageDigest

/**
 * Мини-игры внутри самой игры: ты бегаешь своим медведем по специальной арене, а игроки комнаты Photon играют вместе.
 * Арены (assets/minigames, файлы mg_*) создаются как миры Bearite в текущей сцене, чтобы все в комнате оставались в одной сцене.
 * Игру запускает хост комнаты (игрок с наименьшим номером). Хост же считает очки по позициям игроков
 * (мод пишет их в maps/_pos) и рассылает таблицу через тот же публичный ntfy, что и чат.
 * Игры: паркур-гонка, царь горы, догонялки.
 */
class MiniGames(private val act: Activity) {
    private val ui = GameUi(act)
    private val d = act.resources.displayMetrics.density
    private fun dp(v: Int) = (v * d).toInt()
    private val main = Handler(Looper.getMainLooper())
    private val dir = File(act.filesDir, "maps")
    private val prefs = act.getSharedPreferences("chat", Context.MODE_PRIVATE)
    private val room = act.getSharedPreferences("room", Context.MODE_PRIVATE)
    private val cid: String get() = prefs.getString("cid", null) ?: java.util.UUID.randomUUID().toString().take(8).also { prefs.edit().putString("cid", it).apply() }
    private val base get() = (prefs.getString("url", ChatOverlay.DEFAULT_URL) ?: ChatOverlay.DEFAULT_URL).ifBlank { ChatOverlay.DEFAULT_URL }

    /** Табло поверх игры (добавляется в корневой FrameLayout GameActivity). */
    val hud = TextView(act).apply {
        textSize = 14f; setTextColor(Color.WHITE); typeface = Typeface.DEFAULT_BOLD
        background = GradientDrawable().apply { setColor(0xAA101010.toInt()); cornerRadius = dp(14).toFloat() }
        setPadding(dp(12), dp(8), dp(12), dp(8)); visibility = View.GONE; isClickable = false
    }
    var onStarted: (() -> Unit)? = null

    private class P(val actor: Int, val nick: String, val local: Boolean)
    private class Pos(val x: Float, val y: Float, val z: Float)

    private var players = listOf<P>()
    private var maxPlayers = 0
    private var roomName = ""
    private var phase = "idle"     // idle, prep, play
    private var game = ""
    private var prepUntil = 0L
    private var startedAt = 0L
    private var durMs = 0L
    private val scores = HashMap<Int, Int>()
    private val finished = HashMap<Int, Long>()
    private var itActor = 0
    private var immuneUntil = 0L
    private var lastScoreSend = 0L
    private var lastSecond = 0L
    private var lastTp = 0L
    private var cpIdx = 0
    private var message = ""
    private var tabList: LinearLayout? = null
    @Volatile private var relayGen = 0
    private var relayRoom = ""

    private val me: P? get() = players.firstOrNull { it.local }
    private val isHost: Boolean get() = players.isEmpty() || me == null || me!!.actor == players.minOf { it.actor }
    private fun nick(a: Int) = players.firstOrNull { it.actor == a }?.nick?.ifBlank { "игрок $a" } ?: "игрок $a"

    init {
        // Photon Cloud: AppId по умолчанию (можно поменять в поле на вкладке «Мультиплеер»)
        try {
            if (!File(dir, "_appid").exists()) { dir.mkdirs(); File(dir, "_appid").writeText(room.getString("appid", DEFAULT_APPID) ?: DEFAULT_APPID) }
        } catch (_: Throwable) {}
        main.post(object : Runnable { override fun run() { tick(); main.postDelayed(this, 250) } })
    }

    /** Ник для комнат Photon: тот же, что в чате. */
    private var nick: String
        get() = prefs.getString("nick", "") ?: ""
        set(v) { prefs.edit().putString("nick", v.trim().take(24)).apply() }

    fun stopAll() { relayGen++ }

    // ------------------------------------------------------------------ вкладка меню

    fun render(into: LinearLayout) {
        tabList = into
        readPlayers()
        into.removeAllViews()
        into.addView(ui.label(if (roomName.isEmpty()) "Ты не в комнате" else "Комната: $roomName", 16f), ui.matchWrap().apply { topMargin = dp(8) })
        into.addView(ui.label(
            if (roomName.isEmpty()) "Мини-игры работают в мультиплеере: зайди в комнату игры, и хост сможет запустить игру для всех."
            else "Игроков: ${players.size}" + (if (maxPlayers > 0) " из $maxPlayers" else " (без лимита)") + (if (isHost) " · ты хост" else " · хост: " + (players.minByOrNull { it.actor }?.nick ?: "?")),
            13f, GameUi.MUTED, bold = false))
        // игры
        into.addView(ui.label("Мини-игры", 14f), ui.matchWrap().apply { topMargin = dp(14) })
        val canStart = roomName.isNotEmpty() && isHost && phase == "idle"
        val why = "комната=«$roomName» игроков=${players.size} я=${me?.actor} хост=$isHost фаза=$phase"
        BLog.i("мини-игры: вкладка: $why")
        into.addView(ui.label(why, 11f, GameUi.MUTED, bold = false))
        for ((g, title, sub) in listOf(
            Triple("parkour", "Паркур-гонка", "Добеги по платформам до финиша быстрее всех"),
            Triple("hill", "Царь горы", "60 секунд: очки за время на вершине, соперников можно сбрасывать"),
            Triple("tag", "Догонялки", "60 секунд: один водящий ловит остальных, очки за свободное время"),
        )) {
            into.addView(ui.pill("$title\n$sub", primary = canStart, sizeSp = 13f) { if (canStart) hostStart(g) else { message = if (roomName.isEmpty()) "Сначала зайди в комнату." else if (!isHost) "Запускает хост комнаты." else "Игра уже идёт."; render(into) } },
                ui.matchWrap().apply { topMargin = dp(6) })
        }
        if (phase != "idle" && isHost) into.addView(ui.pill("Остановить игру", danger = true) { hostStop() }, ui.matchWrap().apply { topMargin = dp(10) })
        if (message.isNotEmpty()) into.addView(ui.label(message, 13f, GameUi.RUST, bold = false))
    }

    /** Вкладка «Мультиплеер»: сколько игроков сейчас в комнате и лимит для новых комнат. */
    fun renderMulti(into: LinearLayout) {
        readPlayers()
        into.removeAllViews()
        into.addView(ui.label(if (roomName.isEmpty()) "Ты не в игровой комнате" else "Комната: $roomName", 16f), ui.matchWrap().apply { topMargin = dp(8) })
        into.addView(ui.label(
            if (roomName.isEmpty()) "Зайди в мультиплеер, чтобы увидеть игроков."
            else "Подключено: ${players.size}" + (if (maxPlayers > 0) " из $maxPlayers" else " (без лимита)"),
            14f, GameUi.CREAM, bold = false))
        for (p in players.sortedBy { it.actor }) into.addView(ui.label("• " + p.nick.ifBlank { "игрок ${p.actor}" } + (if (p.local) "  (ты)" else ""), 14f, if (p.local) GameUi.GREEN else GameUi.CREAM, bold = p.local))
        // лимит игроков для создаваемых комнат
        into.addView(ui.label("Лимит игроков в новой комнате", 14f), ui.matchWrap().apply { topMargin = dp(12) })
        into.addView(ui.row("Игроков", ui.textInput(room.getString("max", "") ?: "", 120, "пусто = 4 как в игре") { v ->
            val digits = v.filter(Char::isDigit).take(3)
            room.edit().putString("max", digits).apply()
            val f = File(dir, "_maxplayers")
            try { if (digits.isEmpty()) f.delete() else f.writeText(digits) } catch (_: Throwable) {}
        }), ui.matchWrap().apply { topMargin = dp(4) })
        // ник: им подписываемся в комнатах Photon (тот же ник, что в чате)
        into.addView(ui.label("Твой ник", 14f), ui.matchWrap().apply { topMargin = dp(12) })
        into.addView(ui.textInput(nick, 300, "как тебя звать в игре") { v ->
            nick = v
            if (v.isNotBlank()) cmd("nick\t" + v.trim().replace('\t', ' ').take(24))
        }, ui.matchWrap().apply { topMargin = dp(4) })
        // две кнопки, как в игре: создать новую комнату и присоединиться по коду
        into.addView(ui.pill("Создать новую комнату", primary = true, sizeSp = 15f) {
            if (nick.isBlank()) { message = "Сначала впиши ник."; renderMulti(into); return@pill }
            val c = (100000..999999).random().toString()
            room.edit().putString("code", c).apply()
            val max = room.getString("max", "")?.toIntOrNull() ?: 0
            cmd("nick\t" + nick.trim().replace('\t', ' ').take(24))
            cmd("create\t$c\t$max")
            message = "Комната создаётся. Код для друзей: $c"
            renderMulti(into)
        }, ui.matchWrap().apply { topMargin = dp(10) })
        into.addView(ui.label("Создаёт комнату, код покажем здесь. Друзья входят по этому коду.", 12f, GameUi.MUTED, bold = false))
        into.addView(ui.textInput(room.getString("code", "") ?: "", 300, "код комнаты (6 цифр)") { v -> room.edit().putString("code", v.filter(Char::isDigit).take(12)).apply() }, ui.matchWrap().apply { topMargin = dp(10) })
        into.addView(ui.pill("Присоединиться к комнате") {
            val c = (room.getString("code", "") ?: "").trim()
            if (nick.isBlank()) { message = "Сначала впиши ник."; renderMulti(into); return@pill }
            if (c.isEmpty()) { message = "Впиши код комнаты."; renderMulti(into); return@pill }
            cmd("nick\t" + nick.trim().replace('\t', ' ').take(24))
            cmd("join\t$c")
            message = "Вхожу в комнату $c…"
            renderMulti(into)
        }, ui.matchWrap().apply { topMargin = dp(6) })
        if (message.isNotEmpty()) into.addView(ui.label(message, 13f, GameUi.RUST, bold = false))

        // свой AppId Photon Cloud: мод подставит его при подключении (после перезапуска игры)
        into.addView(ui.label("AppId Photon Cloud (свой)", 14f), ui.matchWrap().apply { topMargin = dp(12) })
        into.addView(ui.textInput(room.getString("appid", DEFAULT_APPID) ?: DEFAULT_APPID, 300, "вставь App ID из dashboard.photonengine.com") { v ->
            val t = v.trim()
            room.edit().putString("appid", t).apply()
            val f = File(dir, "_appid")
            try { if (t.isEmpty()) f.delete() else f.writeText(t) } catch (_: Throwable) {}
        }, ui.matchWrap().apply { topMargin = dp(4) })
        into.addView(ui.label("Применяется после перезапуска игры. Пусто — игра подключается к своему серверу, как раньше.", 12f, GameUi.MUTED, bold = false))
        into.addView(ui.label("Сервер Photon игры не разрешает больше 4 игроков в комнате, это ограничение не обойти. Здесь можно только уменьшить лимит (1–3); пусто или 4 и больше — как в игре.", 12f, GameUi.MUTED, bold = false))
    }

    // ------------------------------------------------------------------ файлы мода

    private fun readPlayers() {
        try { roomName = File(dir, "_room").readText().trim() } catch (_: Throwable) { roomName = "" }
        val lines = try { File(dir, "_players").readText().lines().filter { it.isNotBlank() } } catch (_: Throwable) { emptyList() }
        if (lines.isEmpty()) { players = emptyList(); return }
        maxPlayers = lines[0].split('\t').getOrNull(1)?.toIntOrNull() ?: 0
        players = lines.drop(1).mapNotNull { l ->
            val p = l.split('\t'); val a = p.getOrNull(0)?.toIntOrNull() ?: return@mapNotNull null
            P(a, p.getOrElse(1) { "" }, p.getOrElse(2) { "0" } == "1")
        }
    }

    private fun readPositions(): Map<Int, Pos> {
        val out = HashMap<Int, Pos>()
        try {
            for (l in File(dir, "_pos").readText().lines()) {
                val p = l.split('\t'); if (p.size < 6) continue
                val a = p[0].toIntOrNull() ?: continue
                out[a] = Pos(p[3].toFloatOrNull() ?: continue, (p[4].toFloatOrNull() ?: continue) - OY, p[5].toFloatOrNull() ?: continue)
            }
        } catch (_: Throwable) {}
        return out
    }

    private fun cmd(text: String) { BLog.i("мини-игры: команда моду «${text.replace('\t', ' ')}»"); try { val t = File(dir, "_cmd.tmp"); t.writeText(text + "\n"); t.renameTo(File(dir, "_cmd")) } catch (_: Throwable) {} }

    private fun installArena(g: String) {
        try {
            dir.mkdirs()
            act.assets.open("minigames/mg_$g.map").use { i -> File(dir, "mg_$g.map").outputStream().use { o -> i.copyTo(o) } }
        } catch (t: Throwable) { BLog.e("арена $g не скопирована", t) }
    }

    // ------------------------------------------------------------------ рассылка (ntfy)

    private fun topic(r: String) = "bearite-mg-" + MessageDigest.getInstance("SHA-256").digest(("mgame" + r).toByteArray()).joinToString("") { "%02x".format(it) }.take(24)

    private fun post(o: JSONObject) {
        val r = roomName; if (r.isEmpty()) return
        o.put("c", cid)
        Thread {
            try {
                val h = URL("$base/${topic(r)}").openConnection() as HttpURLConnection
                h.connectTimeout = 8000; h.readTimeout = 8000; h.requestMethod = "POST"; h.doOutput = true
                h.setRequestProperty("Content-Type", "text/plain; charset=utf-8")
                h.outputStream.use { it.write(o.toString().toByteArray()) }
                h.responseCode; h.disconnect()
            } catch (_: Throwable) {}
        }.start()
    }

    private fun ensureRelay() {
        if (roomName == relayRoom) return
        relayRoom = roomName; val g = ++relayGen
        if (roomName.isEmpty()) return
        val r = roomName
        Thread {
            var since = "10s"
            while (relayGen == g) {
                try {
                    val h = URL("$base/${topic(r)}/json?since=$since").openConnection() as HttpURLConnection
                    h.connectTimeout = 8000; h.readTimeout = 95000
                    if (h.responseCode != 200) throw RuntimeException()
                    h.inputStream.bufferedReader().use { rd ->
                        while (relayGen == g) {
                            val ln = rd.readLine() ?: break
                            val j = try { JSONObject(ln) } catch (_: Throwable) { continue }
                            if (j.optString("event") != "message") continue
                            if (j.optString("id").isNotEmpty()) since = j.getString("id")
                            val m = try { JSONObject(j.getString("message")) } catch (_: Throwable) { continue }
                            if (m.optString("c") == cid) continue
                            main.post { if (relayGen == g) onMessage(m) }
                        }
                    }
                    h.disconnect()
                } catch (_: Throwable) { try { Thread.sleep(2000) } catch (_: InterruptedException) { return@Thread } }
            }
        }.apply { isDaemon = true }.start()
    }

    private fun onMessage(m: JSONObject) {
        when (m.optString("k")) {
            "start" -> if (phase == "idle") begin(m.optString("g"))
            "stop" -> finish("Хост остановил игру", false)
            "score" -> if (!isHost && phase != "idle") {
                scores.clear(); val s = m.optJSONObject("s")
                if (s != null) for (k in s.keys()) scores[k.toInt()] = s.getInt(k)
                itActor = m.optInt("it", 0)
            }
            "end" -> if (phase != "idle") finish(m.optString("t"), false)
        }
    }

    // ------------------------------------------------------------------ ход игры

    private fun hostStart(g: String) {
        BLog.i("мини-игры: хост запускает «$g», комната «$roomName», игроков ${players.size}")
        message = ""
        post(JSONObject().put("k", "start").put("g", g))
        begin(g)
        onStarted?.invoke()
    }

    private fun hostStop() { post(JSONObject().put("k", "stop")); finish("Игра остановлена", false) }

    private fun begin(g: String) {
        readPlayers()
        BLog.i("мини-игры: begin «$g», игроков ${players.size}, я=${me?.actor}, хост=$isHost")
        game = g; phase = "prep"; scores.clear(); finished.clear(); itActor = 0; cpIdx = 0
        durMs = when (g) { "parkour" -> 150000L; else -> 60000L }
        installArena(g)
        try { File(dir, "_mg").writeText("1") } catch (_: Throwable) {}
        main.postDelayed({ cmd("enter\tmg_$g") }, 700)   // карту мод успевает прочитать
        prepUntil = System.currentTimeMillis() + 8000
        hud.visibility = View.VISIBLE
        message = ""
    }

    private fun spawnFor(g: String): Triple<Float, Float, Float> {
        val idx = players.sortedBy { it.actor }.indexOfFirst { it.local }.coerceAtLeast(0)
        val n = maxOf(players.size, 1)
        return when (g) {
            "parkour" -> Triple((idx % 5 - 2) * 1.6f, 1.5f, (idx / 5) * 1.6f - 2f)
            "hill" -> { val a = idx * 2 * Math.PI / n; Triple((Math.cos(a) * 24).toFloat(), 2f, (Math.sin(a) * 24).toFloat()) }
            else -> { val a = idx * 2 * Math.PI / n; Triple((Math.cos(a) * 12).toFloat(), 2f, (Math.sin(a) * 12).toFloat()) }
        }
    }

    private fun tp(t: Triple<Float, Float, Float>) { cmd("tp\t${t.first}\t${t.second}\t${t.third}"); lastTp = System.currentTimeMillis() }

    private fun tick() {
        readPlayers(); ensureRelay()
        if (phase == "idle") { if (hud.visibility == View.VISIBLE && message.isEmpty()) hud.visibility = View.GONE; return }
        val now = System.currentTimeMillis()
        if (phase == "prep") {
            val left = ((prepUntil - now) / 1000).coerceAtLeast(0)
            hud.text = "${title()}\nАрена загружается… старт через $left"
            if (now >= prepUntil) { BLog.i("мини-игры: старт, позиций игроков: ${readPositions().size}"); phase = "play"; startedAt = now; lastSecond = now; lastScoreSend = now; tp(spawnFor(game))
                if (isHost && game == "tag" && players.isNotEmpty()) { itActor = players.random().actor }
                immuneUntil = now + 3000 }
            return
        }
        val pos = readPositions(); val mine = me?.let { pos[it.actor] }
        val elapsed = now - startedAt
        // падение с арены: возвращаемся на последнюю контрольную точку или на старт
        if (mine != null && now - lastTp > 1500) {
            val kill = if (game == "parkour") -12f else -6f
            if (mine.y < kill) {
                if (game == "parkour") { val c = MgArenas.PARKOUR_CPS[cpIdx]; tp(Triple(c.first, c.second + 2f, c.third)) } else tp(spawnFor(game))
            }
            if (game == "parkour") for (i in cpIdx + 1 until MgArenas.PARKOUR_CPS.size) {
                val c = MgArenas.PARKOUR_CPS[i]
                if (Math.hypot((mine.x - c.first).toDouble(), (mine.z - c.third).toDouble()) < 4.0 && mine.y >= c.second - 1f) cpIdx = i
            }
        }
        if (isHost) hostLogic(pos, elapsed, now)
        val left = ((durMs - elapsed) / 1000).coerceAtLeast(0)
        val sb = StringBuilder(title()).append("  ·  ").append(left).append(" с")
        if (game == "tag") sb.append(if (itActor == me?.actor) "\nТЫ ВОДЯЩИЙ — лови!" else "\nВодящий: ${nick(itActor)}")
        if (game == "parkour" && mine != null) sb.append("\nДо финиша: ${Math.max(0, (MgArenas.PARKOUR_LEN - mine.z).toInt())} м")
        for ((a, s) in scores.entries.sortedByDescending { it.value }.take(5)) sb.append("\n${nick(a)} — $s")
        hud.text = sb.toString()
        if (!isHost && elapsed > durMs + 15000) finish("Время вышло", false)
    }

    private fun title() = when (game) { "parkour" -> "Паркур-гонка"; "hill" -> "Царь горы"; else -> "Догонялки" }

    private fun hostLogic(pos: Map<Int, Pos>, elapsed: Long, now: Long) {
        var over = elapsed >= durMs
        when (game) {
            "parkour" -> {
                val f = MgArenas.PARKOUR_FINISH
                for (p in players) {
                    val q = pos[p.actor] ?: continue
                    if (!finished.containsKey(p.actor) && Math.abs(q.x - f.first) < 7f && Math.abs(q.z - f.third) < 7f && q.y > f.second - 1f) {
                        finished[p.actor] = elapsed
                        scores[p.actor] = maxOf(1, 10 - (finished.size - 1) * 2)
                    }
                }
                if (players.isNotEmpty() && finished.size >= players.size) over = true
            }
            "hill" -> if (now - lastSecond >= 1000) {
                lastSecond = now
                for (p in players) { val q = pos[p.actor] ?: continue
                    if (Math.hypot(q.x.toDouble(), q.z.toDouble()) <= MgArenas.HILL_RADIUS && q.y >= MgArenas.HILL_TOP - 1f) scores[p.actor] = (scores[p.actor] ?: 0) + 1 }
            }
            "tag" -> {
                val it0 = pos[itActor]
                if (it0 != null && now > immuneUntil) for (p in players) {
                    if (p.actor == itActor) continue
                    val q = pos[p.actor] ?: continue
                    if (Math.hypot((q.x - it0.x).toDouble(), (q.z - it0.z).toDouble()) < 2.0 && Math.abs(q.y - it0.y) < 1.5f) { itActor = p.actor; immuneUntil = now + 2500; lastScoreSend = 0; break }
                }
                if (now - lastSecond >= 1000) { lastSecond = now; for (p in players) if (p.actor != itActor) scores[p.actor] = (scores[p.actor] ?: 0) + 1 }
            }
        }
        if (over) {
            val sorted = players.sortedByDescending { scores[it.actor] ?: 0 }
            val text = if (sorted.isEmpty()) "Игра окончена" else "Победитель: ${sorted[0].nick.ifBlank { "игрок ${sorted[0].actor}" }} (${scores[sorted[0].actor] ?: 0})"
            val s = JSONObject(); for ((a, v) in scores) s.put(a.toString(), v)
            post(JSONObject().put("k", "score").put("s", s).put("it", itActor))
            post(JSONObject().put("k", "end").put("t", text))
            finish(text, true); return
        }
        if (now - lastScoreSend >= 5000) {
            lastScoreSend = now
            val s = JSONObject(); for ((a, v) in scores) s.put(a.toString(), v)
            post(JSONObject().put("k", "score").put("s", s).put("it", itActor))
        }
    }

    private fun finish(text: String, host: Boolean) {
        if (phase == "idle") return
        phase = "idle"; message = text
        val result = StringBuilder(text)
        for ((a, s) in scores.entries.sortedByDescending { it.value }.take(6)) result.append("\n${nick(a)} — $s")
        hud.text = result.toString(); hud.visibility = View.VISIBLE
        cmd("exit")
        try { File(dir, "_mg").delete() } catch (_: Throwable) {}
        main.postDelayed({ if (phase == "idle") { hud.visibility = View.GONE; message = "" } }, 9000)
    }

    companion object {
        const val OY = 1000f
        const val DEFAULT_APPID = "ae18accd-8a43-479c-8000-c2eab1aeb36e"
    }
}
