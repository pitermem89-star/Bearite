package com.bearite.patcher

import android.net.Uri
import android.provider.OpenableColumns
import android.widget.Toast
import androidx.appcompat.app.AlertDialog
import androidx.appcompat.app.AppCompatActivity
import java.io.File
import java.text.SimpleDateFormat
import java.util.Date
import java.util.Locale

/**
 * Загрузка сохранения .sba с телефона: файл выбирается в проводнике и кладётся в папку сохранений игры.
 * Игра работает внутри лаунчера, поэтому её данные лежат в папках лаунчера (внутренней и в Android/data/.../files).
 * Файл копируется в com.bearite.patcher/files под своим именем; прежний файл с таким именем сохраняется рядом как .bak.
 */
class SaveImport(private val act: AppCompatActivity) {

    private fun roots(): List<File> = listOfNotNull(act.getExternalFilesDir(null), act.filesDir).distinctBy { it.absolutePath }   // сначала видимая в проводнике Android/data/…/files

    private fun walk(dir: File, depth: Int, out: MutableList<File>, all: Boolean) {
        if (depth > 5 || out.size > 400) return
        val kids = try { dir.listFiles() } catch (_: Throwable) { null } ?: return
        for (f in kids) {
            if (f.isDirectory) { if (f.name != "maps" && f.name != "cache") walk(f, depth + 1, out, all) }
            else if (all || f.name.endsWith(".sba", ignoreCase = true)) out.add(f)
        }
    }

    private fun existing(): List<File> { val l = ArrayList<File>(); for (r in roots()) walk(r, 0, l, false); return l }

    /** Пишет в лог, что лежит в папках игры: по этому видно, куда игра кладёт сохранения. */
    fun logLayout() {
        for (r in roots()) {
            val l = ArrayList<File>(); walk(r, 0, l, true)
            BLog.i("сохранения: папка ${r.absolutePath}, файлов ${l.size}: " + l.take(40).joinToString("; ") { it.relativeTo(r).path + " (" + it.length() + ")" })
        }
    }

    private fun nameOf(uri: Uri): String {
        try {
            act.contentResolver.query(uri, arrayOf(OpenableColumns.DISPLAY_NAME), null, null, null)?.use { c ->
                if (c.moveToFirst()) return c.getString(0) ?: ""
            }
        } catch (_: Throwable) {}
        return uri.lastPathSegment?.substringAfterLast('/') ?: "save.sba"
    }

    fun handle(uri: Uri) {
        val name = nameOf(uri)
        val data = try {
            act.contentResolver.openInputStream(uri)?.use { it.readBytes() }
        } catch (t: Throwable) { BLog.e("сохранение: не прочитал файл", t); null }
        if (data == null || data.isEmpty()) { toast("Не получилось прочитать файл"); return }
        if (data.size > 30_000_000) { toast("Файл слишком большой для сохранения"); return }
        BLog.i("сохранение: выбран «$name», ${data.size} байт")
        logLayout()
        if (!name.endsWith(".sba", ignoreCase = true)) {
            AlertDialog.Builder(act).setTitle("Это не .sba").setMessage("Файл «$name» не похож на сохранение .sba. Всё равно загрузить?")
                .setNegativeButton("Отмена", null).setPositiveButton("Загрузить") { _, _ -> choose(name, data) }.show()
        } else choose(name, data)
    }

    /** Папка данных игры, как её видно в проводнике: Android/data/com.bearite.patcher/files. */
    private fun dataDir(): File = act.getExternalFilesDir(null) ?: act.filesDir

    /** Файл копируется в папку игры как есть: то же имя, то же расширение, существующий файл заменяется. */
    private fun choose(name: String, data: ByteArray) {
        val safe = name.replace(Regex("[\\\\/:*?\"<>|]"), "_").ifBlank { "save.sba" }
        val target = File(dataDir(), safe)
        try {
            target.parentFile?.mkdirs()
            target.writeBytes(data)
            if (target.length() != data.size.toLong()) throw java.io.IOException("размер записанного файла не совпал")
            BLog.i("сохранение: скопировано в ${target.absolutePath}, ${data.size} байт")
            AlertDialog.Builder(act).setTitle("Сохранение загружено")
                .setMessage("Файл скопирован:\n${target.absolutePath}\n\nЗапусти игру и открой слот сохранения.")
                .setPositiveButton("Ок", null).show()
        } catch (t: Throwable) {
            BLog.e("сохранение: не записалось", t)
            toast("Не получилось записать: ${t.message}")
        }
    }

    private fun toast(s: String) = Toast.makeText(act, s, Toast.LENGTH_LONG).show()
}
