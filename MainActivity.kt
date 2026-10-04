package com.rachid.remote

import android.app.Activity
import android.content.Context
import android.hardware.ConsumerIrManager
import android.net.wifi.WifiManager
import android.os.Bundle
import android.view.HapticFeedbackConstants
import android.view.View
import android.widget.*
import dadb.AdbKeyPair
import dadb.Dadb
import java.io.File
import java.net.InetSocketAddress
import java.net.Socket
import java.util.concurrent.Executors
import java.util.concurrent.TimeUnit

// proto: 0 = NEC, 1 = Samsung32, 2 = Sony SIRC-12, 3 = Wi-Fi (ADB) لأي Android TV / TV Box
class P(val name: String, val proto: Int, val addr: Int, val k: Map<String, Int>)

val PROFILES = listOf(
    // Wi-Fi: كيخدم بنفس الشبكة (راوتر بلا إنترنت عادي). الأرقام = Android KeyEvent
    P("Wi-Fi: Android TV / TV Box", 3, 0, mapOf("POWER" to 26, "MUTE" to 164, "VOLUP" to 24, "VOLDN" to 25,
        "UP" to 19, "DOWN" to 20, "LEFT" to 21, "RIGHT" to 22, "OK" to 23,
        "MENU" to 82, "BACK" to 4, "HOME" to 3, "SETTINGS" to -1, "PLAY" to 85, "INPUT" to 178)),
    P("LG", 0, 0x04, mapOf("POWER" to 0x08, "MUTE" to 0x09, "VOLUP" to 0x02, "VOLDN" to 0x03,
        "UP" to 0x40, "DOWN" to 0x41, "LEFT" to 0x07, "RIGHT" to 0x06, "OK" to 0x44,
        "MENU" to 0x43, "BACK" to 0x28, "HOME" to 0x7C)),
    P("Samsung", 1, 0x07, mapOf("POWER" to 0x02, "MUTE" to 0x0F, "VOLUP" to 0x07, "VOLDN" to 0x0B,
        "UP" to 0x60, "DOWN" to 0x61, "LEFT" to 0x65, "RIGHT" to 0x62, "OK" to 0x68,
        "MENU" to 0x1A, "BACK" to 0x58, "HOME" to 0x79)),
    P("Sony", 2, 0x01, mapOf("POWER" to 0x15, "MUTE" to 0x14, "VOLUP" to 0x12, "VOLDN" to 0x13,
        "UP" to 0x74, "DOWN" to 0x75, "LEFT" to 0x34, "RIGHT" to 0x33, "OK" to 0x65, "MENU" to 0x60)),
    // BenQ: الكود المخصص الرسمي 0x30 (NEC). الأكواد تلقاها بزر "مسح الأكواد" (IR فقط)
    P("BenQ (0x30)", 0, 0x30, mapOf()),
    P("BenQ (0x0C)", 0, 0x0C, mapOf()),
    P("مخصص NEC", 0, 0x00, mapOf())
)

class MainActivity : Activity() {
    private var ir: ConsumerIrManager? = null
    private var cur = 0
    private lateinit var stv: TextView
    private lateinit var ipEt: EditText

    // ---------- IR ----------
    private val h = android.os.Handler(android.os.Looper.getMainLooper())
    private var scanning = false
    private var sc = 0
    private val tick = object : Runnable {
        override fun run() {
            if (!scanning) return
            val (f, pat) = enc(PROFILES[cur], sc)
            ir?.transmit(f, pat)
            stv.text = "كود: " + sc + " (0x" + Integer.toHexString(sc) + ")"
            sc = (sc + 1) and 255
            h.postDelayed(this, 700)
        }
    }

    private fun lsb(v: Int, n: Int) = (0 until n).map { (v shr it) and 1 }

    private fun enc(p: P, c: Int): Pair<Int, IntArray> {
        if (p.proto == 2) {
            val f = ArrayList<Int>()
            f.add(2400); f.add(600)
            for (b in lsb(c, 7) + lsb(p.addr, 5)) { f.add(if (b == 1) 1200 else 600); f.add(600) }
            f.removeAt(f.size - 1)
            val gap = 45000 - f.sum()
            val all = ArrayList<Int>()
            for (i in 0 until 3) { all.addAll(f); if (i < 2) all.add(gap) }
            return 40000 to all.toIntArray()
        }
        val l = ArrayList<Int>()
        if (p.proto == 0) { l.add(9000); l.add(4500) } else { l.add(4500); l.add(4500) }
        val bits = lsb(p.addr, 8) + lsb(p.addr.inv() and 255, 8) + lsb(c, 8) + lsb(c.inv() and 255, 8)
        for (b in bits) { l.add(560); l.add(if (b == 1) 1690 else 560) }
        l.add(560)
        return 38000 to l.toIntArray()
    }

    // ---------- Wi-Fi (ADB) ----------
    private val ex = Executors.newSingleThreadExecutor()
    private var adb: Dadb? = null
    private var adbIp = ""

    private fun adbSend(cmd: String) {
        val ip = ipEt.text.toString().trim()
        if (ip.isEmpty()) { Toast.makeText(this, "كتب IP ديال الجهاز أو دير بحث 🔍", Toast.LENGTH_SHORT).show(); return }
        getSharedPreferences("r", 0).edit().putString("ip", ip).apply()
        ex.execute {
            try {
                if (adb == null || adbIp != ip) {
                    try { adb?.close() } catch (e: Exception) {}
                    val pr = File(filesDir, "k"); val pu = File(filesDir, "k.pub")
                    if (!pr.exists()) AdbKeyPair.generate(pr, pu)
                    adb = Dadb.create(ip, 5555, AdbKeyPair.read(pr, pu))
                    adbIp = ip
                }
                adb!!.shell(cmd)
            } catch (e: Exception) {
                try { adb?.close() } catch (x: Exception) {}
                adb = null
                runOnUiThread { Toast.makeText(this, "فشل: " + (e.message ?: ""), Toast.LENGTH_LONG).show() }
            }
        }
    }

    private fun findBox() {
        val ipI = (getSystemService(Context.WIFI_SERVICE) as WifiManager).dhcpInfo.ipAddress
        if (ipI == 0) { Toast.makeText(this, "ما متصلش بـ Wi-Fi", Toast.LENGTH_SHORT).show(); return }
        val base = (ipI and 255).toString() + "." + ((ipI shr 8) and 255) + "." + ((ipI shr 16) and 255) + "."
        stv.text = "كنقلب فالشبكة..."
        Thread {
            val pool = Executors.newFixedThreadPool(64)
            val found = java.util.Collections.synchronizedList(ArrayList<String>())
            for (i in 1..254) pool.execute {
                try { Socket().use { it.connect(InetSocketAddress(base + i, 5555), 400); found.add(base + i) } } catch (e: Exception) {}
            }
            pool.shutdown(); pool.awaitTermination(15, TimeUnit.SECONDS)
            runOnUiThread {
                if (found.isEmpty()) stv.text = "ما لقيت والو. فعّل USB debugging فالـ TV Box"
                else { ipEt.setText(found[0]); stv.text = "لقيت: " + found.joinToString() }
            }
        }.start()
    }

    // ---------- إرسال ----------
    private fun send(key: String, v: View) {
        v.performHapticFeedback(HapticFeedbackConstants.VIRTUAL_KEY)
        val p = PROFILES[cur]
        val c = p.k[key]
        if (c == null) { Toast.makeText(this, "غير متوفر", Toast.LENGTH_SHORT).show(); return }
        if (p.proto == 3) {
            adbSend(if (c == -1) "am start -a android.settings.SETTINGS" else "input keyevent " + c)
            return
        }
        if (ir?.hasIrEmitter() != true) { Toast.makeText(this, "الهاتف ما فيهش IR", Toast.LENGTH_SHORT).show(); return }
        val (f, pat) = enc(p, c)
        ir?.transmit(f, pat)
    }

    override fun onCreate(s: Bundle?) {
        super.onCreate(s)
        ir = getSystemService(Context.CONSUMER_IR_SERVICE) as? ConsumerIrManager
        val root = LinearLayout(this).apply { orientation = LinearLayout.VERTICAL; setPadding(24, 48, 24, 24) }

        val st = TextView(this).apply {
            text = if (ir?.hasIrEmitter() == true) "IR جاهز ✅" else "IR: ❌ (استعمل Wi-Fi)"
            textSize = 16f
        }
        val sp = Spinner(this)
        sp.adapter = ArrayAdapter(this, android.R.layout.simple_spinner_dropdown_item, PROFILES.map { it.name })
        sp.onItemSelectedListener = object : AdapterView.OnItemSelectedListener {
            override fun onItemSelected(a: AdapterView<*>?, v: View?, i: Int, l: Long) { cur = i }
            override fun onNothingSelected(a: AdapterView<*>?) {}
        }
        root.addView(st); root.addView(sp)

        stv = TextView(this).apply { textSize = 15f }
        ipEt = EditText(this).apply {
            hint = "IP ديال TV Box (مثال 192.168.1.20)"
            setText(getSharedPreferences("r", 0).getString("ip", ""))
            setSingleLine()
        }
        val find = Button(this).apply { text = "🔍 بحث عن الجهاز فالشبكة"; setOnClickListener { findBox() } }
        root.addView(ipEt); root.addView(find)

        val sb = Button(this)
        sb.text = "🔎 مسح أكواد IR"
        sb.setOnClickListener {
            if (PROFILES[cur].proto == 3 || ir?.hasIrEmitter() != true) { Toast.makeText(this, "خاص IR وبروفايل IR", Toast.LENGTH_SHORT).show(); return@setOnClickListener }
            scanning = !scanning
            if (scanning) { sc = 0; sb.text = "⏹ وقّف"; h.post(tick) }
            else {
                h.removeCallbacks(tick)
                sb.text = "🔎 مسح أكواد IR"
                val a = (sc + 255) and 255
                stv.text = "وقفتي عند " + a + " (0x" + Integer.toHexString(a) + ") — جرّب حتى " + ((a + 255) and 255) + " و" + ((a + 254) and 255)
            }
        }
        root.addView(sb); root.addView(stv)

        fun row(vararg b: Pair<String, String>) {
            val r = LinearLayout(this).apply { orientation = LinearLayout.HORIZONTAL }
            for ((label, key) in b) {
                r.addView(Button(this).apply {
                    text = label; textSize = 18f
                    layoutParams = LinearLayout.LayoutParams(0, 170, 1f)
                    setOnClickListener { send(key, it) }
                })
            }
            root.addView(r)
        }
        row("⏻" to "POWER", "🔀 مصدر" to "INPUT", "🔇" to "MUTE")
        row("🔊 +" to "VOLUP", "🔉 -" to "VOLDN")
        row("⏯ Pause" to "PLAY", "MENU" to "MENU")
        row("▲" to "UP")
        row("◀" to "LEFT", "OK" to "OK", "▶" to "RIGHT")
        row("▼" to "DOWN")
        row("HOME" to "HOME", "↩ رجوع" to "BACK")
        row("⚙ الإعدادات" to "SETTINGS")

        setContentView(ScrollView(this).apply { addView(root) })
        if (ipEt.text.isEmpty()) findBox()
    }
}
