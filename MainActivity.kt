package com.rachid.remote

import android.app.Activity
import android.app.AlertDialog
import android.content.Context
import android.hardware.ConsumerIrManager
import android.net.ConnectivityManager
import android.net.Network
import android.net.NetworkCapabilities
import android.net.NetworkRequest
import android.net.wifi.WifiManager
import android.os.Build
import android.os.Bundle
import android.security.keystore.KeyGenParameterSpec
import android.security.keystore.KeyProperties
import android.view.HapticFeedbackConstants
import android.view.View
import android.widget.*
import dadb.AdbKeyPair
import dadb.Dadb
import java.io.ByteArrayOutputStream
import java.io.EOFException
import java.io.File
import java.io.InputStream
import java.io.OutputStream
import java.math.BigInteger
import java.net.InetSocketAddress
import java.net.Socket
import java.security.KeyPairGenerator
import java.security.KeyStore
import java.security.MessageDigest
import java.security.Principal
import java.security.PrivateKey
import java.security.cert.X509Certificate
import java.security.interfaces.RSAPublicKey
import java.util.concurrent.Executors
import java.util.concurrent.TimeUnit
import javax.net.ssl.SSLContext
import javax.net.ssl.SSLSocket
import javax.net.ssl.TrustManager
import javax.net.ssl.X509KeyManager
import javax.net.ssl.X509TrustManager
import javax.security.auth.x500.X500Principal

// proto: 0 = NEC, 1 = Samsung32, 2 = Sony SIRC-12, 3 = Wi-Fi (تلقائي: Android TV Remote أو ADB)
class P(val name: String, val proto: Int, val addr: Int, val k: Map<String, Int>)

val PROFILES = listOf(
    // الأرقام = Android KeyEvent
    P("Wi-Fi (تلقائي): أي Android TV / TV Box", 3, 0, mapOf("POWER" to 26, "MUTE" to 164, "VOLUP" to 24, "VOLDN" to 25,
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
    P("BenQ (0x30)", 0, 0x30, mapOf()),
    P("BenQ (0x0C)", 0, 0x0C, mapOf()),
    P("مخصص NEC", 0, 0x00, mapOf())
)

// ====================== Protobuf صغير ======================
object Pb {
    fun vint(v: Long): ByteArray {
        val o = ByteArrayOutputStream()
        var x = v
        while ((x and 0x7FL.inv()) != 0L) {
            o.write(((x and 0x7FL) or 0x80L).toInt())
            x = x ushr 7
        }
        o.write(x.toInt())
        return o.toByteArray()
    }
    fun tag(f: Int, w: Int): ByteArray = vint(((f shl 3) or w).toLong())
    fun i(f: Int, v: Long): ByteArray = tag(f, 0) + vint(v)
    fun b(f: Int, d: ByteArray): ByteArray = tag(f, 2) + vint(d.size.toLong()) + d
    fun s(f: Int, t: String): ByteArray = b(f, t.toByteArray())

    fun parse(d: ByteArray): List<Triple<Int, Int, Any>> {
        val r = ArrayList<Triple<Int, Int, Any>>()
        var p = 0
        fun rv(): Long {
            var res = 0L
            var sh = 0
            while (true) {
                val c = d[p++].toInt() and 0xFF
                res = res or ((c and 0x7F).toLong() shl sh)
                if ((c and 0x80) == 0) break
                sh += 7
            }
            return res
        }
        try {
            while (p < d.size) {
                val t = rv().toInt()
                val f = t shr 3
                when (t and 7) {
                    0 -> r.add(Triple(f, 0, rv()))
                    2 -> { val n = rv().toInt(); r.add(Triple(f, 2, d.copyOfRange(p, p + n))); p += n }
                    1 -> p += 8
                    5 -> p += 4
                    else -> return r
                }
            }
        } catch (e: Exception) {}
        return r
    }
}

fun writeMsg(o: OutputStream, body: ByteArray) {
    o.write(Pb.vint(body.size.toLong()) + body)
    o.flush()
}

fun readMsg(i: InputStream): ByteArray {
    var len = 0
    var sh = 0
    while (true) {
        val c = i.read()
        if (c < 0) throw EOFException()
        len = len or ((c and 0x7F) shl sh)
        if ((c and 0x80) == 0) break
        sh += 7
    }
    val buf = ByteArray(len)
    var off = 0
    while (off < len) {
        val n = i.read(buf, off, len - off)
        if (n < 0) throw EOFException()
        off += n
    }
    return buf
}

// ====================== TLS بشهادة العميل (محفوظة فـ Android Keystore) ======================
class FixedKm(val key: PrivateKey, val chain: Array<X509Certificate>) : X509KeyManager {
    override fun getClientAliases(keyType: String?, issuers: Array<Principal>?): Array<String>? = arrayOf("c")
    override fun chooseClientAlias(keyType: Array<String>?, issuers: Array<Principal>?, socket: Socket?): String? = "c"
    override fun getServerAliases(keyType: String?, issuers: Array<Principal>?): Array<String>? = null
    override fun chooseServerAlias(keyType: String?, issuers: Array<Principal>?, socket: Socket?): String? = null
    override fun getCertificateChain(alias: String?): Array<X509Certificate>? = chain
    override fun getPrivateKey(alias: String?): PrivateKey? = key
}

object Tls {
    private const val ALIAS = "remote_client"

    private fun ks(): KeyStore {
        val k = KeyStore.getInstance("AndroidKeyStore")
        k.load(null)
        return k
    }

    fun clientCert(): X509Certificate {
        val k = ks()
        if (!k.containsAlias(ALIAS)) {
            val g = KeyPairGenerator.getInstance(KeyProperties.KEY_ALGORITHM_RSA, "AndroidKeyStore")
            g.initialize(
                KeyGenParameterSpec.Builder(ALIAS, KeyProperties.PURPOSE_SIGN or KeyProperties.PURPOSE_VERIFY)
                    .setKeySize(2048)
                    .setDigests(KeyProperties.DIGEST_NONE, KeyProperties.DIGEST_SHA1, KeyProperties.DIGEST_SHA256,
                        KeyProperties.DIGEST_SHA384, KeyProperties.DIGEST_SHA512)
                    .setSignaturePaddings(KeyProperties.SIGNATURE_PADDING_RSA_PKCS1, KeyProperties.SIGNATURE_PADDING_RSA_PSS)
                    .setCertificateSubject(X500Principal("CN=remote"))
                    .setCertificateSerialNumber(BigInteger.ONE)
                    .build()
            )
            g.generateKeyPair()
        }
        return k.getCertificate(ALIAS) as X509Certificate
    }

    fun socket(ip: String, port: Int): SSLSocket {
        val cert = clientCert()
        val key = ks().getKey(ALIAS, null) as PrivateKey
        val tm = object : X509TrustManager {
            override fun checkClientTrusted(chain: Array<X509Certificate>?, authType: String?) {}
            override fun checkServerTrusted(chain: Array<X509Certificate>?, authType: String?) {}
            override fun getAcceptedIssuers(): Array<X509Certificate> = arrayOf()
        }
        val ctx = SSLContext.getInstance("TLS")
        ctx.init(arrayOf(FixedKm(key, arrayOf(cert))), arrayOf<TrustManager>(tm), null)
        val raw = Socket()
        raw.connect(InetSocketAddress(ip, port), 4000)
        val s = ctx.socketFactory.createSocket(raw, ip, port, true) as SSLSocket
        s.enabledProtocols = arrayOf("TLSv1.2")
        s.soTimeout = 0
        s.startHandshake()
        return s
    }
}

// ====================== الربط (Pairing) بكود فالتلفاز: المنفذ 6467 ======================
class Pairing(val ip: String) {
    private var s: SSLSocket? = null

    private fun outer(f: Int, payload: ByteArray): ByteArray = Pb.i(1, 2) + Pb.i(2, 200) + Pb.b(f, payload)

    private fun expect(i: InputStream) {
        val st = (Pb.parse(readMsg(i)).firstOrNull { it.first == 2 }?.third as? Long) ?: 0L
        if (st != 200L) throw Exception("status " + st)
    }

    private fun un(n: BigInteger): ByteArray {
        var b = n.toByteArray()
        if (b.size > 1 && b[0] == 0.toByte()) b = b.copyOfRange(1, b.size)
        return b
    }

    fun begin() {
        val sock = Tls.socket(ip, 6467)
        s = sock
        val i = sock.inputStream
        val o = sock.outputStream
        writeMsg(o, outer(10, Pb.s(1, "atvremote") + Pb.s(2, "androidtv-remote")))
        expect(i)
        writeMsg(o, outer(20, Pb.b(1, Pb.i(1, 3) + Pb.i(2, 6)) + Pb.i(3, 1)))
        expect(i)
        writeMsg(o, outer(30, Pb.b(1, Pb.i(1, 3) + Pb.i(2, 6)) + Pb.i(2, 1)))
        expect(i)
    }

    fun finish(code: String) {
        val sock = s ?: throw Exception("ما كاين ربط")
        val c = code.trim()
        if (c.length != 6 || !c.all { Character.digit(it, 16) >= 0 }) throw Exception("الكود خاص يكون 6 حروف/أرقام")
        val cp = Tls.clientCert().publicKey as RSAPublicKey
        val sp = sock.session.peerCertificates[0].publicKey as RSAPublicKey
        val md = MessageDigest.getInstance("SHA-256")
        md.update(un(cp.modulus)); md.update(un(cp.publicExponent))
        md.update(un(sp.modulus)); md.update(un(sp.publicExponent))
        val tail = c.substring(2)
        md.update(ByteArray(2) { tail.substring(it * 2, it * 2 + 2).toInt(16).toByte() })
        val h = md.digest()
        if ((h[0].toInt() and 0xFF) != c.substring(0, 2).toInt(16)) throw Exception("الكود غلط")
        writeMsg(sock.outputStream, outer(40, Pb.b(1, h)))
        expect(sock.inputStream)
        close()
    }

    fun close() { try { s?.close() } catch (e: Exception) {} }
}

// ====================== الريموت (Android TV Remote): المنفذ 6466 ======================
class RemoteConn(val ip: String, val onClose: () -> Unit) {
    private var s: SSLSocket? = null
    private var o: OutputStream? = null
    @Volatile var ready = false
    @Volatile var alive = false
    private val lk = Any()

    private fun send(body: ByteArray) { synchronized(lk) { writeMsg(o!!, body) } }

    fun open() {
        val sock = Tls.socket(ip, 6466)
        s = sock
        o = sock.outputStream
        alive = true
        val i = sock.inputStream
        Thread {
            try {
                while (true) {
                    for (f in Pb.parse(readMsg(i))) {
                        when (f.first) {
                            1 -> send(Pb.b(1, Pb.i(1, 622) + Pb.b(2,
                                Pb.s(1, "Remote") + Pb.s(2, "Rachid") + Pb.i(3, 1) + Pb.s(4, "1") +
                                Pb.s(5, "androidtv-remote") + Pb.s(6, "1.0.0"))))
                            2 -> send(Pb.b(2, Pb.i(1, 622)))
                            8 -> {
                                val v = (Pb.parse(f.third as ByteArray).firstOrNull { it.first == 1 }?.third as? Long) ?: 0L
                                send(Pb.b(9, Pb.i(1, v)))
                            }
                            40 -> ready = true
                        }
                    }
                }
            } catch (e: Exception) {
            } finally {
                alive = false
                ready = false
                onClose()
            }
        }.start()
    }

    fun key(code: Int) { send(Pb.b(10, Pb.i(1, code.toLong()) + Pb.i(2, 3))) }

    fun close() { try { s?.close() } catch (e: Exception) {} }
}

class MainActivity : Activity() {
    private var ir: ConsumerIrManager? = null
    private var cur = 0
    private lateinit var stv: TextView
    private lateinit var ipEt: EditText
    private lateinit var devBox: LinearLayout

    // 0 = ما متصلش، 1 = Android TV Remote، 2 = ADB
    @Volatile private var mode = 0
    private var rc: RemoteConn? = null
    private var pairing: Pairing? = null

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

    // ---------- ربط التطبيق بالواي فاي (يخدم حتى لو الراوتر بلا إنترنت) ----------
    private var wifiCb: ConnectivityManager.NetworkCallback? = null

    private fun bindWifi() {
        if (Build.VERSION.SDK_INT < 23) return
        try {
            val cm = getSystemService(Context.CONNECTIVITY_SERVICE) as ConnectivityManager
            val req = NetworkRequest.Builder()
                .addTransportType(NetworkCapabilities.TRANSPORT_WIFI)
                .removeCapability(NetworkCapabilities.NET_CAPABILITY_INTERNET)
                .build()
            val cb = object : ConnectivityManager.NetworkCallback() {
                override fun onAvailable(n: Network) { cm.bindProcessToNetwork(n) }
                override fun onLost(n: Network) { cm.bindProcessToNetwork(null) }
            }
            wifiCb = cb
            cm.requestNetwork(req, cb)
        } catch (e: Exception) {}
    }

    override fun onDestroy() {
        super.onDestroy()
        try {
            val cm = getSystemService(Context.CONNECTIVITY_SERVICE) as ConnectivityManager
            wifiCb?.let { cm.unregisterNetworkCallback(it) }
            if (Build.VERSION.SDK_INT >= 23) cm.bindProcessToNetwork(null)
        } catch (e: Exception) {}
        Thread { closeAll() }.start()
    }

    // ---------- ADB (احتياطي للأجهزة اللي ما فيهاش Android TV Remote) ----------
    private val ex = Executors.newSingleThreadExecutor()
    private var adb: Dadb? = null
    private var adbIp = ""

    private fun adbSend(cmd: String) {
        val ip = ipEt.text.toString().trim()
        if (ip.isEmpty()) { Toast.makeText(this, "كتب IP ديال الجهاز", Toast.LENGTH_SHORT).show(); return }
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

    // ---------- أدوات ----------
    private fun ui(t: String) { runOnUiThread { stv.text = t } }

    private fun portOpen(ip: String, port: Int): Boolean =
        try { Socket().use { it.connect(InetSocketAddress(ip, port), 400) }; true } catch (e: Exception) { false }

    private fun closeAll() {
        try { rc?.close() } catch (e: Exception) {}
        rc = null
        try { pairing?.close() } catch (e: Exception) {}
        pairing = null
        try { adb?.close() } catch (e: Exception) {}
        adb = null
        mode = 0
    }

    // ---------- البحث على الأجهزة ----------
    private fun findBox() {
        val ipI = (applicationContext.getSystemService(Context.WIFI_SERVICE) as WifiManager).dhcpInfo.ipAddress
        if (ipI == 0) { Toast.makeText(this, "ما متصلش بـ Wi-Fi", Toast.LENGTH_SHORT).show(); return }
        val base = (ipI and 255).toString() + "." + ((ipI shr 8) and 255) + "." + ((ipI shr 16) and 255) + "."
        stv.text = "كنقلب فالشبكة..."
        devBox.removeAllViews()
        Thread {
            val pool = Executors.newFixedThreadPool(64)
            val found = java.util.Collections.synchronizedList(ArrayList<String>())
            for (i in 1..254) pool.execute {
                val ip = base + i
                if (portOpen(ip, 6466)) found.add(ip + "|tv")
                else if (portOpen(ip, 5555)) found.add(ip + "|adb")
            }
            pool.shutdown(); pool.awaitTermination(20, TimeUnit.SECONDS)
            val list = found.toList().sortedBy { it.substringBefore('|').substringAfterLast('.').toInt() }
            runOnUiThread { showDevices(list) }
        }.start()
    }

    private fun showDevices(list: List<String>) {
        devBox.removeAllViews()
        if (list.isEmpty()) {
            stv.text = "ما لقيت جهاز. تأكد الهاتف والـ Box على نفس الراوتر والـ Box مشغل، ولا كتب IP واضغط اتصال"
            return
        }
        stv.text = "لقيت " + list.size + " — اضغط على الجهاز"
        for (e in list) {
            val ip = e.substringBefore('|')
            val type = if (e.endsWith("|tv")) "📺 Android TV (بكود ربط)" else "🔧 ADB"
            devBox.addView(Button(this).apply {
                text = type + "  " + ip
                setOnClickListener { connectTo(ip) }
            })
        }
    }

    // ---------- الاتصال ----------
    private fun connectTo(ip: String) {
        if (ip.isEmpty()) { Toast.makeText(this, "كتب IP", Toast.LENGTH_SHORT).show(); return }
        ipEt.setText(ip)
        getSharedPreferences("r", 0).edit().putString("ip", ip).apply()
        stv.text = "كنتصل بـ " + ip + " ..."
        ex.execute {
            try {
                closeAll()
                if (portOpen(ip, 6466)) {
                    if (getSharedPreferences("r", 0).getBoolean("paired_" + ip, false)) startRemote(ip) else startPairing(ip)
                } else if (portOpen(ip, 5555)) {
                    mode = 2
                    ui("متصل (ADB) ✅ " + ip + " — إلا طلع Allow فالتلفاز ضغط Always allow")
                } else {
                    ui("ما قدرتش نتصل بـ " + ip + ". تأكد الجهاز مشغل وعلى نفس الراوتر")
                }
            } catch (e: Exception) {
                ui("فشل: " + (e.message ?: e.javaClass.simpleName))
            }
        }
    }

    private fun startPairing(ip: String) {
        val p = Pairing(ip)
        pairing = p
        p.begin()
        ui("شوف التلفاز: خاص يبان كود")
        runOnUiThread { askCode(ip, p) }
    }

    private fun askCode(ip: String, p: Pairing) {
        val et = EditText(this).apply { hint = "الكود"; setSingleLine() }
        AlertDialog.Builder(this)
            .setTitle("الربط مع التلفاز")
            .setMessage("كتب الكود (6 حروف/أرقام) اللي طلع فالتلفاز")
            .setView(et)
            .setCancelable(false)
            .setPositiveButton("تأكيد") { _, _ ->
                val code = et.text.toString().trim()
                ex.execute {
                    try {
                        p.finish(code)
                        getSharedPreferences("r", 0).edit().putBoolean("paired_" + ip, true).apply()
                        ui("تم الربط ✅ كنتصل...")
                        startRemote(ip)
                    } catch (e: Exception) {
                        p.close()
                        ui("فشل الربط: " + (e.message ?: e.javaClass.simpleName) + " — اضغط على الجهاز من جديد")
                    }
                }
            }
            .setNegativeButton("إلغاء") { _, _ -> p.close(); ui("تلغى الربط") }
            .show()
    }

    private fun startRemote(ip: String) {
        val c = RemoteConn(ip) {
            runOnUiThread {
                if (rc?.alive != true && mode == 1) { mode = 0; stv.text = "تقطع الاتصال. اضغط على الجهاز من جديد" }
            }
        }
        rc = c
        c.open()
        var t = 0
        while (!c.ready && c.alive && t < 60) { Thread.sleep(100); t++ }
        if (c.ready) {
            mode = 1
            ui("متصل ✅ " + ip)
        } else {
            getSharedPreferences("r", 0).edit().remove("paired_" + ip).apply()
            c.close(); rc = null
            ui("ما نجحش الاتصال. اضغط على الجهاز من جديد باش يتعاود الربط بالكود")
        }
    }

    // ---------- إرسال ----------
    private fun send(key: String, v: View) {
        v.performHapticFeedback(HapticFeedbackConstants.VIRTUAL_KEY)
        val p = PROFILES[cur]
        val c = p.k[key]
        if (c == null) { Toast.makeText(this, "غير متوفر", Toast.LENGTH_SHORT).show(); return }
        if (p.proto == 3) {
            when (mode) {
                1 -> {
                    val code = if (c == -1) 176 else c
                    ex.execute {
                        try { rc?.key(code) } catch (e: Exception) { mode = 0; ui("تقطع الاتصال. اضغط على الجهاز من جديد") }
                    }
                }
                2 -> adbSend(if (c == -1) "am start -a android.settings.SETTINGS" else "input keyevent " + c)
                else -> Toast.makeText(this, "اضغط على الجهاز فاللائحة أولاً (ولا كتب IP واضغط اتصال)", Toast.LENGTH_LONG).show()
            }
            return
        }
        if (ir?.hasIrEmitter() != true) { Toast.makeText(this, "الهاتف ما فيهش IR", Toast.LENGTH_SHORT).show(); return }
        val (f, pat) = enc(p, c)
        ir?.transmit(f, pat)
    }

    override fun onCreate(s: Bundle?) {
        super.onCreate(s)
        bindWifi()
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
        devBox = LinearLayout(this).apply { orientation = LinearLayout.VERTICAL }
        ipEt = EditText(this).apply {
            hint = "IP ديال TV Box (مثال 192.168.1.20)"
            setText(getSharedPreferences("r", 0).getString("ip", ""))
            setSingleLine()
        }
        val find = Button(this).apply { text = "🔍 بحث عن الأجهزة فالشبكة"; setOnClickListener { findBox() } }
        val conn = Button(this).apply { text = "🔗 اتصال بهاد IP"; setOnClickListener { connectTo(ipEt.text.toString().trim()) } }
        root.addView(find); root.addView(devBox); root.addView(ipEt); root.addView(conn)

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
        row("🔴 ON/OFF" to "POWER", "🔀 مصدر" to "INPUT", "🔇" to "MUTE")
        row("🔊 +" to "VOLUP", "🔉 -" to "VOLDN")
        row("⏯ Pause" to "PLAY", "MENU" to "MENU")
        row("▲" to "UP")
        row("◀" to "LEFT", "OK" to "OK", "▶" to "RIGHT")
        row("▼" to "DOWN")
        row("HOME" to "HOME", "↩ رجوع" to "BACK")
        row("⚙ الإعدادات" to "SETTINGS")

        setContentView(ScrollView(this).apply { addView(root) })

        // تلقائي: بحث على الأجهزة، وإلا كان جهاز مربوط من قبل كيتصل بيه بوحدو
        val saved = getSharedPreferences("r", 0).getString("ip", "") ?: ""
        h.postDelayed({
            findBox()
            if (saved.isNotEmpty() && getSharedPreferences("r", 0).getBoolean("paired_" + saved, false)) connectTo(saved)
        }, 1000)
    }
}
