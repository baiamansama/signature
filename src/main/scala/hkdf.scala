import javax.crypto.Mac
import javax.crypto.spec.SecretKeySpec
import java.math.BigInteger
import java.nio.charset.StandardCharsets

val BLOCK_SIZE = 32

def extract(salt: Array[Byte], ikm: Array[Byte]): Array[Byte] = {
    val mac = Mac.getInstance("HmacSHA256")
    val secret = new SecretKeySpec(salt, "HmacSHA256")
    mac.init(secret)
    mac.doFinal(ikm)
}

def expand(L: Int, prk: Array[Byte], info: Array[Byte]): Array[Byte] = {
    val N: Int = math.ceil(L.toDouble / BLOCK_SIZE).toInt
    var bytes_written: Int = 0
    var okm: Array[Byte] = Array[Byte]()

    for (i <- 1 to N) {
        val h = if (i == 1) {
            val mac = Mac.getInstance("HmacSHA256")
            val secret = new SecretKeySpec(prk, "HmacSHA256")
            mac.init(secret)
            mac.update(info ++ Array[Byte](1))
            mac        } else {
            val mac = Mac.getInstance("HmacSHA256")
            val secret = new SecretKeySpec(prk, "HmacSHA256")
            mac.init(secret)
            mac.update(T ++ info ++ Array[Byte](i))
            mac
        }
        val T = h.doFinal()
        val to_write = L - bytes_written
        val write = if (to_write > BLOCK_SIZE) BLOCK_SIZE else to_write
        okm ++= T.slice(0, write)
        bytes_written += write
    }
    assert(bytes_written == L)
    okm
}ca

def extract_expand(L: Int, key: Array[Byte], salt: Array[Byte], info: Array[Byte]): Array[Byte] = {
    val prk = extract(salt, key)
    expand(L, prk, info)
}

