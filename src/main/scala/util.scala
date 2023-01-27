import javax.crypto.Mac
import javax.crypto.spec.SecretKeySpec

val HMAC_BLOCK_SIZE = 64

def hash256(m: Array[Byte]): Array[Byte] = {
    val digest = MessageDigest.getInstance("SHA-256")
    digest.digest(m)
}

def hash512(m: Array[Byte]): Array[Byte] = {
    val digest = MessageDigest.getInstance("SHA-256")
    digest.digest(m ++ Array[Byte](0)) ++ digest.digest(m ++ Array[Byte](1))
}

def hmac256(m: Array[Byte], k: Array[Byte]): Array[Byte] = {
    val key = if (k.length > HMAC_BLOCK_SIZE) hash256(k) else k
    val keyPad = new Array[Byte](HMAC_BLOCK_SIZE)
    Array.copy(key, 0, keyPad, 0, key.length)
    Array.fill(keyPad, key.length, HMAC_BLOCK_SIZE)(0x00.toByte)
    val opad = Array.fill[Byte](HMAC_BLOCK_SIZE)(0x5C)
    val ipad = Array.fill[Byte](HMAC_BLOCK_SIZE)(0x36)
    val kopad = keyPad.zip(opad).map { case (a, b) => (a ^ b).toByte }
    val kipad = keyPad.zip(ipad).map { case (a, b) => (a ^ b).toByte }
    hash256(kopad ++ hash256(kipad ++ m))
}
