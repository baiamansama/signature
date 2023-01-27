import java.security.MessageDigest

import scala.util.Try

val q:BigInt = BigInt("4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787")

def I2OSP(val: BigInt, length: Int): Array[Byte] = {
    if (val < 0 || val >= (1 << (8 * length))) {
        throw new IllegalArgumentException(s"bad I2OSP call: val=$val length=$length")
    }
    val ret = Array.ofDim[Byte](length)
    var val_ = val
    for (idx <- (length - 1) to 0 by -1) {
        ret(idx) = (val_ & 0xFF).toByte
        val_ = val_ >> 8
    }
    ret
}

def OS2IP(octets: Array[Byte]): BigInt = {
    var ret = BigInt(0)
    for (o <- octets) {
        ret = (ret << 8) + BigInt(o & 0xff)
    }
    ret
}

def _strxor(str1: Array[Byte], str2: Array[Byte]): Array[Byte] = {
    (str1 zip str2).map { case (s1, s2) => (s1 ^ s2).toByte }
}

def expand_message_xmd(msg: Array[Byte], DST: Array[Byte], len_in_bytes: Int, hash_fn: String): Array[Byte] = {
    val b_in_bytes = MessageDigest.getInstance(hash_fn).getDigestLength
    val r_in_bytes = MessageDigest.getInstance(hash_fn).getBlockLength

    val ell = (len_in_bytes + b_in_bytes - 1) / b_in_bytes
    if (ell > 255) {
        throw new IllegalArgumentException(s"expand_message_xmd: ell=$ell out of range")
    }
    val DST_prime = DST ++ I2OSP(DST.length, 1)
    val Z_pad = I2OSP(0, r_in_bytes)
    val l_i_b_str = I2OSP(len_in_bytes, 2)

    val b_0 = MessageDigest.getInstance(hash_fn).digest(Z_pad ++ msg ++ l_i_b_str ++ I2OSP(0, 1) ++ DST_prime)
    val b_vals = Array.ofDim[Array[Byte]](ell)
    b_vals(0) = MessageDigest.getInstance(hash_fn).digest(b_0 ++ I2OSP(1, 1) ++ DST_prime)
    for (idx <- 1 until ell) {
        b_vals(idx) = MessageDigest.getInstance(hash_fn).digest(_strxor(b_0, b_vals(idx - 1)) ++ I2OSP(idx + 1, 1) ++ DST_prime)
    }
    val pseudo_random_bytes = b_vals.reduce(_ ++ _)
    pseudo_random_bytes.slice(0, len_in_bytes)
}

def expand_message_xof(msg: Array[Byte], DST: Array[Byte], len_in_bytes: Int, hash_fn: String): Array[Byte] = {
    val DST_prime = DST ++ I2OSP(DST.length, 1)
    val msg_prime = msg ++ I2OSP(len_in_bytes, 2) ++ DST_prime
    Try(MessageDigest.getInstance(hash_fn).digest(msg_prime)).getOrElse(Array.emptyByteArray)
}

def hash_to_field(msg: Array[Byte], count: Int, DST: Array[Byte], modulus: BigInt, degree: Int, blen: Int, expand_fn: (Array[Byte], Array[Byte], Int, String) => Array[Byte], hash_fn: String): Array[Array[BigInt]] = {
    val len_in_bytes = count * degree * blen
    val pseudo_random_bytes = expand_fn(msg, DST, len_in_bytes, hash_fn)

    val u_vals = Array.ofDim[Array[BigInt]](count)
    for (idx <- 0 until count) {
        val e_vals = Array.ofDim[BigInt](degree)
        for (jdx <- 0 until degree) {
            val elm_offset = blen * (jdx + idx * degree)
            val tv = pseudo_random_bytes.slice(elm_offset, elm_offset + blen)
            e_vals(jdx) = OS2IP(tv) % modulus
        }
        u_vals(idx) = e_vals
    }
    u_vals
}

def Hp(msg: Array[Byte], count: Int, dst: Array[Byte]): Array[Array[BigInt]] = {
    if (!msg.isInstanceOf[Array[Byte]]) {
        throw new IllegalArgumentException("Hp can't hash anything but bytes")
    }
    hash_to_field(msg, count, dst, q, 1, 64, expand_message_xmd, "SHA-256")
}

def Hp2(msg: Array[Byte], count: Int, dst: Array[Byte]): List[List[BigInt]] = {
    if (!msg.isInstanceOf[Array[Byte]]) {
        throw new IllegalArgumentException("Hp2 can't hash anything but bytes")
    }
    hash_to_field(msg, count, dst, q, 2, 64, expand_message_xmd, "SHA-256")
}

