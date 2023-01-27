import ec.* 
import hkdf.* 

class PrivateKey(val value: BigInt) {
    val PRIVATE_KEY_SIZE = 32

    require(value < default_ec.n, s"Value must be less than the curve order (${default_ec.n})")

    def fromBytes(buffer: Array[Byte]): PrivateKey = {
        new PrivateKey(BigInt(buffer) % (default_ec.n))
    }

    def fromSeed(seed: Array[Byte]): PrivateKey = {
        val L = 48
        val okm = extract_expand(L, seed ++ Array(0.toByte), "BLS-SIG-KEYGEN-SALT-".getBytes(), Array(0, L))
        new PrivateKey(BigInt(okm) % (default_ec.n))
    }

    def fromInt(n: BigInt): PrivateKey = {
        new PrivateKey(n % (default_ec.n))
    }

    def getG1(): G1Generator = {
        value * G1Generator()
    }

    def sign(m: Array[Byte]): Unit = {
        // implementation here
    }

    override def ==(other: Any): Boolean = {
        other match {
            case that: PrivateKey => value == that.value
            case _ => false
        }
    }

    override def hashCode(): Int = {
        value.hashCode()
    }

    def toBytes: Array[Byte] = {
        value.toByteArray
    }

    def size(): Int = {
        PRIVATE_KEY_SIZE
    }

    override def toString(): String = {
        "PrivateKey(0x" + toBytes.map("%02x".format(_)).mkString + ")"
    }

    override def repr(): String = {
        "PrivateKey(0x" + toBytes.map("%02x".format(_)).mkString + ")"
    }

    def aggregate(privateKeys: Seq[PrivateKey]): PrivateKey = {
        new PrivateKey(privateKeys.map(_.value).sum % default_ec.n)
    }
}
