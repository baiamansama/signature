import ec.{G1Generator, G2Generator, JacobianPoint, default_ec}
import hkdf.{extract_expand}
import private_key.{PrivateKey}

def key_gen(seed: Array[Byte]): PrivateKey = {
    val L = 48
    val okm = extract_expand(L, seed ++ Array[Byte](0), "BLS-SIG-KEYGEN-SALT-".getBytes(), Array[Byte](0, L))
    new PrivateKey(BigInt(okm).mod(default_ec.n))
}

def ikm_to_lamport_sk(ikm: Array[Byte], salt: Array[Byte]): Array[Byte] = {
    extract_expand(32 * 255, ikm, salt, Array[Byte]())
}

def parent_sk_to_lamport_pk(parent_sk: PrivateKey, index: Int): Array[Byte] = {
    val salt = index.toByteArray
    val ikm = parent_sk.toByteArray
    val not_ikm = ikm.map(e => (e ^ 0xFF).toByte) // Flip bits
    val lamport0 = ikm_to_lamport_sk(ikm, salt)
    val lamport1 = ikm_to_lamport_sk(not_ikm, salt)

    var lamport_pk = Array[Byte]()
    for (i <- 0 until 255) {
        lamport_pk ++= hash256(lamport0.slice(i * 32, (i + 1) * 32))
    }
    for (i <- 0 until 255) {
        lamport_pk ++= hash256(lamport1.slice(i * 32, (i + 1) * 32))
    }

    hash256(lamport_pk)
}
def derive_child_sk(parent_sk: PrivateKey, index: Int): PrivateKey = {
    val lamport_pk = parent_sk_to_lamport_pk(parent_sk, index)
    key_gen(lamport_pk)
}

def derive_child_sk_unhardened(parent_sk: PrivateKey, index: Int): PrivateKey = {
    val h = hash256(parent_sk.get_g1().toByteArray ++ index.toByteArray)
    PrivateKey.aggregate(List(PrivateKey.from_bytes(h), parent_sk))
}

def derive_child_g1_unhardened(parent_pk: JacobianPoint, index: Int): JacobianPoint = {
    val h = hash256(parent_pk.toByteArray ++ index.toByteArray)
    parent_pk + (PrivateKey.from_bytes(h).value * G1Generator())
}

def derive_child_g2_unhardened(parent_pk: JacobianPoint, index: Int): JacobianPoint = {
    val h = hash256(parent_pk.toByteArray ++ index.toByteArray)
    parent_pk + (PrivateKey.from_bytes(h) * G2Generator())
}
