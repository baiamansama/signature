import ec.* 
import pairing.* 
import private_key.*
import op_swu_g2.* 
import hd_keys.* 
import fields.* 

val basic_scheme_dst: Array[Byte] = "BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_NUL_".getBytes()
val aug_scheme_dst: Array[Byte] = "BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_AUG_".getBytes()
val pop_scheme_dst: Array[Byte] = "BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_".getBytes()
val pop_scheme_pop_dst: Array[Byte] = "BLS_POP_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_".getBytes()

def core_sign_mpl(sk: PrivateKey, message: Array[Byte], dst: Array[Byte]): JacobianPoint = {
    sk.value * g2_map(message, dst)
}

def core_verify_mpl(pk: JacobianPoint, message: Array[Byte], signature: JacobianPoint, dst: Array[Byte]): Boolean = {
    try {
        signature.check_valid()
        pk.check_valid()
    } catch {
        case e: AssertionError => return false
    }
    val q = g2_map(message, dst)
    val one = Fq12.one(default_ec.q)
    val pairing_result = ate_pairing_multi(List(pk, G1Generator().negate()), List(q, signature))
    pairing_result == one
}
def core_aggregate_mpl(signatures: List[JacobianPoint]): JacobianPoint = {
    if (signatures.length < 1) {
        throw new Exception("Must aggregate at least 1 signature")
    }
    var aggregate = signatures(0)
    aggregate.check_valid()
    for (i <- 1 until signatures.length) {
        val signature = signatures(i)
        signature.check_valid()
        aggregate += signature
    }
    aggregate
}

def core_aggregate_verify(pks: List[JacobianPoint], ms: List[Array[Byte]], signature: JacobianPoint, dst: Array[Byte]): Boolean = {
    if (pks.length != ms.length || pks.length < 1) {
        return false
    }
    try {
        signature.check_valid()
        var qs = List(signature)
        var ps = List(G1Generator().negate())
        for (i <- 0 until pks.length) {
            pks(i).check_valid()
            qs = qs :+ g2_map(ms(i), dst)
            ps = ps :+ pks(i)
        }
        Fq12.one(default_ec.q) == ate_pairing_multi(ps, qs)
    } catch {
        case e: AssertionError => return false
    }
}

class BasicSchemeMPL {
    def keyGen(seed: Array[Byte]): PrivateKey = {
        key_gen(seed)
    }
    def sign(sk: PrivateKey, message: Array[Byte]): JacobianPoint = {
        core_sign_mpl(sk, message, basic_scheme_dst)
    }

    def verify(pk: JacobianPoint, message: Array[Byte], signature: JacobianPoint): Boolean = {
        core_verify_mpl(pk, message, signature, basic_scheme_dst)
    }

    def aggregate(signatures: List[JacobianPoint]): JacobianPoint = {
        core_aggregate_mpl(signatures)
    }

    def aggregateVerify(pks: List[JacobianPoint], ms: List[Array[Byte]], signature: JacobianPoint): Boolean = {
        if (pks.size != ms.size || pks.size < 1) {
            return false
        }
        if (ms.toSet.size != ms.size) {
            return false
        }
        core_aggregate_verify(pks, ms, signature, basic_scheme_dst)
    }

    def deriveChildSK(sk: PrivateKey, index: Int): PrivateKey = {
        derive_child_sk(sk, index)
    }

    def deriveChildSKUnhardened(sk: PrivateKey, index: Int): PrivateKey = {
        derive_child_sk_unhardened(sk, index)
    }

    def deriveChildPKUnhardened(pk: JacobianPoint, index: Int): JacobianPoint = {
        derive_child_g1_unhardened(pk, index)
    }
}
class AugSchemeMPL {
    def keyGen(seed: Array[Byte]): PrivateKey = key_gen(seed)

    def sign(sk: PrivateKey, message: Array[Byte]): JacobianPoint = {
        val pk = sk.getG1()
        core_sign_mpl(sk, pk.toByteArray ++ message, aug_scheme_dst)
    }

    def verify(pk: JacobianPoint, message: Array[Byte], signature: JacobianPoint): Boolean = {
        core_verify_mpl(pk, pk.toByteArray ++ message, signature, aug_scheme_dst)
    }

    def aggregate(signatures: List[JacobianPoint]): JacobianPoint = {
        core_aggregate_mpl(signatures)
    }

    def aggregateVerify(pks: List[JacobianPoint], ms: List[Array[Byte]], signature: JacobianPoint): Boolean = {
        if (pks.size != ms.size || pks.size < 1) {
            return false
        }
        val m_primes = pks.zip(ms).map { case (pk, m) => pk.toByteArray ++ m }
        core_aggregate_verify(pks, m_primes, signature, aug_scheme_dst)
    }

    def deriveChildSk(sk: PrivateKey, index: Int): PrivateKey = {
        derive_child_sk(sk, index)
    }

    def deriveChildSkUnhardened(sk: PrivateKey, index: Int): PrivateKey = {
        derive_child_sk_unhardened(sk, index)
    }

    def deriveChildPkUnhardened(pk: JacobianPoint, index: Int): JacobianPoint = {
        derive_child_g1_unhardened(pk, index)
    }
}

class PopSchemeMPL {
    def key_gen(seed: Array[Byte]): PrivateKey = key_gen(seed)

    def sign(sk: PrivateKey, message: Array[Byte]): JacobianPoint = core_sign_mpl(sk, message, pop_scheme_dst)

    def verify(pk: JacobianPoint, message: Array[Byte], signature: JacobianPoint): Boolean = core_verify_mpl(pk, message, signature, pop_scheme_dst)

    def aggregate(signatures: List[JacobianPoint]): JacobianPoint = core_aggregate_mpl(signatures)

    def aggregate_verify(pks: List[JacobianPoint], ms: List[Array[Byte]], signature: JacobianPoint): Boolean = {
        if (pks.length != ms.length || pks.length < 1) return false
        core_aggregate_verify(pks, ms, signature, pop_scheme_dst)
    }

    def pop_prove(sk: PrivateKey): JacobianPoint = {
        val pk: JacobianPoint = sk.get_g1()
        sk.value * g2_map(pk.bytes, pop_scheme_pop_dst)
    }

    def pop_verify(pk: JacobianPoint, proof: JacobianPoint): Boolean = {
        try {
            proof.check_valid()
            pk.check_valid()
            val q = g2_map(pk.bytes, pop_scheme_pop_dst)
            val one = Fq12.one(default_ec.q)
            val pairing_result = ate_pairing_multi(List(pk, G1Generator().negate()), List(q, proof))
            pairing_result == one
        } catch {
            case _: AssertionError => false
        }
    }

    def fast_aggregate_verify(pks: List[JacobianPoint], message: Array[Byte], signature: JacobianPoint): Boolean = {
        if (pks.length < 1) return false
        var aggregate: JacobianPoint = pks(0)
        for (pk <- pks.tail) aggregate += pk
        core_verify_mpl(aggregate, message, signature, pop_scheme_dst)
    }

    def derive_child_sk(sk: PrivateKey, index: Int): PrivateKey = derive_child_sk(sk, index)

    def derive_child_sk_unhardened(sk: PrivateKey, index: Int): PrivateKey = derive_child_sk_unhardened(sk, index)

    def derive_child_pk_unhardened(pk: JacobianPoint, index: Int): JacobianPoint = derive_child_g1_unhardened(pk, index)
}
