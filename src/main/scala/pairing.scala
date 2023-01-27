import scala.collection.immutable.List

import bls12381.* 
import ec.*
import fields.* 

case class EC(q: BigInt, a: BigInt, b: BigInt, gx: BigInt, gy: BigInt, g2x: BigInt, g2y: BigInt, n: BigInt, h: BigInt, x: BigInt, k: BigInt, sqrt_n3: BigInt, sqrt_n3m1o2: BigInt)

val default_ec = EC(bls12381.parameters())
val default_ec_twist = EC(bls12381.parameters())

def int_to_bits(i: Int): List[Int] = {
  if (i < 1) {
    return List(0)
  }
  var bits = List[Int]()
  var temp = i
  while (temp != 0) {
    bits = temp % 2 :: bits
    temp = temp / 2
  }
  bits
}

def double_line_eval(R: AffinePoint, P: AffinePoint, ec: EC = default_ec): BigInt = {
  val R12 = untwist(R)

  val slope = (Fq(ec.q) * (R12.x ** 2) + ec.a) / (Fq(ec.q) * R12.y)
  val v = R12.y - slope * R12.x

  P.y - P.x * slope - v
}

def addLineEval(R: AffinePoint, Q: AffinePoint, P: AffinePoint, ec: EllipticCurve = defaultEC) : Fq = {
    val R12 = untwist(R)
    val Q12 = untwist(Q)

    if (R12 == Q12.negate()) {
        return P.x - R12.x
    }
    val slope = (Q12.y - R12.y) / (Q12.x - R12.x)
    val v = (Q12.y * R12.x - R12.y * Q12.x) / (R12.x - Q12.x)

    P.y - P.x * slope - v
}

def millerLoop(T: Int, P: AffinePoint, Q: AffinePoint, ec: EllipticCurve = defaultEC) : Fq12 = {
    val T_bits = intToBits(T)
    var R = Q
    var f = Fq12.one(ec.q)
    for (i <- 1 until T_bits.length) {
        val lrr = doubleLineEval(R, P, ec)
        f = f * f * lrr

        R = Fq(ec.q, 2) * R
        if (T_bits(i) == 1) {
            val lrq = addLineEval(R, Q, P, ec)
            f = f * lrq

            R = R + Q
        }
    }
    f
}

def finalExponentiation(element: Fq12, ec: EllipticCurve = defaultEC) : Fq12 = {
    if (ec.k == 12) {
        var ans = element.pow((math.pow(ec.q, 4) - math.pow(ec.q, 2) + 1) / ec.n)
        ans = ans.qiPower(2) * ans
        ans = ans.qiPower(6) / ans
        ans
    } else {
        element.pow((math.pow(ec.q, ec.k) - 1) / ec.n)
    }
}

def atePairing(P: JacobianPoint, Q: JacobianPoint, ec: EllipticCurve = defaultEC) : Fq12 = {
    val t = defaultEC.x + 1
    val T = math.abs(t - 1)
    val element = millerLoop(T, P.toAffine(), Q.toAffine(), ec)
    finalExponentiation(element, ec)
}

def atePairingMulti(Ps: List[JacobianPoint], Qs: List[JacobianPoint], ec: EllipticCurve = defaultEC) : Fq12 = {
    val t = defaultEC.x + 1
    val T = math.abs(t - 1)
    var prod = Fq12.one(ec.q)
    for (i <- 0 until Qs.length) {
        prod *= millerLoop(T, Ps(i).toAffine(), Qs(i).toAffine(), ec)
    }
    final_exponentiation(prod, ec.get)
}




