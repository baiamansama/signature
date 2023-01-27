import scala.math.BigInt
import bls12381.{h_eff, q}
import ec.*
import fields.* 
import hash_to_field.* 
import scala.Option

def sgn0(x: Fq2): Int = {
  val sign_0 = x.value(0) % 2
  val zero_0 = x(0) == 0
  val sign_1 = x.value(1) % 2
  sign_0 | (zero_0 && sign_1)
}

val xi_2 = Fq2(q, -2, -1)

val Ell2p_a = Fq2(q, 0, 240)
val Ell2p_b = Fq2(q, 1012, 1012)

val ev1 = BigInt("699BE3B8C6870965E5BF892AD5D2CC7B0E85A117402DFD83B7F4A947E02D978498255A2AAEC0AC627B5AFBDF1BF1C90", 16)
val ev2 = BigInt("8157CD83046453F5DD0972B6E3949E4288020B5B8A9CC99CA07E27089A2CE2436D965026ADAD3EF7BABA37F2183E9B5", 16)
val ev3 = BigInt("AB1C2FFDD6C253CA155231EB3E71BA044FD562F6F72BC5BAD5EC46A0B7A3B0247CF08CE6C6317F40EDBC653A72DEE17", 16)
val ev4 = BigInt("AA404866706722864480885D68AD0CCAC1967C7544B447873CC37E0181271E006DF72162A3D3E0287BF597FBF7F8FC1", 16)
val etas = Array(Fq2(q, ev1, ev2), Fq2(q, q - ev2, ev1), Fq2(q, ev3, ev4), Fq2(q, q - ev4, ev3))

def osswu2_help(t: Fq2): JacobianPoint = {
    val num_den_common = xi_2.pow(2) * t.pow(4) + xi_2 * t.pow(2)
    val x0_num = Ell2p_b * (num_den_common + Fq(q, 1))
    var x0_den = -Ell2p_a * num_den_common
    if (x0_den == 0) x0_den = Ell2p_a * xi_2

    val gx0_den = pow(x0_den, 3)
    var gx0_num = Ell2p_b * gx0_den
    gx0_num += Ell2p_a * x0_num * pow(x0_den, 2)
    gx0_num += pow(x0_num, 3)

    var tmp1 = pow(gx0_den, 7)  
    var tmp2 = gx0_num * tmp1  
    tmp1 = tmp1 * tmp2 * gx0_den 
    val sqrt_candidate = tmp2 * pow(tmp1, (q ** 2 - 9) / 16)

    for (root <- roots_of_unity) {
        var y0 = sqrt_candidate * root
        if (y0.pow(2) * gx0_den == gx0_num) {
            if (sgn0(y0) != sgn0(t)) {
                y0 = -y0
            }
            assert(sgn0(y0) == sgn0(t))
            return JacobianPoint(x0_num * x0_den, y0 * pow(x0_den, 3), x0_den, false, default_ec_twist)
        }
    }

    val x1_num = xi_2 * t.pow(2) * x0_num
    val x1_den = x0_den
    val gx1_num = xi_2.pow(3) * t.pow(6) * gx0_num
    val gx1_den = gx0_den
    sqrt_candidate *= t.pow(3)
    for (eta <- etas) {
        var y1 = eta * sqrt_candidate
        if (y1.pow(2) * gx1_den == gx1_num) {
            if (sgn0(y1) != sgn0(t)) {
                y1 = -y1
            }
            assert(sgn0(y1) == sgn0(t))
            return JacobianPoint(x1_num * x1_den, y1 * pow(x1_den, 3), x1_den, false, default_ec_twist)
        }
    }

    throw new Exception("osswu2_help failed for unknown reasons")
}

val xnum = Array (
  Fq2 (q,
  BigInt ("0x5C759507E8E333EBB5B7A9A47D7ED8532C52D39FD3A042A88B58423C50AE15D5C2638E343D9C71C6238AAAAAAAA97D6",
  16),
  BigInt ("0x5C759507E8E333EBB5B7A9A47D7ED8532C52D39FD3A042A88B58423C50AE15D5C2638E343D9C71C6238AAAAAAAA97D6",
  16)), Fq2 (q, 0x0,
  BigInt ("0x11560BF17BAA99BC32126FCED787C88F984F87ADF7AE0C7F9A208C6B4F20A4181472AAA9CB8D555526A9FFFFFFFFC71A",
  16)), Fq2 (q,
  BigInt ("0x11560BF17BAA99BC32126FCED787C88F984F87ADF7AE0C7F9A208C6B4F20A4181472AAA9CB8D555526A9FFFFFFFFC71E",
  16),
  BigInt ("0x8AB05F8BDD54CDE190937E76BC3E447CC27C3D6FBD7063FCD104635A790520C0A395554E5C6AAAA9354FFFFFFFFE38D",
  16)), Fq2 (q,
  BigInt ("0x171D6541FA38CCFAED6DEA691F5FB614CB14B4E7F4E810AA22D6108F142B85757098E38D0F671C7188E2AAAAAAAA5ED1",
  16), 0x0)
)
val xden = Array (
  Fq2 (q, 0x0,
  BigInt ("0x1A0111EA397FE69A4B1BA7B6434BACD764774B84F38512BF6730D2A0F6B0F6241EABFFFEB153FFFFB9FEFFFFFFFFAA63",
  16)), Fq2 (q, 0xc,
  BigInt ("0x1A0111EA397FE69A4B1BA7B6434BACD764774B84F38512BF6730D2A0F6B0F6241EABFFFEB153FFFFB9FEFFFFFFFFAA9F",
  16)), Fq2 (q, 0x1, 0x0)
)
val ynum = Array (
  Fq2 (q,
  BigInt ("0x1530477C7AB4113B59A4C18B076D11930F7DA5D4A07F649BF54439D87D27E500FC8C25EBF8C92F6812CFC71C71C6D706",
  16),
  BigInt ("0x1530477C7AB4113B59A4C18B076D11930F7DA5D4A07F649BF54439D87D27E500FC8C25EBF8C92F6812CFC71C71C6D706",
  16)), Fq2 (q, 0x0,
  BigInt ("0x5C759507E8E333EBB5B7A9A47D7ED8532C52D39FD3A042A88B58423C50AE15D5C2638E343D9C71C6238AAAAAAAA97BE",
  16)), Fq2 (q,
  BigInt ("0x11560BF17BAA99BC32126FCED787C88F984F87ADF7AE0C7F9A208C6B4F20A4181472AAA9CB8D555526A9FFFFFFFFC71C",
  16),
  BigInt ("0x8AB05F8BDD54CDE190937E76BC3E447CC27C3D6FBD7063FCD104635A790520C0A395554E5C6AAAA9354FFFFFFFFE38F",
  16)), Fq2 (q,
  BigInt ("0x124C9AD43B6CF79BFBF7043DE3811AD0761B0F37A1E26286B0E977C69AA274524E79097A56DC4BD9E1B371C71C718B10",
  16), 0x0)
)
val yden = Array (
  Fq2 (
    q,
    BigInt ("0x1A0111EA397FE69A4B1BA7B6434BACD764774B84F38512BF6730D2A0F6B0F6241EABFFFEB153FFFFB9FEFFFFFFFFA8FB"),
    BigInt ("0x1A0111EA397FE69A4B1BA7B6434BACD764774B84F38512BF6730D2A0F6B0F6241EABFFFEB153FFFFB9FEFFFFFFFFA8FB"),
  ), Fq2 (
    q, 0x0,
    BigInt ("0x1A0111EA397FE69A4B1BA7B6434BACD764774B84F38512BF6730D2A0F6B0F6241EABFFFEB153FFFFB9FEFFFFFFFFA9D3"),
  ), Fq2 (
    q, 0x12,
    BigInt ("0x1A0111EA397FE69A4B1BA7B6434BACD764774B84F38512BF6730D2A0F6B0F6241EABFFFEB153FFFFB9FEFFFFFFFFAA99"),
  ), Fq2 (q, 0x1, 0x0),
)

def iso3(P: JacobianPoint): JacobianPoint = eval_iso(P, (xnum, xden, ynum, yden), default_ec_twist)

def opt_swu2_map(t: Fq2, t2: Option[Fq2] = None): JacobianPoint = {
    val Pp = iso3(osswu2_help(t))
    val Pp2 = if (t2.isDefined) iso3(osswu2_help(t2)) else JacobianPoint(Fq2(0), Fq2(0), Fq2(0))
    Pp + Pp2
}
