import scala.math._
import org.web3j.utils.Numeric //double chech this
import scala.util.control.DeepCopy //val newObject = DeepCopy.deepcopy(originalObject)
import scala.collection.mutable._

class Fq(val Q: Int, val value: Int):
    val extension: Int = 1

    def neg : Fq = new Fq(Q, -value)

    def +(other: Fq): Fq = {
        if (!other.isInstanceOf[Fq]) {
            return NotImplemented
        }
        new Fq(Q, value + other.value)
    }
    def -(other: Fq): Fq = {
        if (!other.isInstanceOf[Fq]) {
            return NotImplemented
        }
        new Fq(Q, other.value - value)
    }
    
    def *(other: Fq): Fq = this.*(other)

    override def equals(other: Any): Boolean = {
        if (!other.isInstanceOf[Fq]) {
            return false
        }
        val otherFq = other.asInstanceOf[Fq]
        return this.value == otherFq.value && this.Q == otherFq.Q
        }

    def <(other: Fq): Boolean = this.value < other.value

    def >(other: Fq): Boolean = this.value > other.value

    def <=(other: Fq): Boolean = this.value <= other.value

    def >=(other: Fq): Boolean = this.value >= other.value

    override def toString: String = {
        val s = Numeric.toHexString(this.value)
        val s2 = if (s.length > 10) s.slice(0, 7) + ".." + s.slice(-5) else s
        "Fq(" + s2 + ")"
    }

    override def toString: String = "Fq(" + Numeric.toHexString(this.value) + ")"

    def toByteArray: Array[Byte] = BigInt(this.value).toByteArray

    def fromBytes(buffer: Array[Byte], q: Int): Fq = {
        require(buffer.length == 48)
        new Fq(q, BigInt(buffer))
    }
    def pow(other: Any): Fq = {
        if (other == 0)
            new Fq(Q, 1)
        else if (other == 1)
            new Fq(Q, value)
        else if (other % 2 == 0)
            (math.pow(new Fq(Q, value * value), (other / 2)).asInstanceOf[Int])
        else
            (math.pow(new Fq(Q, value * value), (other / 2)).asInstanceOf[Int]) * this
    }

    def qiPower(i: Int): Fq = this

    def inv: Fq = {
        var x0 = 1
        var x1 = 0
        var y0 = 0
        var y1 = 1
        var a = Q.toInt
        var b = value.toInt
        while (a != 0) {
            val q = b / a
            val temp = a
            a = b % a
            b = temp
            val x0temp = x0
            x0 = x1
            x1 = x0temp - q * x1
            val y0temp = y0
            y0 = y1
            y1 = y0temp - q * y1
        }
        new Fq(Q, x0)
    }
    def floor(other: Any): Fq = {
        other match {
            case i: Int if !other.isInstanceOf[Fq] => this * Fq(Q, i).neg
            case o: Fq => this * o.neg
            case _ => throw new Exception("Invalid argument type")
        }
    }

    def iterator: Iterator[Fq] = Iterator(this)
    import scala.math._

def modsqrt: Fq = {
    if (value.toInt == 0) return new Fq(Q, 0)
    if (pow(value.toInt, (Q - 1) / 2, Q) != 1) throw new IllegalArgumentException("No sqrt exists")
    if (Q % 4 == 3) return new Fq(Q, pow(value.toInt, (Q + 1) / 4, Q))
    if (Q % 8 == 5) return new Fq(Q, pow(value.toInt, (Q + 3) / 8, Q))

    var S = 0
    var q = Q - 1
    while (q % 2 == 0) {
      q = q / 2
      S += 1
    }

    var z = 0
    for (i <- 0 until Q) {
      val euler = pow(i, (Q - 1) / 2, Q)
      if (euler == -1 % Q) {
        z = i
        break
      }
    }
    var M = S
    var c = pow(z, q, Q)
    var t = pow(value.toInt, q, Q)
    var R = pow(value.toInt, (q + 1) / 2, Q)

    while (true) {
      if (t == 0) return new Fq(Q, 0)
      if (t == 1) return new Fq(Q, R)
      var i = 0
      var f = t
      while (f != 1) {
        f = pow(f, 2, Q)
        i += 1
      }
      var b = pow(c, pow(2, M - i - 1, Q), Q)
      M = i
      c = pow(b, 2, Q)
      t = (t * c) % Q
      R = (R * b) % Q
    }
    new Fq(Q, 0)
  }
  def copy: Fq = new Fq(Q, value)

    def zero(Q: Int): Fq = new Fq(Q, 0)

    def one(Q: Int): Fq = new Fq(Q, 1)

    def fromFq(Q: Int, fq: Fq): Fq = fq

// next class

class FieldExtBase(val tuple: Any) {
    var root: Any = null
    var extension: Int = _
    var embedding: Int = _
    var basefield: Any = _
    var Q: Int = _

    def this(Q: Int, args: Any*) {
        this(args)
        try {
            val arg_extension = args(0).asInstanceOf[FieldExtBase].extension
            args(1).asInstanceOf[FieldExtBase].extension
        } catch {
            case _: Throwable =>
                if (args.size != 2)
                    throw new IllegalArgumentException("Invalid number of arguments")
                arg_extension = 1
                val new_args = args.map(a => new Fq(Q, a.asInstanceOf[Int]))
                args = new_args
        }
        if (arg_extension != 1) {
            if (args.size != embedding)
                throw new IllegalArgumentException("Invalid number of arguments")
            for (arg <- args)
                assert(arg.asInstanceOf[FieldExtBase].extension == arg_extension)
        }
        assert(args.forall(arg => arg.isInstanceOf[basefield.type]))
        this.Q = Q
    }

    def neg(): FieldExtBase = {
        val cls = this.getClass
        val ret = new FieldExtBase(tuple.map(x => -x))
        ret.Q = this.Q
        ret.root = this.root
        ret
    }

    def +(other: Any): FieldExtBase = {
        val cls = this.getClass
        var other_new: Seq[Any] = _
        if (!other.isInstanceOf[cls]) {
            if (!other.isInstanceOf[Int] && other.asInstanceOf[FieldExtBase].extension > this.extension)
                return NotImplemented
            other_new = Seq.fill(this.tuple.size)(basefield.zero(this.Q))
            other_new(0) = other_new(0).asInstanceOf[Fq] + other
        } else {
            other_new = other.asInstanceOf[FieldExtBase].tuple
        }
        val ret = new FieldExtBase((this.tuple, other_new).zipped.map(_ + _))
        ret.Q = this.Q
        ret.root = this.root
        ret
    }

    def radd(other: Any): FieldExtBase = this.+(other)

    def -(other: Any): FieldExtBase = this + (other.neg())

    def rsub(other: Any): FieldExtBase = this + (other.neg())

    def *(other: Any): FieldExtBase = {
        val cls = this.getClass
        var ret: FieldExtBase = _
        if (other.isInstanceOf[Int]) {
            ret = new FieldExtBase(tuple.map(x => x * other))
            ret.Q = this.Q
            ret.root = this.root
            ret
        } else {
            if (cls.extension < other.asInstanceOf[FieldExtBase].extension)
                return NotImplemented

            val buf = Seq.fill(this.tuple.size)(basefield.zero(this.Q))

            for (i <- this.tuple.indices) {
                val x = this.tuple(i)
                if (cls.extension == other.asInstanceOf[FieldExtBase].extension) {
                    for (j <- other.asInstanceOf[FieldExtBase].tuple.indices) {
                        val y = other.asInstanceOf[FieldExtBase].tuple(j)
                        if (x != null && y != null) {
                            if (i + j >= this.embedding)
                                buf(i + j % this.embedding) += x * y * this.root
                            else
                                buf(i + j % this.embedding) += x * y
                        }
                    }
                } else {
                    if (x != null) buf(i) = x * other
                }
            }
            ret = new FieldExtBase(buf)
            ret.Q = this.Q
            ret.root = this.root
            ret
        }
    
    def rmul(other: Any): Fq = this.*(other)

    def floordiv(other: Any): Fq = this * inv(other)

    def `==`(other: Any): Boolean = {
        if (!other.isInstanceOf[FieldExtBase]) {
            if (other.isInstanceOf[FieldExtBase] || other.isInstanceOf[Int]) {
                if (!other.isInstanceOf[FieldExtBase] || this.extension > other.asInstanceOf[FieldExtBase].extension) {
                    for (i <- 1 until this.embedding) {
                        if (this(i) != typeOf[root].zero(this.Q)) return false
                    }
                    return this(0) == other
                }
                return NotImplemented
            }
            return NotImplemented
        } else {
            return this == other.asInstanceOf[FieldExtBase] && this.Q == other.asInstanceOf[FieldExtBase].Q
        }
        }
    }

    def <(other: Any) = this.reverse.__lt__(other.reverse)
    def >(other: Any) = super.>(other)
    def !(other: Any) = !==(other)
    override def toString() = "Fq" + extension + "(" + args.mkString(", ") + ")"
    override def __repr__() = toString()

    def bytes: Array[Byte] = {
        var sumBytes = Array[Byte]()
        for (x <- this.reverse) {
            if (!x.isInstanceOf[FieldExtBase] && !x.isInstanceOf[Fq]) {
                x = Fq.fromFq(Q, x)
            }
            sumBytes = sumBytes ++ x.getBytes
            }
        sumBytes
    }
    def fromBytes(buffer: Array[Byte], Q: Int): FieldExt = {
        require(buffer.length == extension * 48, "buffer size must match extension")
        val embeddedSize = 48 * (extension / embedding)
        val tup = for (i <- 0 until embedding) yield buffer.slice(i * embeddedSize, (i + 1) * embeddedSize)
        new FieldExt(Q, tup.map(basefield.fromBytes(_, Q)).reverse)
    }

    def pow(e: Int): FieldExt = {
        require(e >= 0, "e must be non-negative")
        var ans = one(Q)
        var base = this
        ans.root = this.root

        while (e > 0) {
            if (e % 2 == 1) ans *= base
            base *= base
            e = e >> 1
        }
        ans
    }

    def boolean(): Boolean = {
        for(x <- this){
            if(x == true){
                return true
            }
        }
        return false
    }

    def setRoot(root: FieldExtBase): Unit = {
        this = root
    }

    def zero(Q: FieldExtBase): FieldExtBase = {
        this.fromFq(Q, Fq(Q, 0))
    }

    def one(Q: FieldExtBase): FieldExtBase = {
        this.fromFq(Q, Fq(Q, 1))
    }
    @classmethod
    // def from_fq(cls, Q, fq):
    //     y = cls.basefield.from_fq(Q, fq)
    //     z = cls.basefield.zero(Q)
    //     ret = super().__new__(cls, (z if i else y for i in range(cls.embedding)))
    //     ret.Q = Q
    //     if cls == Fq2:
    //         ret.set_root(Fq(Q, -1))
    //     elif cls == Fq6:
    //         ret.set_root(Fq2(Q, Fq.one(Q), Fq.one(Q)))
    //     elif cls == Fq12:
    //         r = Fq6(Q, Fq2.zero(Q), Fq2.one(Q), Fq2.zero(Q))
    //         ret.set_root(r)
    //     return ret

    // def __deepcopy__(self, memo):
    //     cls = type(self)
    //     ret = super().__new__(cls, (deepcopy(a, memo) for a in self))
    //     ret.Q = self.Q
    //     ret.root = self.root
    //     return ret

    // def qi_power(self, i):
    //     if self.Q != bls12381_q:
    //         raise NotImplementedError
    //     cls = type(self)
    //     i %= cls.extension
    //     if i == 0:
    //         return self
    //     ret = super().__new__(
    //         cls,
    //         (
    //             a.qi_power(i) * frob_coeffs[cls.extension, i, j] if j else a.qi_power(i)
    //             for j, a in enumerate(self)
    //         ),
    //     )
    //     ret.Q = self.Q
    //     ret.root = self.root
    //     return ret
















}

  




       

