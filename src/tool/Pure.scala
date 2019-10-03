package tool

case class Fun(name: String) {
  override def toString = name
}

// Pure Expression
sealed trait Pure extends Prop {
  def unary_!(): Pure = Pure.not(this)
  def &&(that: Pure): Pure = Pure.and(this, that)
  def question(left: Pure, right: Pure): Pure = Pure.question(this, left, right)

 // def eval(st: Stack): Pure
  //def subst(su: Subst): Pure

  def isRelational = false
}

// ???
object Const {
  object void extends App("void")
  object low extends App("low")
  object high extends App("high")

  object _null extends App("null")
  object _true extends App("true")
  object _false extends App("false")
}

object Pure {
  class unary(val fun: Fun) {
    def this(name: String) = this(Fun(name))

    def unapply(pure: Pure) = pure match {
      case App(`fun`, List(arg)) => Some(arg)
      case _ => None
    }

    def apply(arg: Pure) = {
      App(fun, List(arg))
    }
  }

  class binary(val fun: Fun) {
    def this(name: String) = this(Fun(name))

    def unapply(pure: Pure) = pure match {
      case App(`fun`, List(arg1, arg2)) => Some((arg1, arg2))
      case _ => None
    }

    def apply(arg1: Pure, arg2: Pure): Pure = {
      App(fun, List(arg1, arg2))
    }
  }

  class ternary(val fun: Fun) {
    def this(name: String) = this(Fun(name))

    def unapply(pure: Pure) = pure match {
      case App(`fun`, List(arg1, arg2, arg3)) => Some((arg1, arg2, arg3))
      case _ => None
    }

    def apply(arg1: Pure, arg2: Pure, arg3: Pure): Pure = {
      App(fun, List(arg1, arg2, arg3))
    }
  }

  class nary(val fun: Fun) {
    def this(name: String) = this(Fun(name))

    def unapply(pure: Pure) = pure match {
      case App(`fun`, args) => Some(args)
      case _ => None
    }

    def apply(args: List[Pure]) = {
      App(fun, args)
    }
  }

  object not extends unary("!")
  object and extends binary("&&")
  object eq extends binary("==")
  object or extends binary("||")
  object imp extends binary("==>")
  object eqv extends binary("<=>")

  object uminus extends unary("-")
  object plus extends binary("+")
  object minus extends binary("-")
  object times extends binary("*")
  object divBy extends binary("/")
  object mod extends binary("%")

  object lt extends binary("<")
  object le extends binary("<=")
  object gt extends binary(">")
  object ge extends binary(">=")

  object question extends ternary("?:")

  object lower extends binary("lower")

  object distinct extends nary("distinct")

  object array_select extends binary("select")
  object array_store extends ternary("update")
}

trait Loc extends beaver.Symbol {
  def free: Set[Var]
  //def norm(st: Stack): Loc
  //def subst(su: Subst): Loc
}

// Literal
case class Lit(v: Any) extends Expression with Pure {
  def free = Set()
//  def eval(st: Stack) = this
  //override def subst(su: Subst) = this
  override def toString = v.toString
}

case class Var(name: String, index: Option[Int] = None) extends Pure {
  def this(name: String) = this(name, None)

  def ident = Id(name)
  //def prime = Var(name.prime, index)
  def free = Set(this)
/*
  def eval(st: Stack) = this match {
    case Var(name, None) if st contains ident =>
      val (typ, pure) = st(ident)
      assert(pure != this)
      // println("resolving " + this + " as program variable, assigned to " + pure)
      pure
    case _ =>
      this
  }

  def fresh = Var.fresh(name)

  def subst(su: Subst) = su.getOrElse(this, this)
 */
  //override def toString = name __ index
}

object Var {
  var index = 0
  /* Possibly outdated list of callers (including indirect ones)
   * - Var.fresh
   * - State.local
   * - State.param
   * - State.havoc
   *
   * - Exec._post (for return value)
   *
   * - Subst.refresh
   *   - Bound.refresh  (uncritical, variables remain bound)
   *   - Assert.refresh (similarly)
   *   - State.refresh  (similarly)
   */
  def fresh(name: String) = {
    index += 1
    Var(name, Some(index))
  }

  val attacker = Var("attacker")
  val result = Var("result")
}

case class Ref(loc: Loc) extends Pure {
  def free = loc.free
  //def eval(st: Stack) = Ref(loc norm st) // XXX: this maybe questionable
  //def subst(su: Subst) = Ref(loc subst su)
  override def toString = "&" + loc
}

object Ref {
  def apply(loc: Loc) = loc match {
    case DeRef(ptr) => ptr
    case _ => new Ref(loc)
  }
}

case class App(fun: Fun, args: List[Pure]) extends Pure {
  def this(fun: String, args: List[Pure]) = this(Fun(fun), args)
  def this(fun: String) = this(fun, Nil)
  def this(fun: String, arg: Pure) = this(fun, List(arg))
  def this(fun: String, arg1: Pure, arg2: Pure) = this(fun, List(arg1, arg2))
  def this(fun: String, arg1: Pure, arg2: Pure, arg3: Pure) = this(fun, List(arg1, arg2, arg3))

  def free = Set() ++ (args flatMap (_.free))
  //def eval(st: Stack) = App(fun, args map (_ eval st))
 // def subst(su: Subst) = App(fun, args map (_ subst su))

  override def toString = this match {
    case App(Fun("=="), List(arg1, arg2)) =>
      "(" + arg1 + " == " + arg2 + ")"
    case App(Fun("!="), List(App(Fun("=="), List(arg1, arg2)))) =>
      "(" + arg1 + " != " + arg2 + ")"
    case _ =>
      fun + args.mkString("(", ", ", ")")
  }
}

case class DeRef(ptr: Pure) extends Loc {
  def free = ptr.free
  //def norm(st: Stack) = DeRef(ptr eval st)
 // def subst(su: Subst) = DeRef(ptr subst su)
  override def toString = "*" + ptr
}

object DeRef {
  def apply(ptr: Pure) = ptr match {
    case Ref(loc) => loc
    case _ => new DeRef(ptr)
  }
}

case class DeRefField(ptr: Pure, field: String) extends Loc {
  def free = ptr.free
  //def norm(st: Stack) = DeRefField(ptr eval st, field)
  //def subst(su: Subst) = DeRefField(ptr subst su, field)
  override def toString = ptr + "->" + field
}

/** rather bad matching for array index expressionessions */
object ArrayIndex {
  def unapply(ptr: Pure): Option[(Var, Pure)] = ptr match {
    case Pure.plus(ptr: Var, index: Pure) =>
      Some((ptr, index))
    case Pure.plus(index: Pure, ptr: Var) =>
      Some((ptr, index))
    case _ =>
      None
  }
}
