package tool

case class Fun(name: String) {
  override def toString = name
}

sealed trait Pure extends Prop {
  override def unary_!(): Pure = Pure.not(this)
  def &&(that: Pure): Pure = Pure.and(this, that)
  def subst(su: Subst): Pure

  def isRelational = false
}

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

}

case class Lit(v: Any) extends Expression with Pure {
  def free = Set()
  override def subst(su: Subst) = this
  override def toString = v.toString
}

case class Var(name: String, index: Option[Int] = None) extends Pure {
  def this(name: String) = this(name, None)

  def ident = Id(name)
  def free = Set(this)

  def fresh = Var.fresh(name)

  def subst(su: Subst) = su.getOrElse(this, this)

  // adjust?
  //override def toString = name __ index
}

object Var {
  var index = 0

  def fresh(name: String) = {
    index += 1
    Var(name, Some(index))
  }
}

case class App(fun: Fun, args: List[Pure]) extends Pure {
  def this(fun: String, args: List[Pure]) = this(Fun(fun), args)
  def this(fun: String) = this(fun, Nil)
  def this(fun: String, arg: Pure) = this(fun, List(arg))
  def this(fun: String, arg1: Pure, arg2: Pure) = this(fun, List(arg1, arg2))
  def this(fun: String, arg1: Pure, arg2: Pure, arg3: Pure) = this(fun, List(arg1, arg2, arg3))

  def free = Set() ++ (args flatMap (_.free))
  def subst(su: Subst) = App(fun, args map (_ subst su))

  override def toString = this match {
    case App(Fun("=="), List(arg1, arg2)) =>
      "(" + arg1 + " == " + arg2 + ")"
    case App(Fun("!="), List(App(Fun("=="), List(arg1, arg2)))) =>
      "(" + arg1 + " != " + arg2 + ")"
    case _ =>
      fun + args.mkString("(", ", ", ")")
  }
}