package tool

import scala.reflect.ClassTag
; /**
 * Converts parsed logical terms into appropriate logical data structures.
 *
 * While it is possible to keep pure formulas, propositions, locations, and assertions
 * almost separate in LALR, the whole distinction breaks down with connectives
 * (and, or, not, imp, eqv), which mess up the precedence levels,
 * lead to ambiguity, and prevent separate grouping by parenthesis for the individual types, too.
 * Hence, we parse all of these as "term"s (using beaver.Symbol) and take them apart later
 * using runtime casts, which have to be performed at some point (not that efficiency matters here anyway).
 */
object Term {
  type Term = beaver.Symbol

  object error {

    abstract class Error extends Exception {
      def info: Seq[Any]

      override def toString = info.mkString(" ")
    }

    case class InvalidProgram(info: Any*) extends Error

    case class VerificationFailure(info: Any*) extends Error

    case class InternalError(info: Any*) extends Error

  }

  def cast[B](a: Any, name: String)(implicit ev: ClassTag[B]): B = a match {
    case b: B =>
      b
    case _ =>
      throw error.InvalidProgram("illegal " + name, a)
  }

  def casts[B](as: Array[_], name: String)(implicit ev: ClassTag[B]): List[B] = {
    List.tabulate(as.length)(i => cast[B](as(i), name)(ev))
  }

  def loc(t: Term): Loc = cast[Loc](t, "location")
  def pure(t: Term): Pure = cast[Pure](t, "pure expression")
  def pures(ts: Array[Term]): List[Pure] = casts[Pure](ts, "pure expression")
  //def assrt(t: Term): Assert = cast[Assert](t, "assertion")

  def app(fun: String): Term = new App(fun)
  def app(fun: String, arg: Term): Term = new App(fun, pure(arg))
  def app(fun: String, arg1: Term, arg2: Term): Term = new App(fun, pure(arg1), pure(arg2))
  def app(fun: String, args: Array[Term]): Term = new App(fun, pures(args))

  /*
  def sec(arg: Term, sec: Term): Term = new Sec(pure(arg), pure(sec))

  def pto(ptr: Term, arg: Term): Term = new Pto(pure(ptr), pure(arg))
  def pto(ptr: Term, sec: Term, arg: Term): Term = new Pto(pure(ptr), pure(sec), pure(arg))

  def res(ptr: Term): Term = new Res(pure(ptr))

  def chunk(name: String): Term = new Chunk(name, List(), List())
  def chunk_in(name: String, in: Array[Term]): Term = new Chunk(name, pures(in), List())
  def chunk_out(name: String, out: Array[Term]): Term = new Chunk(name, List(), pures(out))
  def chunk(name: String, in: Array[Term], out: Array[Term]): Term = new Chunk(name, pures(in), pures(out))
   */

  /*
  def ref(arg: Term): Term = new Ref(loc(arg))
  def deref(arg: Term): Term = new DeRef(pure(arg))
  def deref(arg: Term, field: String): Term = new DeRefField(pure(arg), field)

  def exists(bound: Array[Param], body: Term): Term = body match {
    case body: Prop =>
      new Bind(Ex, List(bound: _*), body)
    case body: Assert =>
      new Exists(List(bound: _*), body)
    case _ =>
      throw error.InvalidProgram("illegal assertion", body)
  }

  def forall(bound: Array[Param], body: Term): Term = body match {
    case body: Prop =>
      new Bind(All, List(bound: _*), body)
    case _ =>
      throw error.InvalidProgram("illegal proposition", body)
  }
   */

  def question(test: Term, left: Term, right: Term): Term = (test, left, right) match {
    case (test: Pure, left: Pure, right: Pure) =>
      test question (left, right)
    //case (test: Prop, left: Assert, right: Assert) =>
    //  Cond(test, left, right)
    case _ =>
      throw error.InvalidProgram("illegal assertion", test + " ? " + left + " : " + right)
  }

  def not(prop: Term): Term = prop match {
    case prop: Pure =>
      !prop
    case prop: Prop =>
      !prop
    case _ =>
      throw error.InvalidProgram("illegal assertion", "! " + prop)
  }

  def and(left: Term, right: Term): Term = (left, right) match {
    case (left: Pure, right: Pure) =>
      left && right
    case (left: Prop, right: Prop) =>
      left && right
    //case (left: Assert, right: Assert) =>
     // left && right
    case _ =>
      throw error.InvalidProgram("illegal assertion", left + " && " + right)
  }

  def or(left: Term, right: Term): Term = (left, right) match {
    case (left: Pure, right: Pure) =>
      left || right
    case (left: Prop, right: Prop) =>
      left || right
    case _ =>
      throw error.InvalidProgram("illegal assertion", left + " || " + right)
  }

  /*
  def imp(left: Term, right: Term): Term = (left, right) match {
    case (left: Pure, right: Pure) =>
      left ==> right
    case (left: Prop, right: Prop) =>
      left ==> right
    case (left: Prop, right: Assert) =>
      left ==> right
    case _ =>
      throw error.InvalidProgram("illegal assertion", left + " ==> " + right)
  }

  def eqv(left: Term, right: Term): Term = (left, right) match {
    case (left: Pure, right: Pure) =>
      left <=> right
    case (left: Prop, right: Prop) =>
      left <=> right
    case _ =>
      throw error.InvalidProgram("illegal assertion", left + " <=> " + right)
  }
   */
}
