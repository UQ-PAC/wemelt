package object tool {
  object error {

    abstract class Error extends Exception {
      def info: Seq[Any]

      override def toString = info.mkString(" ")
    }

    case class InvalidProgram(info: Any*) extends Error
    case class ProgramError(info: Any*) extends Error
    case class Z3Error(info: Any*) extends Error

    case class WhileError(line: Int, test: Expression, message: String) extends Exception {
      override def toString = "line " + line + ": WHILE rule not valid for while(" + test + ") {...} as " + message
    }
    case class AssignError(line: Int, lhs: Id, rhs: Expression, message: String)  extends Exception {
      override def toString = "line " + line + ": ASSIGN rule not valid for " + lhs + " = " + rhs + " as " + message
    }
    case class AssignCError(line: Int, lhs: Id, rhs: Expression, message: String)  extends Exception {
      override def toString = "line " + line + ": ASSIGNC rule not valid for " + lhs + " = " + rhs + " as " + message
    }
    case class IfError(line: Int, test: Expression, message: String) extends Exception {
      override def toString = "line " + line + ": IF rule not valid for if(" + test + ") {...} as " + message
    }
    case class NonblockingError(line: Int, lhs: Id, rhs: Expression, message: String) extends Exception {
      override def toString = "line " + line + ": NONBLOCKING rule not valid for " + lhs + " = " + rhs + " as " + message
    }

  }
  
  type Rename = Map[Var, Var]
  type Subst = Map[Expression, Var]

  object Subst {
    val empty: Subst = Map()

    def apply(xs: (Expression, Var)*): Subst = {
      xs.toMap
    }

    def fresh(xs: Set[Var]): Rename = {
      xs.map(x => (x, x.fresh)).toMap
    }

    def refresh(bound: Set[Var], xs: Set[Var]): (Set[Var], Rename) = {
      assert(xs subsetOf bound)
      val su = Subst.fresh(xs)
      val ty = xs map (x => su(x))
      (bound -- xs ++ ty, su)
    }

  }

  val sub = "₀₁₂₃₄₅₆₇₈₉"
  implicit class StringOps(self: String) {
    def prime = self + "'"

    def __(index: Int): String = {
      self + (index.toString map (n => sub(n - '0')))
    }

    def __(index: Option[Int]): String = index match {
      case None => self
      case Some(index) => this __ index
    }

  }

  implicit class DToString(D: Map[Id, (Set[Id], Set[Id], Set[Id], Set[Id])]) {
    def DStr: String = {
      val w_w: String = (D map (kv => kv._1 + " -> " + kv._2._1.mkString("(", " ", ")"))).mkString(", ")
      val w_r: String = (D map (kv => kv._1 + " -> " + kv._2._2.mkString("(", " ", ")"))).mkString(", ")
      val r_w: String = (D map (kv => kv._1 + " -> " + kv._2._3.mkString("(", " ", ")"))).mkString(", ")
      val r_r: String = (D map (kv => kv._1 + " -> " + kv._2._4.mkString("(", " ", ")"))).mkString(", ")
      "W_w: " + w_w + "\n   W_r: " + w_r + "\n   R_w: " + r_w + "\n   R_r: " + r_r
    }
  }

  implicit class PToString(P: List[Expression]) {
    def PStr: String = P.mkString(" && ")
  }

  implicit class GammaToString(gamma: Map[Id, Security]) {
    def gammaStr = gamma.mkString(", ")
  }

}
