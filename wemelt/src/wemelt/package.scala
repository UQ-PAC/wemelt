package object wemelt {
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
    case class CASError(line: Int, lhs: Id, x: Id, r1: Expression, r2: Expression, message: String)  extends Exception {
      override def toString = "line " + line + ": CAS rule not valid for " + lhs + " = " + "CAS(" + x + ", " + r1 + ", " + r2 + ") as " + message
    }
    case class CASCError(line: Int, lhs: Id, x: Id, r1: Expression, r2: Expression, message: String)  extends Exception {
      override def toString = "line " + line + ": CASC rule not valid for " + lhs + " = " + "CAS(" + x + ", " + r1 + ", " + r2 + ") as " + message
    }
    case class IfError(line: Int, test: Expression, message: String) extends Exception {
      override def toString = "line " + line + ": IF rule not valid for if(" + test + ") {...} as " + message
    }
    case class NonblockingError(line: Int, statement: Statement, message: String) extends Exception {
      override def toString = "line " + line + ": NONBLOCKING rule not valid for " + statement + " as " + message
    }
    case class ArrayError(line: Int, a: Id, index: Expression, rhs: Expression, message: String) extends Exception {
      override def toString = "line " + line + ": ARRAY ASSIGN rule not valid for " + a + "[" + index + "] = " + rhs + " as " + message
    }
    case class ArrayCError(line: Int, a: Id, index: Expression, rhs: Expression, message: String) extends Exception {
      override def toString = "line " + line + ": ARRAY ASSIGNC rule not valid for " + a + "[" + index + "] = " + rhs + " as " + message
    }

  }

  type Subst = Map[Expression, Var]

  object Subst {
    val empty: Subst = Map()

    def apply(xs: (Expression, Var)*): Subst = {
      xs.toMap
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

    def arrayIndex(index: Int): String = self + "[" + index + "]"

  }

  val newline ="""
      |""".stripMargin

  implicit class DToString(D: Map[Id, (Set[Id], Set[Id], Set[Id], Set[Id])]) {
    def DStr: String = {
      val w_w: String = (D map (kv => kv._1 + " -> " + kv._2._1.mkString("(", " ", ")"))).mkString("," + newline + "        ")
      val w_r: String = (D map (kv => kv._1 + " -> " + kv._2._2.mkString("(", " ", ")"))).mkString("," + newline + "        ")
      val r_w: String = (D map (kv => kv._1 + " -> " + kv._2._3.mkString("(", " ", ")"))).mkString("," + newline + "        ")
      val r_r: String = (D map (kv => kv._1 + " -> " + kv._2._4.mkString("(", " ", ")"))).mkString("," + newline + "        ")
      "W_w: " + w_w + newline + "   W_r: " + w_r + newline + "   R_w: " + r_w + newline + "   R_r: " + r_r
    }
  }

  implicit class PToString(P: List[Expression]) {
    def PStr: String = P.mkString(" &&" + newline + "   ")
  }

  implicit class GammaToString(gamma: Map[Id, Security]) {
    def gammaStr = gamma.mkString(", ")
  }
}
