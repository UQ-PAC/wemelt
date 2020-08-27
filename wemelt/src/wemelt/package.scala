package object wemelt {
  object error {

    abstract class Error extends Exception {
      def info: Seq[Any]

      override def toString: String = info.mkString(" ")
    }

    case class InvalidProgram(info: Any*) extends Error
    case class ProgramError(info: Any*) extends Error
    case class Z3Error(info: Any*) extends Error

    case class WhileError(line: Int, test: Expression, message: String) extends Exception {
      override def toString: String = "line " + line + ": WHILE rule not valid for while(" + test + ") {...} as " + message
    }
    case class AssignLError(line: Int, lhs: Var, rhs: Expression, message: String)  extends Exception {
      override def toString: String = "line " + line + ": ASSIGNL rule not valid for " + lhs + " = " + rhs + " as " + message
    }
    case class AssignGError(line: Int, lhs: Var, rhs: Expression, message: String)  extends Exception {
      override def toString: String = "line " + line + ": ASSIGNG rule not valid for " + lhs + " = " + rhs + " as " + message
    }
    case class StoreError(line: Int, index: Expression, rhs: Expression, message: String)  extends Exception {
      override def toString: String = "line " + line + ": STORE rule not valid for mem[" + index + "] = " + rhs + " as " + message
    }
    /*
    case class CASError(line: Int, lhs: Var, x: Var, r1: Expression, r2: Expression, message: String)  extends Exception {
      override def toString = "line " + line + ": CAS rule not valid for " + lhs + " = " + "CAS(" + x + ", " + r1 + ", " + r2 + ") as " + message
    }
    case class CASCError(line: Int, lhs: Var, x: Var, r1: Expression, r2: Expression, message: String)  extends Exception {
      override def toString = "line " + line + ": CASC rule not valid for " + lhs + " = " + "CAS(" + x + ", " + r1 + ", " + r2 + ") as " + message
    }
     */
    case class IfError(line: Int, test: Expression, message: String) extends Exception {
      override def toString: String = "line " + line + ": IF rule not valid for if(" + test + ") {...} as " + message
    }
    /*
    case class ArrayError(line: Int, a: Var, index: Expression, rhs: Expression, message: String) extends Exception {
      override def toString = "line " + line + ": ARRAY ASSIGN rule not valid for " + a + "[" + index + "] = " + rhs + " as " + message
    }
    case class ArrayCError(line: Int, a: Var, index: Expression, rhs: Expression, message: String) extends Exception {
      override def toString = "line " + line + ": ARRAY ASSIGNC rule not valid for " + a + "[" + index + "] = " + rhs + " as " + message
    }
     */

  }

  type Subst = Map[Expression, Expression]
  type DType = Map[Var, (Set[Var], Set[Var], Set[Var], Set[Var], Set[Var], Set[Var], Set[Var], Set[Var])]

  val sub = "₀₁₂₃₄₅₆₇₈₉"
  implicit class StringOps(self: String) {
    def prime: String = self + "'"

    def __(index: Int): String = {
      self + (index.toString map (n => sub(n - '0')))
    }

    def __(index: Option[Int]): String = index match {
      case None => self
      case Some(index) => this __ index
    }

    def arrayIndex(index: Int): String = self + "[" + index + "]"

  }

  val newline: String ="""
      |""".stripMargin

  implicit class DToString(D: DType) {
    def DStr: String = {
      val w_w: String = (D map (kv => kv._1 + " -> " + kv._2._1.mkString("(", " ", ")"))).mkString("," + newline + "        ")
      val w_r: String = (D map (kv => kv._1 + " -> " + kv._2._2.mkString("(", " ", ")"))).mkString("," + newline + "        ")
      val r_w: String = (D map (kv => kv._1 + " -> " + kv._2._3.mkString("(", " ", ")"))).mkString("," + newline + "        ")
      val r_r: String = (D map (kv => kv._1 + " -> " + kv._2._4.mkString("(", " ", ")"))).mkString("," + newline + "        ")
      val i_w: String = (D map (kv => kv._1 + " -> " + kv._2._5.mkString("(", " ", ")"))).mkString("," + newline + "        ")
      val i_r: String = (D map (kv => kv._1 + " -> " + kv._2._6.mkString("(", " ", ")"))).mkString("," + newline + "        ")
      val u_w: String = (D map (kv => kv._1 + " -> " + kv._2._7.mkString("(", " ", ")"))).mkString("," + newline + "        ")
      val u_r: String = (D map (kv => kv._1 + " -> " + kv._2._8.mkString("(", " ", ")"))).mkString("," + newline + "        ")
      "W_w: " + w_w + newline + "   W_r: " + w_r + newline + "   R_w: " + r_w + newline + "   R_r: " + r_r + newline +
      "   I_w: " + i_w + newline + "   I_r: " + i_r + newline + "   U_w: " + u_w + newline + "   U_r: " + u_r
    }
  }

  implicit class PToString(P: List[Expression]) {
    def PStr: String = P.mkString(" &&" + newline + "   ")
  }

  implicit class OrToString(exprs: List[Expression]) {
    def OrStr: String = exprs.mkString(" ||" + newline + "   ")
  }

  implicit class GammaToString(gamma: Map[Var, Predicate]) {
    def gammaStr: String = gamma.mkString(", ")
  }
}
