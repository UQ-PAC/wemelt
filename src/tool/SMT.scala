package tool

import com.microsoft.z3

object SMT {
  val cfg = new java.util.HashMap[String, String]()
  val ctx = new z3.Context(cfg)
  val solver = ctx.mkSolver()

  val int_zero = ctx.mkInt(0)

  def prove (cond: Expression, given: List[Expression]) = {
    solver.push()
    val res = try {
      for (p <- given)
        solver.add(formula(p))

      solver.add(ctx.mkNot(formula(cond)))
      solver.check
    } catch {
      case e: Throwable =>
        throw error.Z3Error("Z3 failed", cond, given, e)
    } finally {
      solver.pop()
    }

    res == z3.Status.UNSATISFIABLE
  }

  def formula(prop: Expression): z3.BoolExpr = translate(prop) match {
    case phi: z3.BoolExpr => phi
    case arith: z3.ArithExpr => ctx.mkNot(ctx.mkEq(arith, int_zero))
    case expr =>
      throw error.InvalidProgram("not a boolean expression", prop)
  }

  def arith(prop: Expression): z3.IntExpr = translate(prop) match {
    // only dealing with integers
    case arith: z3.IntExpr => arith
    case expr =>
      throw error.InvalidProgram("not an arithmetic expression", prop)
  }

  def translate(prop: Expression): z3.Expr = prop match {
    case x: Var => translate(x)

    // need to implement these
    //case Const._true => ctx.mkTrue
    //case Const._false => ctx.mkFalse

    case Lit(n: Int) => ctx.mkInt(n)

    case x: Id =>
      throw error.InvalidProgram("unresolved program variable", x)

    case BinOp("=", arg1, arg2) => ctx.mkEq(translate(arg1), translate(arg2))

    case PreOp("!", arg) => ctx.mkNot(formula(arg))
    case BinOp("&&", arg1, arg2) => ctx.mkAnd(formula(arg1), formula(arg2))
    case BinOp("||", arg1, arg2) => ctx.mkOr(formula(arg1), formula(arg2))
    case BinOp("==", arg1, arg2) => ctx.mkEq(formula(arg1), formula(arg2))

    case PreOp("-", arg) => ctx.mkUnaryMinus(arith(arg))
    case BinOp("+", arg1, arg2) => ctx.mkAdd(arith(arg1), arith(arg2))
    case BinOp("-", arg1, arg2) => ctx.mkSub(arith(arg1), arith(arg2))
    case BinOp("*", arg1, arg2) => ctx.mkMul(arith(arg1), arith(arg2))
    case BinOp("/", arg1, arg2) => ctx.mkDiv(arith(arg1), arith(arg2))
    case BinOp("%", arg1, arg2) => ctx.mkMod(arith(arg1), arith(arg2))

    case BinOp("<=", arg1, arg2) => ctx.mkLe(arith(arg1), arith(arg2))
    case BinOp("<", arg1, arg2) => ctx.mkLt(arith(arg1), arith(arg2))
    case BinOp(">=", arg1, arg2) => ctx.mkGe(arith(arg1), arith(arg2))
    case BinOp(">", arg1, arg2) => ctx.mkGt(arith(arg1), arith(arg2))

      // need to properly implement, probably convert to bitvector, then back??
      /*
    case BinOp("|", arg1, arg2) => ctx.mkGt(bitwise(arg1), bitwise(arg2))
    case BinOp("&", arg1, arg2) => ctx.mkGt(bitwise(arg1), bitwise(arg2))
    case BinOp("^", arg1, arg2) => ctx.mkGt(bitwise(arg1), bitwise(arg2))
       */

        /*
    case Pure.array_select(arg1, arg2) =>
      ctx.mkSelect(array(arg1), translate(arg2))
    case Pure.array_store(arg1, arg2, arg3) =>
      ctx.mkStore(array(arg1), translate(arg2), translate(arg3))
         */

    case _ =>
      throw error.InvalidProgram("cannot translate to SMT", prop)
  }


}