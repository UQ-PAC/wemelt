package tool

import com.microsoft.z3

object SMT {
  val intSize = 32 // size of bitvectors used
  val cfg = new java.util.HashMap[String, String]()
  val ctx = new z3.Context(cfg)
  val solver = ctx.mkSolver()

  val int_zero = ctx.mkInt(0)

  def prove(cond: Expression, given: List[Expression]) = {
    println("smt checking " + cond + " given " + given)
    solver.push()
    val res = try {
      for (p <- given) {
        solver.add(formula(p))
      }
      solver.add(formula(PreOp("!", cond)))

      solver.check
    } catch {
      case e: Throwable =>
        throw error.Z3Error("Z3 failed", cond, given, e)
    } finally {
      solver.pop()
    }

    println(res)
    res == z3.Status.SATISFIABLE
  }

  // recursively convert each list into AND structures
  def PToAnd(exprs: List[Expression]): z3.BoolExpr = exprs match {
      case Nil =>
        ctx.mkTrue

      case expr :: rest =>
        val xs = PToAnd(rest)
        val x =  ctx.mkAnd(formula(expr), xs)
        x
    }

  def proveImplies(strong: List[Expression], weak: List[Expression]) = {
    solver.push()
    val res = try {
      solver.add(ctx.mkImplies(PToAnd(strong), PToAnd(weak)))
      solver.check
    } catch {
      case e: Throwable =>
        throw error.Z3Error("Z3 failed", strong, weak, e)
    } finally {
      solver.pop()
    }

    res == z3.Status.SATISFIABLE
  }

  def formula(prop: Expression): z3.BoolExpr = translate(prop) match {
    case b: z3.BoolExpr => b
    case _ =>
      throw error.InvalidProgram("not a boolean expression", prop)
  }

  def arith(prop: Expression): z3.IntExpr = translate(prop) match {
    case arith: z3.IntExpr => arith
    // treating bit vectors as unsigned
    case bitVec: z3.BitVecExpr => ctx.mkBV2Int(bitVec, false)
    case _ =>
      throw error.InvalidProgram("not an arithmetic expression", prop)
  }

  def bitwise(prop: Expression): z3.BitVecExpr = translate(prop) match {
    case bitVec: z3.BitVecExpr => bitVec
    case arith: z3.IntExpr => ctx.mkInt2BV(intSize, arith)
    case _ =>
      throw error.InvalidProgram("not a bitwise expression", prop)
  }

  /* currently doing all arithmetic operations on ints - may want to switch to bitvectors
   and bitwise arithmetic operations for better simulation of the assembly
  https://z3prover.github.io/api/html/classcom_1_1microsoft_1_1z3_1_1_context.html */
  def translate(prop: Expression): z3.Expr = prop match {
    case x: Var => ctx.mkConst(x.toString, ctx.getIntSort)

    case Const._true => ctx.mkTrue
    case Const._false => ctx.mkFalse

    case Lit(n: Int) => ctx.mkInt(n)

    case x: Id =>
      throw error.InvalidProgram("unresolved program variable", x)

    case BinOp("=", arg1, arg2) => ctx.mkEq(translate(arg1), translate(arg2))
    case BinOp("==", arg1, arg2) => ctx.mkEq(translate(arg1), translate(arg2))

    case PreOp("!", arg) => ctx.mkNot(formula(arg))
    case BinOp("&&", arg1, arg2) => ctx.mkAnd(formula(arg1), formula(arg2))
    case BinOp("||", arg1, arg2) => ctx.mkOr(formula(arg1), formula(arg2))

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

    case BinOp("|", arg1, arg2) => ctx.mkBVOR(bitwise(arg1), bitwise(arg2))
    case BinOp("&", arg1, arg2) => ctx.mkBVAND(bitwise(arg1), bitwise(arg2))
    case BinOp("^", arg1, arg2) => ctx.mkBVXOR(bitwise(arg1), bitwise(arg2))
    case PreOp("~", arg) => ctx.mkBVNot(bitwise(arg))

      // defining normal right shift as logical shift right
    case BinOp(">>", arg1, arg2) => ctx.mkBVLSHR(bitwise(arg1), bitwise(arg2))
    case BinOp(">>>", arg1, arg2) => ctx.mkBVASHR(bitwise(arg1), bitwise(arg2))
    case BinOp("<<", arg1, arg2) => ctx.mkBVSHL(bitwise(arg1), bitwise(arg2))


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