package wemelt

import com.microsoft.z3

object SMT {
  val intSize = 32 // size of bitvectors used
  val cfg = new java.util.HashMap[String, String]()
  val ctx = new z3.Context(cfg)
  val solver = ctx.mkSolver()

  def prove(cond: Expression, given: List[Expression], debug: Boolean) = {
    if (debug)
      println("smt checking !(" + cond + ") given " + given.PStr)
    solver.push()
    val res = try {
      for (p <- given) {
        solver.add(formula(p))
      }
      // check that (NOT cond) AND P is unsatisfiable
      solver.add(formula(PreOp("!", cond)))

      solver.check
    } catch {
      case e: java.lang.UnsatisfiedLinkError if e.getMessage.equals("com.microsoft.z3.Native.INTERNALgetErrorMsgEx(JI)Ljava/lang/String;")=>
        // weird unintuitive error z3 can have when an input type is incorrect in a way it doesn't check
        throw error.Z3Error("Z3 failed", cond, given.PStr, "incorrect z3 expression type, probably involving ForAll/Exists")
      case e: Throwable =>
        throw error.Z3Error("Z3 failed", cond, given.PStr, e)
    } finally {
      solver.pop()
    }

    if (debug) {
      println(res)
      if (res == z3.Status.SATISFIABLE) {
        val model = solver.getModel
        println(model)
      }
    }
    res == z3.Status.UNSATISFIABLE
  }

  def proveSat(cond: Expression, given: List[Expression], debug: Boolean) = {
    if (debug)
      println("smt checking " + cond + " given " + given.PStr)
    solver.push()
    val res = try {
      for (p <- given) {
        solver.add(formula(p))
      }
      // check that cond AND P is satisfiable
      solver.add(formula(cond))

      solver.check
    } catch {
      case e: java.lang.UnsatisfiedLinkError if e.getMessage.equals("com.microsoft.z3.Native.INTERNALgetErrorMsgEx(JI)Ljava/lang/String;")=>
        // weird unintuitive error z3 can have when an input type is incorrect in a way it doesn't check
        throw error.Z3Error("Z3 failed", cond, given.PStr, "incorrect z3 expression type, probably involving ForAll/Exists")
      case e: Throwable =>
        throw error.Z3Error("Z3 failed", cond, given.PStr, e)
    } finally {
      solver.pop()
    }

    if (debug) {
      println(res)
      if (res == z3.Status.SATISFIABLE) {
        println(solver.getModel)
      }
    }
    res == z3.Status.SATISFIABLE
  }

  def proveP(given: List[Expression], debug: Boolean) = {
    if (debug)
      println("smt checking " + given.PStr)
    solver.push()
    val res = try {
      for (p <- given) {
        solver.add(formula(p))
      }
      solver.check
    } catch {
      case e: java.lang.UnsatisfiedLinkError if e.getMessage.equals("com.microsoft.z3.Native.INTERNALgetErrorMsgEx(JI)Ljava/lang/String;")=>
        // weird unintuitive error z3 can have when an input type is incorrect in a way it doesn't check
        throw error.Z3Error("Z3 failed", given.PStr, "incorrect z3 expression type, probably involving ForAll/Exists")
      case e: Throwable =>
        throw error.Z3Error("Z3 failed", given.PStr, e)
    } finally {
      solver.pop()
    }

    if (debug) {
      println(res)
      if (res == z3.Status.SATISFIABLE) {
        println(solver.getModel)
      }
    }
    res == z3.Status.SATISFIABLE
  }

  def proveImplies(strong: List[Expression], weak: List[Expression], debug: Boolean) = {
    if (debug)
      println("smt checking !(" + strong.PStr + newline + " implies " + weak.PStr + ")")
    solver.push()
    val res = try {
      solver.add(ctx.mkNot(ctx.mkImplies(PToAnd(strong), PToAnd(weak))))
      solver.check
    } catch {
      case e: Throwable =>
        throw error.Z3Error("Z3 failed", strong, weak, e)
    } finally {
      solver.pop()
    }
    if (debug) {
      println(res)
      if (res == z3.Status.SATISFIABLE) {
        println(solver.getModel)
      }
    }
    res == z3.Status.UNSATISFIABLE
  }

  def proveExpression(cond: Expression, debug: Boolean) = {
    if (debug)
      println("smt checking (" + cond + ")")
    solver.push()
    val res = try {
      // check that (NOT cond) is unsatisfiable
      solver.add(formula(cond))
      solver.check
    } catch {
      case e: java.lang.UnsatisfiedLinkError if e.getMessage.equals("com.microsoft.z3.Native.INTERNALgetErrorMsgEx(JI)Ljava/lang/String;")=>
        // weird unintuitive error z3 can have when an input type is incorrect in a way it doesn't check
        throw error.Z3Error("Z3 failed", cond, "incorrect z3 expression type, probably involving ForAll/Exists")
      case e: Throwable =>
        throw error.Z3Error("Z3 failed", cond, e)
    } finally {
      solver.pop()
    }

    if (debug) {
      println(res)
      if (res == z3.Status.SATISFIABLE) {
        val model = solver.getModel
        println(model)
      }
    }
    res == z3.Status.SATISFIABLE
  }

  // recursively convert expression list into AND structure
  def PToAnd(exprs: List[Expression]): z3.BoolExpr = exprs match {
    case Nil =>
      ctx.mkTrue

    case expr :: rest =>
      val xs = PToAnd(rest)
      val x = ctx.mkAnd(formula(expr), xs)
      x
  }

  def formula(prop: Expression): z3.BoolExpr = translate(prop) match {
    case b: z3.BoolExpr => b
    case e =>
      throw error.InvalidProgram("not a boolean expression", prop, e)
  }

  def arith(prop: Expression): z3.IntExpr = translate(prop) match {
    case arith: z3.IntExpr => arith
    // treating bit vectors as unsigned
    case bitVec: z3.BitVecExpr => ctx.mkBV2Int(bitVec, false)
    case e =>
      throw error.InvalidProgram("not an arithmetic expression", prop, e)
  }

  def bitwise(prop: Expression): z3.BitVecExpr = translate(prop) match {
    case bitVec: z3.BitVecExpr => bitVec
    case arith: z3.IntExpr => ctx.mkInt2BV(intSize, arith)
    case e =>
      throw error.InvalidProgram("not a bitwise expression", prop, e)
  }

  /* currently doing all arithmetic operations on ints - may want to switch to bitvectors
   and bitwise arithmetic operations for better simulation of the assembly semantics if this ends up being important
  https://z3prover.github.io/api/html/classcom_1_1microsoft_1_1z3_1_1_context.html */
  def translate(prop: Expression): z3.Expr = prop match {
    case x: Var => ctx.mkConst(x.toString, ctx.getIntSort)

    case Const._true => ctx.mkTrue
    case Const._false => ctx.mkFalse

    case Lit(n: Int) => ctx.mkInt(n)

    case Switch(n: Int) => ctx.mkBoolConst("Switch" + n)

    case MultiSwitch(n: Int) => ctx.mkConst("MultiSwitch" + n, ctx.getIntSort)

    case x: Id =>
      throw error.InvalidProgram("unresolved program variable", x)

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

    case Question(test, arg1, arg2) => ctx.mkITE(formula(test), translate(arg1), translate(arg2))

    case ForAll(bound, body) =>
      ctx.mkForall(bound.toArray map translate, translate(body), 0, scala.Array(), null, null, null)

    case Exists(bound, body) =>
      ctx.mkExists(bound.toArray map translate, translate(body), 0, scala.Array(), null, null, null)

      // array index
    case VarAccess(name, index) => ctx.mkSelect(ctx.mkArrayConst(name.toString, ctx.getIntSort, ctx.getIntSort), translate(index))

    case _ =>
      throw error.InvalidProgram("cannot translate to SMT", prop)
  }


}