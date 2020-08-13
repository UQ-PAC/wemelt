package wemelt

import com.microsoft.z3
import com.microsoft.z3.Solver
import com.microsoft.z3.Params

object SMT {
  val intSize = 32 // size of bitvectors used
  val cfg = new java.util.HashMap[String, String]()
  val ctx = new z3.Context(cfg)
  val solver: Solver = ctx.mkSolver()

  def prove(cond: Expression, given: Predicate, debug: Boolean): Boolean = {
    if (debug)
      println("smt checking !(" + cond + ") given " + given)
    solver.push()
    val res = try {
      solver.add(convertPredicate(given))
      // check that (NOT cond) AND P is unsatisfiable
      solver.add(formula(PreOp("!", cond)))
      solver.check
    } catch {
      case e: java.lang.UnsatisfiedLinkError if e.getMessage.equals("com.microsoft.z3.Native.INTERNALgetErrorMsgEx(JI)Ljava/lang/String;")=>
        // weird unintuitive error z3 can have when an input type is incorrect in a way it doesn't check
        throw error.Z3Error("Z3 failed", cond, given, "incorrect z3 expression type, probably involving ForAll/Exists")
      case e: Throwable =>
        throw error.Z3Error("Z3 failed", cond, given, e)
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

  def proveSat(cond: Expression, given: Predicate, debug: Boolean): Boolean = {
    if (debug)
      println("smt checking " + cond + " given " + given)
    solver.push()
    val res = try {
      solver.add(convertPredicate(given))
      // check that cond AND P is satisfiable
      solver.add(formula(cond))

      solver.check
    } catch {
      case e: java.lang.UnsatisfiedLinkError if e.getMessage.equals("com.microsoft.z3.Native.INTERNALgetErrorMsgEx(JI)Ljava/lang/String;")=>
        // weird unintuitive error z3 can have when an input type is incorrect in a way it doesn't check
        throw error.Z3Error("Z3 failed", cond, given, "incorrect z3 expression type, probably involving ForAll/Exists")
      case e: Throwable =>
        throw error.Z3Error("Z3 failed", cond, given, e)
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

  def proveP(given: Predicate, debug: Boolean): Boolean = {
    if (debug)
      println("smt checking " + given)
    solver.push()
    val res = try {
      solver.add(convertPredicate(given))
      solver.check
    } catch {
      case e: java.lang.UnsatisfiedLinkError if e.getMessage.equals("com.microsoft.z3.Native.INTERNALgetErrorMsgEx(JI)Ljava/lang/String;")=>
        // weird unintuitive error z3 can have when an input type is incorrect in a way it doesn't check
        throw error.Z3Error("Z3 failed", given, "incorrect z3 expression type, probably involving ForAll/Exists")
      case e: Throwable =>
        throw error.Z3Error("Z3 failed", given, e)
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

  def proveListAnd(given: List[Expression], debug: Boolean): Boolean = {
    if (debug)
      println("smt checking !(" + given + ")")
    solver.push()
    val res = try {
      solver.add(ctx.mkNot(PToAnd(given)))
      solver.check
    } catch {
      case e: java.lang.UnsatisfiedLinkError if e.getMessage.equals("com.microsoft.z3.Native.INTERNALgetErrorMsgEx(JI)Ljava/lang/String;")=>
        // weird unintuitive error z3 can have when an input type is incorrect in a way it doesn't check
        throw error.Z3Error("Z3 failed", given, "incorrect z3 expression type, probably involving ForAll/Exists")
      case e: Throwable =>
        throw error.Z3Error("Z3 failed", given, e)
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

  def proveListOr(given: List[Expression], debug: Boolean): Boolean = {
    if (debug)
      println("smt checking !(" + given.OrStr + ")")
    solver.push()
    val res = try {
      solver.add(ctx.mkNot(PToOr(given)))
      solver.check
    } catch {
      case e: java.lang.UnsatisfiedLinkError if e.getMessage.equals("com.microsoft.z3.Native.INTERNALgetErrorMsgEx(JI)Ljava/lang/String;")=>
        // weird unintuitive error z3 can have when an input type is incorrect in a way it doesn't check
        throw error.Z3Error("Z3 failed", given.OrStr, "incorrect z3 expression type, probably involving ForAll/Exists")
      case e: Throwable =>
        throw error.Z3Error("Z3 failed", given.OrStr, e)
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

  def proveImplies(strong: Predicate, weak: Predicate, debug: Boolean): Boolean = {
    if (debug)
      println("smt checking !(" + strong + newline + "==> " + newline + weak + ")")
    solver.push()
    val res = try {
      solver.add(ctx.mkNot(ctx.mkImplies(convertPredicate(strong), convertPredicate(weak))))
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

  def proveImplies(strong: Predicate, weak: Expression, debug: Boolean): Boolean = proveImplies(strong, Predicate(List(weak)), debug)

  def proveImplies(strong: Predicate, weak: List[Expression], debug: Boolean): Boolean = proveImplies(strong, Predicate(weak), debug)

  def proveExpression(cond: Expression, debug: Boolean): Boolean = {
    if (debug)
      println("smt checking !(" + cond + ")")
    solver.push()
    val res = try {
      // check that (NOT cond) is unsatisfiable
      solver.add(ctx.mkNot(formula(cond)))
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
    res == z3.Status.UNSATISFIABLE
  }

  def convertPredicate(P: Predicate): z3.BoolExpr = {
    if (P.exists.isEmpty && P.forall.isEmpty) {
      PToAnd(P.predicates)
    } else if (P.exists.isEmpty) {
      ctx.mkForall(P.forall.toArray map translate, PToAnd(P.predicates), 0, scala.Array(), null, null, null)
    } else if (P.forall.isEmpty) {
      ctx.mkExists(P.exists.toArray map translate, PToAnd(P.predicates), 0, scala.Array(), null, null, null)
    } else {
      ctx.mkForall(P.forall.toArray map translate, ctx.mkExists(P.exists.toArray map translate, PToAnd(P.predicates), 0, scala.Array(), null, null, null), 0, scala.Array(), null, null, null)
    }
  }

  // recursively convert expression list into AND structure
  def PToAnd(exprs: List[Expression]): z3.BoolExpr = {
    if (exprs.size == 1) {
      formula(exprs.head)
    } else {
      exprs match {
        case Nil =>
          ctx.mkTrue

        case expr :: rest =>
          val xs = PToAnd(rest)
          val x = ctx.mkAnd(formula(expr), xs)
          x
      }
    }
  }

  // OR all expressions in list
  def PToOr(exprs: List[Expression]): z3.BoolExpr = {
    if (exprs.size == 1) {
      formula(exprs.head)
    } else {
      exprs match {
        case Nil =>
          ctx.mkFalse

        case expr :: rest =>
          val xs = PToOr(rest)
          val x = ctx.mkOr(formula(expr), xs)
          x
      }
    }
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
    case x: Var => ctx.mkBVConst(x.name, x.size)

    case Const._true => ctx.mkTrue
    case Const._false => ctx.mkFalse

    case Lit(n: Int) => ctx.mkBV(n, 32)

    case Switch(n: Int) => ctx.mkBoolConst("Switch" + n)

    case MultiSwitch(n: Int) => ctx.mkConst("MultiSwitch" + n, ctx.getIntSort)

    case BinOp("==", arg1, arg2) => ctx.mkEq(translate(arg1), translate(arg2))

    case PreOp("!", arg) => ctx.mkNot(formula(arg))
    case BinOp("&&", arg1, arg2) => ctx.mkAnd(formula(arg1), formula(arg2))
    case BinOp("||", arg1, arg2) => ctx.mkOr(formula(arg1), formula(arg2))
    case BinOp("==>", arg1, arg2) => ctx.mkImplies(formula(arg1), formula(arg2))

    case PreOp("-", arg) => ctx.mkBVNeg(bitwise(arg))
    case BinOp("+", arg1, arg2) => ctx.mkBVAdd(bitwise(arg1), bitwise(arg2))
    case BinOp("-", arg1, arg2) => ctx.mkBVSub(bitwise(arg1), bitwise(arg2))
    case BinOp("*", arg1, arg2) => ctx.mkBVMul(bitwise(arg1), bitwise(arg2))
    case BinOp("/", arg1, arg2) => ctx.mkBVUDiv(bitwise(arg1), bitwise(arg2))
    case BinOp("%", arg1, arg2) => ctx.mkBVURem(bitwise(arg1), bitwise(arg2))

    case BinOp("<=", arg1, arg2) => ctx.mkBVULE(bitwise(arg1), bitwise(arg2))
    case BinOp("<", arg1, arg2) => ctx.mkBVULT(bitwise(arg1), bitwise(arg2))
    case BinOp(">=", arg1, arg2) => ctx.mkBVUGE(bitwise(arg1), bitwise(arg2))
    case BinOp(">", arg1, arg2) => ctx.mkBVUGT(bitwise(arg1), bitwise(arg2))

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

    case ExtHigh(arg1, arg2) =>
      val bv = bitwise(arg2)
      val size = bv.getSortSize
      ctx.mkExtract(size - 1, size - arg1, bv)

    case ExtLow(arg1, arg2) =>
      ctx.mkExtract(arg1, 0, bitwise(arg2))

    case ExtSigned(arg1, arg2) =>
      ctx.mkSignExt(arg1, bitwise(arg2))

    case ExtUnsigned(arg1, arg2) =>
      ctx.mkZeroExt(arg1, bitwise(arg2))

      // array index
    //case VarAccess(name, index) => ctx.mkSelect(ctx.mkArrayConst(name.toString, ctx.getIntSort, ctx.getIntSort), translate(index))

    case _ =>
      throw error.InvalidProgram("cannot translate to SMT", prop)
  }


}