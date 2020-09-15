package wemelt

import com.microsoft.z3
import com.microsoft.z3.{BitVecExpr, Params, Solver}

object SMT {
  val intSize = 32 // size of bitvectors used
  val cfg = new java.util.HashMap[String, String]()
  val ctx = new z3.Context(cfg)
  val solver: Solver = ctx.mkSolver()

  def prove(cond: Expression, given: Predicate, debug: Boolean): Boolean = {
    if (debug)
      println("smt checking !(" + cond + ") given " + given)
    solver.push()
    solver.add(convertPredicate(given))
    // check that (NOT cond) AND P is unsatisfiable
    solver.add(formula(PreOp("!", cond)))
    val res = solver.check
    solver.pop()

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
    solver.add(convertPredicate(given))
    // check that cond AND P is satisfiable
    solver.add(formula(cond))
    val res =solver.check
    solver.pop()

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
    solver.add(convertPredicate(given))
    val res = solver.check
    solver.pop()

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
    solver.add(ctx.mkNot(PToAnd(given)))
    val res = solver.check
    solver.pop()

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
    solver.add(ctx.mkNot(PToOr(given)))
    val res = solver.check
    solver.pop()

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
    solver.add(ctx.mkNot(ctx.mkImplies(convertPredicate(strong), convertPredicate(weak))))
    val res = solver.check
    solver.pop()
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
    // check that (NOT cond) is unsatisfiable
    solver.add(ctx.mkNot(formula(cond)))
    val res = solver.check
    solver.pop()

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

  def bitwiseSameSize(lhs: z3.BitVecExpr, rhs: z3.BitVecExpr): (z3.BitVecExpr, z3.BitVecExpr) = {
    val lhSize = lhs.getSortSize
    val rhSize = rhs.getSortSize
    println("lhs: " + lhs + " size: " + lhSize)
    println("rhs: " + rhs + " size: " + rhSize)
    if (lhSize > rhSize) {
      val rhExt = ctx.mkSignExt(lhSize - rhSize, rhs)
      println("extsize: " + rhExt.getSortSize)
      (lhs, rhExt)
    } else if (rhSize > lhSize) {
      val lhExt = ctx.mkSignExt(rhSize - lhSize, lhs)
      println("extsize: " + lhExt.getSortSize)
      (lhExt, rhs)
    } else {
      (lhs, rhs)
    }
  }

  /* currently doing all arithmetic operations on ints - may want to switch to bitvectors
   and bitwise arithmetic operations for better simulation of the assembly semantics if this ends up being important
  https://z3prover.github.io/api/html/classcom_1_1microsoft_1_1z3_1_1_context.html */
  def translate(prop: Expression): z3.Expr = prop match {
    case x: Var => ctx.mkBVConst(x.toString, x.size)

    case Const._true => ctx.mkTrue
    case Const._false => ctx.mkFalse

    case Lit(n: Int) => ctx.mkBV(n, 32)

    case Switch(n: Int) => ctx.mkBoolConst("Switch" + n)

    case MultiSwitch(n: Int) => ctx.mkConst("MultiSwitch" + n, ctx.getIntSort)

    case BinOp("==", arg1, arg2) =>
      val lhs = translate(arg1)
      val rhs = translate(arg2)
      lhs match {
        case bv: BitVecExpr =>
          rhs match {
            case bv2: BitVecExpr =>
              val (_lhs, _rhs) = bitwiseSameSize(bv, bv2)
              try {
                ctx.mkEq(_lhs, _rhs)
              } catch {
                case e: Throwable =>
                throw error.ProgramError("== type error lhs: " + lhs + "( " + lhs.getSort + ") rhs: " + rhs + "( " + rhs.getSort + ")")
              }
            case _ =>
              // error due to nonmatching types
              throw error.ProgramError("== type error lhs: " + lhs + "( " + lhs.getSort + ") rhs: " + rhs + "( " + rhs.getSort + ")")
          }
        case _ =>
          ctx.mkEq(lhs, rhs)
      }

    case PreOp("!", arg) => ctx.mkNot(formula(arg))
    case BinOp("&&", arg1, arg2) => ctx.mkAnd(formula(arg1), formula(arg2))
    case BinOp("||", arg1, arg2) => ctx.mkOr(formula(arg1), formula(arg2))
    case BinOp("==>", arg1, arg2) => ctx.mkImplies(formula(arg1), formula(arg2))

    case PreOp("-", arg) => ctx.mkBVNeg(bitwise(arg))
    case BinOp("+", arg1, arg2) =>
      val (_arg1, _arg2) = bitwiseSameSize(bitwise(arg1), bitwise(arg2))
      ctx.mkBVAdd(_arg1, _arg2)
    case BinOp("-", arg1, arg2) =>
      val (_arg1, _arg2) = bitwiseSameSize(bitwise(arg1), bitwise(arg2))
      ctx.mkBVSub(_arg1, _arg2)
    case BinOp("*", arg1, arg2) =>
      val (_arg1, _arg2) = bitwiseSameSize(bitwise(arg1), bitwise(arg2))
      ctx.mkBVMul(_arg1, _arg2)
    case BinOp("/", arg1, arg2) =>
      val (_arg1, _arg2) = bitwiseSameSize(bitwise(arg1), bitwise(arg2))
      ctx.mkBVUDiv(_arg1, _arg2)
    case BinOp("%", arg1, arg2) =>
      val (_arg1, _arg2) = bitwiseSameSize(bitwise(arg1), bitwise(arg2))
      ctx.mkBVURem(_arg1, _arg2)

    case BinOp("<=", arg1, arg2) =>
      val (_arg1, _arg2) = bitwiseSameSize(bitwise(arg1), bitwise(arg2))
      ctx.mkBVULE(_arg1, _arg2)
    case BinOp("<", arg1, arg2) =>
      val (_arg1, _arg2) = bitwiseSameSize(bitwise(arg1), bitwise(arg2))
      ctx.mkBVULT(_arg1, _arg2)
    case BinOp(">=", arg1, arg2) =>
      val (_arg1, _arg2) = bitwiseSameSize(bitwise(arg1), bitwise(arg2))
      ctx.mkBVUGE(_arg1, _arg2)
    case BinOp(">", arg1, arg2) =>
      val (_arg1, _arg2) = bitwiseSameSize(bitwise(arg1), bitwise(arg2))
      ctx.mkBVUGT(_arg1, _arg2)

    case BinOp("|", arg1, arg2) =>
      val (_arg1, _arg2) = bitwiseSameSize(bitwise(arg1), bitwise(arg2))
      ctx.mkBVOR(_arg1, _arg2)
    case BinOp("&", arg1, arg2) =>
      val (_arg1, _arg2) = bitwiseSameSize(bitwise(arg1), bitwise(arg2))
      ctx.mkBVAND(_arg1, _arg2)
    case BinOp("^", arg1, arg2) =>
      val (_arg1, _arg2) = bitwiseSameSize(bitwise(arg1), bitwise(arg2))
      ctx.mkBVXOR(_arg1, _arg2)
    case PreOp("~", arg) => ctx.mkBVNot(bitwise(arg))

      // defining normal right shift as logical shift right
    case BinOp(">>", arg1, arg2) =>
      val (_arg1, _arg2) = bitwiseSameSize(bitwise(arg1), bitwise(arg2))
      ctx.mkBVLSHR(bitwise(arg1), bitwise(arg2))
    case BinOp(">>>", arg1, arg2) =>
      val (_arg1, _arg2) = bitwiseSameSize(bitwise(arg1), bitwise(arg2))
      ctx.mkBVASHR(bitwise(arg1), bitwise(arg2))
    case BinOp("<<", arg1, arg2) =>
      val (_arg1, _arg2) = bitwiseSameSize(bitwise(arg1), bitwise(arg2))
      ctx.mkBVSHL(bitwise(arg1), bitwise(arg2))

    case IfThenElse(test, arg1, arg2) => ctx.mkITE(formula(test), translate(arg1), translate(arg2))

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
      val bv = bitwise(arg2)
      val size = bv.getSortSize
      ctx.mkSignExt(arg1 - size, bv)

    case ExtUnsigned(arg1, arg2) =>
      val bv = bitwise(arg2)
      val size = bv.getSortSize
      ctx.mkZeroExt(arg1 - size, bv)

      // array index
      // to fix!!!
    case Access(index, size, freshIndex) =>
        val array = ctx.mkArrayConst("mem" __ freshIndex, ctx.mkBitVecSort(64), ctx.mkBitVecSort(size))
        val bv = bitwise(index)
        val bvSize = bv.getSortSize
        val ext = ctx.mkSignExt(64 - bvSize, bv)
        val test = ctx.mkSelect(array, ext)
        test

    case _ =>
      throw error.InvalidProgram("cannot translate to SMT", prop)
  }


}