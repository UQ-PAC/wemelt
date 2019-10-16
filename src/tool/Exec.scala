package tool

import java.beans.Expression

sealed trait Cont {
  def st: State
}

object Cont {
  case class next(st: State) extends Cont
  case class break(st: State) extends Cont
  case class cont(st: State) extends Cont
  case class ret(result: Expression, st: State) extends Cont
}



object Exec {
  // fix this
  def execute(statements: List[Statement], state: State): Cont = statements match {
    case Nil =>
      Cont.next(state)
    case stmt :: rest =>
      execute(stmt, state) match {
        case Cont.next(st) => execute(rest, st)
        case Cont.ret(ret, st) => Cont.ret(ret, st)
      }

  }

  def execute (statement: Statement, state0: State): Cont = statement match {
    case Malformed =>
      throw error.InvalidProgram("parser")

    case Atomic(expr) =>
      val (_, state1) = rval(expr, state0)
      Cont.next(state1.resetReadWrite())


    case block: Block =>
      // println("blocks currently leak local definitions!")
      execute(block.statements, state0)

    case VarDef(typ, id, None) =>
      //val state1 = state0 define id
      Cont.next(state0)

    case VarDef(typ, id, Some(init)) =>
      val (_init, st1) = rval(init, state0)
      // id has been WRITTEN
      val st2 = st1.updateWritten(id)
      val st3 = st2 define (id, _init)
      val st4 = st3.updateGammaAssign(id, _init)
      val st5 = st4.updateDAssign(id, _init)
      Cont.next(st5.resetReadWrite())

    case Continue =>
      Cont.cont(state0)

    case Break =>
      Cont.break(state0)

    case Return(None) =>
      Cont.ret(Lit("void"), state0)

    case Return(Some(expr)) =>
      val (_expr, st1) = rval(expr, state0)
      Cont.ret(_expr, st1)

    case Fence =>
      // reset D
      val state1 = state0.updateDFence()
      Cont.next(state1)

    case If(test, left, None) =>
      // IF rule
      val (_test, state1) = rval(test, state0)

      // check test is LOW
      val PRestrict = state1.restrictP(state1.knownW()) // calculate P_b
      if (!state1.security(_test, PRestrict)) {
        throw error.SecurityError("IF rule not valid for if(" + test + ") then {" + left + "} as guard expression is HIGH")
      }

      // execute both sides of if statement
      val _left = execute(left, state1)
      val _left1 = _left.st.updatePIfLeft(_test)
      // right hand side is empty
      val _right1 = state1.updatePIfRight(_test)

      // merge states
      val merged = _left1.mergeIf(_right1)
      Cont.next(merged)


    case If(test, left, Some(right)) =>
      // IF rule
      val (_test, state1) = rval(test, state0)

      // check test is LOW
      val PRestrict = state1.restrictP(state1.knownW()) // calculate P_b
      if (!state1.security(_test, PRestrict)) {
        throw error.SecurityError("IF rule not valid for if(" + test + ") then {" + left + "} else {" + right + "} as guard expression is HIGH")
      }

      // execute both sides of if statement
      val _left = execute(left, state1)
      val _left1 = _left.st.updatePIfLeft(_test)
      val _right = execute(right, state1)
      val _right1 = _right.st.updatePIfRight(_test)

      // merge states
      val merged = _left1.mergeIf(_right1)
      Cont.next(merged)


    /*
  case If(test, left, None) =>
    val _test_st = rval_low_test(test, st0)

    val _left = for (
      (_test, st0) <- _test_st;
      cont <- post(left, st0 and truth(_test))
    ) yield cont

    val _right = for (
      (_test, st0) <- _test_st
    ) yield Cont.next(st0 and !truth(_test))

    _left ++ _right

  case If(test, left, Some(right)) =>
    val _test_st = rval_low_test(test, st0)

    val _left = for (
      (_test, st0) <- _test_st;
      cont <- post(left, st0 and truth(_test))
    ) yield cont

    val _right = for (
      (_test, st0) <- _test_st;
      cont <- post(right, st0 and !truth(_test))
    ) yield cont

    _left ++ _right

  case While(test, spec, body) =>
    val invs = spec collect { case Invariant(assrt) => assrt }
    val inv = Assert.and(invs)
    val mod = Syntax.modifies(body)
    */
      /*
    case FunDef(ret, id, params, body) =>
      val st1 = state0 copy (funs = state0.funs + (id -> (ret, params, body)))
      List(Cont.next(st1))

       */
  }

  def rval(expr: Expression, st0: State): (Expression, State) = expr match {
    case id: Id =>
      // value has been READ
      //val _res = st0 lookup id
      val st1 = st0.updateRead(id)
      (id, st1)

    case res: Lit =>
      (res, st0)

    case BinOp("=", lhs, rhs) =>
      val (_rhs, st1) = assign(lhs, rhs, st0)
      (_rhs, st1)


      // need to change this to use proper data structure
    case BinOp("==", arg1, arg2) =>
      val (List(_arg1, _arg2), st1) = rvals(List(arg1, arg2), st0)
      (App(Fun("=="), List(_arg1, _arg2)), st1)

    case BinOp("!=", arg1, arg2) =>
      val (List(_arg1, _arg2), st1) = rvals(List(arg1, arg2), st0)
      (!App(Fun("=="), List(_arg1, _arg2)), st1)

    case PreOp("!", arg) =>
      val (_arg, st1) = rval(arg, st0)
      (!_arg, st1)

    case BinOp("+", arg1, arg2) =>
      val (_args, st1) = rvals(List(arg1, arg2), st0)
      (App(Fun("+"), _args), st1)

    case BinOp("-", arg1, arg2) =>
      val (_args, st1) = rvals(List(arg1, arg2), st0)
      (App(Fun("-"), _args), st1)

    case BinOp("*", arg1, arg2) =>
      val (_args, st1) = rvals(List(arg1, arg2), st0)
      (App(Fun("*"), _args), st1)

    case BinOp("/", arg1, arg2) =>
      val (_args, st1) = rvals(List(arg1, arg2), st0)
      (App(Fun("/"), _args), st1)

    case BinOp("%", arg1, arg2) =>
      val (_args, st1) = rvals(List(arg1, arg2), st0)
      (App(Fun("%"), _args), st1)

    case BinOp("<=", arg1, arg2) =>
      val (_args, st1) = rvals(List(arg1, arg2), st0)
      (App(Fun("<="), _args), st1)

    case BinOp("<", arg1, arg2) =>
      val (_args, st1) = rvals(List(arg1, arg2), st0)
      (App(Fun("<"), _args), st1)

    case BinOp(">=", arg1, arg2) =>
      val (_args, st1) = rvals(List(arg1, arg2), st0)
      (App(Fun(">="), _args), st1)

    case BinOp(">", arg1, arg2) =>
      val (_args, st1) = rvals(List(arg1, arg2), st0)
      (App(Fun(">"), _args), st1)

      /*
    // don't fork if the rhs has no side effects
    case BinOp("||", arg1, arg2) if !Syntax.hasEffects(arg2) =>
      for (
        (_arg1, st1) <- rval_low_test(arg1, st0);
        (_arg2, st2) <- rval(arg2, st1)
      ) yield (App(Fun("||"), List(_arg1, _arg2)), st2)

    case BinOp("&&", arg1, arg2) if !Syntax.hasEffects(arg2) =>
      for (
        (_arg1, st1) <- rval_low_test(arg1, st0);
        (_arg2, st2) <- rval(arg2, st1)
      ) yield (App(Fun("&&"), List(_arg1, _arg2)), st2)

    // shortcut evaluation yields two states
    case BinOp("||", arg1, arg2) =>
      val _arg1_st = rval_low_test(arg1, st0)

      val _true = for (
        (_arg1, st1) <- _arg1_st
      ) yield (Const._true, st1 and _arg1)

      val _false = for (
        (_arg1, st1) <- _arg1_st;
        (_arg2, st2) <- rval(arg2, st1 and !_arg1)
      ) yield (_arg2, st2)

      _true ++ _false

    // shortcut evaluation yields two states
    case BinOp("&&", arg1, arg2) =>
      val _arg1_st = rval_low_test(arg1, st0)

      val _false = for (
        (_arg1, st1) <- _arg1_st
      ) yield (Const._false, st1 and !_arg1)

      val _true = for (
        (_arg1, st1) <- _arg1_st;
        (_arg2, st2) <- rval(arg2, st1 and _arg1)
      ) yield (_arg2, st2)

      _false ++ _true

       */

  }

  def write(id: Id, rhs: Expression, st: State): State = {
    // loc has been WRITTEN
    st assign (id, rhs)
  }

  // return tuple contains the new value and the associated state
  def assign(lhs: Expression, rhs: Expression, st0: State): (Expression, State) = {
    val (_rhs, st1) = rval(rhs, st0)
    val (_lhs, st2) = lval(lhs, st1)
    val st3 = st2.updateWritten(_lhs)
    // at this point the rd and wr sets are complete for the current instruction

    // calculate P_x:=e
    val PRestrict = st3.restrictP(st3.knownW())


    // check if LHS is a control variable
    val st4 = if (st3.controls.contains(_lhs)) {
      // ASSIGNC rule
      // check _rhs is LOW
      val t = st3.security(_rhs, PRestrict)
      if (!t) {
        throw error.SecurityError("ASSIGNC rule not valid for " + _lhs + " = " + _rhs + " as HIGH expression assigned to control variable")
      }

      // secure_update
      val PPrime = st3.assign(_lhs, _rhs) // calculate PPrime - this is an awkward way to get it but will do for now

      val falling = for (i <- st3.controlledBy(_lhs) if (!st3.lowP(i)) && !PPrime.highP(i))
        yield i
      val rising = for (i <- st3.controlledBy(_lhs) if (!st3.highP(i)) && !PPrime.lowP(i))
        yield i

      for (y <- falling -- st3.noReadWrite) {
        if (!st3.knownW().contains(y) || !st3.security(_rhs, PPrime.P)) {
          throw error.SecurityError("ASSIGNC rule not valid for " + _lhs + " = " + _rhs + " as secure update fails for falling set")
        }
      }

      for (y <- rising) {
        if (!st3.knownW().contains(y)) {
          throw error.SecurityError("ASSIGNC rule not valid for " + _lhs + " = " + _rhs + " as secure update fails for rising set")
        }
      }

      // no need to update gamma in ASSIGNC
      st3
    } else {
      // ASSIGN rule
      // if x's mode is not NoRW, ensure that e's security level is not higher than x's security level, given P_x:=e
      if (!st3.noReadWrite.contains(_lhs)) {
        val t = st3.security(_rhs, PRestrict)
        val xSecurity = !st3.highP(_lhs) // combining evalP and highP idk if this will be confusing
        if (!t && xSecurity) {
          throw error.SecurityError("ASSIGN rule not valid for " + _lhs + " = " + _rhs + " as HIGH expression assigned to LOW variable")
        }
      }

      st3.updateGammaAssign(_lhs, _rhs)
    }

    val st6 = st4.assign(_lhs, _rhs) // this is currently where P is updated
    val st7 = st6.updateDAssign(_lhs, _rhs)

    (_rhs, st7.resetReadWrite())
  }

  // check lvalue is a variable
  def lval(expr: Expression, st0: State): (Id, State) = {
    case id: Id =>
      (id, st0)

    case _ =>
      throw error.InvalidProgram("not lvalue", expr)
  }

  // evaluate multiple rvalues
  def rvals(exprs: List[Expression], pre: State): (List[Expression], State) = exprs match {
    case Nil =>
      (Nil, pre)

    case expr :: rest => // XXX: right-to-left, should be parallel
      val (xs, st) = rvals(rest, pre)
      val (x, post) = rval(expr, st)
      (x :: xs, post)
  }

  def convertToCNF(props: List[Expression]): List[Expression] = {
    for (p <- props) p match {
      case BinOp("&&", arg1, arg2) =>
        List(arg1, arg2) // fix this
      case BinOp("||", arg1, arg2) =>
        // need to recursively build list of each side
      case PreOp("!", arg) =>
        convertNot(arg)

      case p: _ =>
        p
    }
  }


  // https://www.cs.jhu.edu/~jason/tutorials/convert-to-CNF.html
  def convertToCNF(prop: Expression): Expression = prop match {
    case BinOp("&&", arg1, arg2) =>
      BinOp("&&", convertToCNF(arg1), convertToCNF(arg2))

    case BinOp("||", arg1, arg2) =>
      convertToCNF()
    case PreOp("!", arg) =>
      convertNot(arg)

    case p: _ =>
      p

  }

  def convertNot(prop: Expression): Expression = prop match {
    case BinOp("&&", arg1, arg2) =>
      convertToCNF(BinOp("||", PreOp("!", arg1), PreOp("!", arg2)))

    case BinOp("||", arg1, arg2) =>
      convertToCNF(BinOp("&&", PreOp("!", arg1), PreOp("!", arg2)))

    case PreOp("!", arg) =>
      convertToCNF(arg)

    case p: _ =>
      p
  }

}
