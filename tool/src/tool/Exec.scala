package tool

sealed trait Cont {
  def st: State
}

object Cont {
  case class next(st: State) extends Cont
  /*
  case class break(st: State) extends Cont
  case class cont(st: State) extends Cont
  case class ret(result: Expression, st: State) extends Cont */
}



object Exec {

  def execute(statements: List[Statement], state: State): Cont = statements match {
    case Nil =>
      Cont.next(state)
    case stmt :: rest =>
      val st = execute(stmt, state).st
      execute(rest, st)
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

      /*
    case Continue =>
      Cont.cont(state0)

    case Break =>
      Cont.break(state0)

    case Return(None) =>
      Cont.ret(Lit("void"), state0)

    case Return(Some(expr)) =>
      val (_expr, st1) = rval(expr, state0)
      Cont.ret(_expr, st1)

       */

    case Assignment(lhs, rhs) =>
      println(lhs + " = " + rhs + ":")
      val (_rhs, st1) = rval(rhs, state0)
      val st2 = st1.updateWritten(lhs)
      // at this point the rd and wr sets are complete for the current instruction

      // check if LHS is a control variable
      val st3 = if (st2.controls.contains(lhs)) {
        assignCRule(lhs, _rhs, st2)
      } else {
        assignRule(lhs,_rhs, st2)
      }

      val st4 = st3.assign(lhs, _rhs) // update P
      val st5 = st4.updateDAssign(lhs, _rhs)

      println("gamma: " +  st5.gamma)
      println("P: " +  st5.P)
      println("D: " +  st5.D)
      Cont.next(st5.resetReadWrite())

    case Fence =>
      // reset D
      val state1 = state0.updateDFence()
      println("fence")
      println("gamma: " +  state1.gamma)
      println("P: " +  state1.P)
      println("D: " +  state1.D)
      Cont.next(state1)

    case If(test, left, None) =>
      println("If(" + "test" + ") then {" + left + "} :")
      // IF rule
      // evaluate test which updates D
      val (_test, state1) = rval(test, state0)

      // check test is LOW
      val PRestrict = state1.restrictP(state1.knownW()) // calculate P_b
      if (!state1.security(_test, PRestrict)) {
        throw error.SecurityError("IF rule not valid for " + statement + " as guard expression is HIGH")
      }

      // execute both sides of if statement
      val _left = state1.updatePIfLeft(_test)
      val _left1 = execute(left, _left).st
      // right hand side is empty
      val _right1 = state1.updatePIfRight(_test)

      // merge states
      val merged = _left1.mergeIf(_right1)
      println("gamma: " +  merged.gamma)
      println("P: " +  merged.P)
      println("D: " +  merged.D)
      Cont.next(merged)


    case If(test, left, Some(right)) =>
      // IF rule
      // evaluate test which updates D
      println("If(" + "test" + ") then {" + left + "} else { " + right + "} :")
      val (_test, state1) = rval(test, state0)

      // check test is LOW
      val PRestrict = state1.restrictP(state1.knownW()) // calculate P_b
      if (!state1.security(_test, PRestrict)) {
        throw error.SecurityError("IF rule not valid for "+ statement + " as guard expression is HIGH")
      }

      // execute both sides of if statement
      val _left = state1.updatePIfLeft(_test)
      val _left1 = execute(left, _left).st

      val _right = state1.updatePIfRight(_test)
      val _right1 = execute(right, _right).st

      println("merging if states:")
      // merge states
      val merged = _left1.mergeIf(_right1)
      println("gamma: " +  merged.gamma)
      println("P_L: " + _left1.P)
      println("P_R: " + _right1.P)
      println("P merged: " +  merged.P)
      println("D: " +  merged.D)
      Cont.next(merged)

    case While(test, invariants, gamma, body) =>
      // WHILE rule

      // replace Ids in invariant with vars
      val idToVar: Subst = {
        for (v <- state0.variables)
          yield v -> v.toVar
      }.toMap

      val PPrime = invariants map {i => i.subst(idToVar)}

      // convert gammaPrime to map instead of list
      val gammaPrime: Map[Id, Security] = {
        for (g <- gamma) yield {
          g match {
            case BinOp("==", arg1: Id, Const.low) =>
              arg1 -> true
            case BinOp("==", arg1: Id, Const.high) =>
              arg1 -> false
            case _ =>
              throw error.InvalidProgram(g + " is not a valid input to gamma")
          }
        }
        }.toMap

      println("while rule:")
      println("gamma':" + gammaPrime)
      println("P':" + PPrime)

      // P' only contains stable variables - tested
      val PPrimeVar: Set[Id] = (invariants flatMap {x => x.getVariables}).toSet
      for (i <- PPrimeVar) {
        if (!state0.stable.contains(i))
          throw error.SecurityError("WHILE rule not valid for " + statement + " as "  + i + " in invariant is not stable")
      }

      // check P' is weaker than previous P - tested
      if (!SMT.proveImplies(state0.P, PPrime)) {
        throw error.SecurityError("WHILE rule not valid for " + statement + " as provided P' " + PPrime + " is not weaker than P " + state0.P)
      }

      // gamma' has same domain as gamma - tested
      if (state0.gamma.keySet != gammaPrime.keySet) {
        throw error.InvalidProgram("input gamma " + gammaPrime + " for " + statement + " does not have same domain as gamma: " + state0.gamma)
      }

      // check gamma' is greater or equal than gamma for all x - tested
      for (g <- state0.gamma.keySet) {
        if (!state0.gamma(g) && gammaPrime(g)) {
          throw error.SecurityError("WHILE rule not valid for " + statement + " as gamma' " + gammaPrime + " is not greater than gamma + " + state0.gamma + " for " + g)
        }
      }
      val DFixed = DFixedPoint(test, body, state0)
      println("DFixed: " + DFixed)
      val DPrime = State.mergeD(state0.D, DFixed)
      println("D': " + DPrime)

      val state1 = state0.copy(P = PPrime, gamma = gammaPrime, D = DPrime)

      // check DPrime is subset of D - tested
      for (v <- state0.variables) {
        if (!((state1.W_r(v) subsetOf state0.W_r(v)) && (state1.W_w(v) subsetOf state0.W_w(v)) && (state1.R_r(v) subsetOf state0.R_r(v)) && (state1.R_w(v) subsetOf state0.R_w(v))))
          throw error.SecurityError("WHILE rule not valid for " + statement + " as D' " + state1.D + " is not a subset of D" + state0.D)
      }

      // evaluate test which updates D
      val (_test, state2) = rval(test, state1)

      // check test is LOW with regards to P', gamma' - tested
      if (!state2.security(_test, state2.P)) {
        throw error.SecurityError("WHILE rule not valid for "+ statement + " as guard expression is HIGH")
      }

      // add test to P
      val state3 = state2.updatePIfLeft(_test)

      // evaluate body
      val _body = execute(body, state3)
      val state4 = _body.st

      println("while rule:")
      println("gamma':" + gammaPrime)
      println("P':" + PPrime)

      println("gamma'':" + state4.gamma)
      println("P'':" + state4.P)

      // check D' is subset of D''
      for (v <- state0.variables) {
        if (!((state1.W_r(v) subsetOf state4.W_r(v)) && (state1.W_w(v) subsetOf state4.W_w(v)) && (state1.R_r(v) subsetOf state4.R_r(v)) && (state1.R_w(v) subsetOf state4.R_w(v))))
          throw error.SecurityError("WHILE rule not valid for " + statement + " as D' " + state1.D + " is not a subset of D" + state0.D)
      }

      // check gamma' is greater or equal than gamma'' for all x
      for (g <- gammaPrime.keySet) {
        if (!state4.gamma(g) && gammaPrime(g)) {
          throw error.SecurityError("WHILE rule not valid for " + statement + " as gamma' " + state4.gamma + " is not greater than gamma'' " + gammaPrime + " for " + g)
        }
      }

      // check P'' is stronger than P' - tested
      if (!SMT.proveImplies(state4.P, PPrime)) {
        throw error.SecurityError("WHILE rule not valid for " + statement + " as provided P' " + PPrime + " does not hold after loop body. P'': " + state3.P)
      }

      // state1 used here as do not keep gamma'', P'', D'' from after loop body execution
      // remove test from P'
      val state5 = state1.updatePIfRight(_test)
      Cont.next(state5)

    case _ =>
      throw error.InvalidProgram("unimplemented statement " + statement)

  }

  def DFixedPoint(test: Expression, body: Statement, state: State): Map[Id, (Set[Id], Set[Id], Set[Id], Set[Id])] = {
    var DFixed = false
    var st0 = state
    var DPrime: Map[Id, (Set[Id], Set[Id], Set[Id], Set[Id])] = Map()
    var dfixedloops = 0
    while (!DFixed) {
      dfixedloops = dfixedloops + 1
      val st1 = DFixedPoint(test, st0)
      val st2 = DFixedPoint(body, st1)

      // compare st2.D to st0.D
      val it = st0.variables.toIterator
      while (it.hasNext && !DFixed) {
        val v = it.next
        DFixed = (st0.W_r(v) == st2.W_r(v)) && (st0.W_w(v) == st2.W_w(v)) && (st0.R_r(v) == st2.R_r(v)) && (st0.R_w(v) == st2.R_w(v))
      }

      // if D has changed, repeat
      if (DFixed) {
        DPrime = st2.D
      } else {
        st0 = st2
      }
    }
    println("dfixed loops " + dfixedloops)
    DPrime
  }

  def DFixedPoint(statements: List[Statement], state: State): State = statements match {
    case Nil =>
      state
    case stmt :: rest =>
      val st = DFixedPoint(stmt, state)
      DFixedPoint(rest, st)
  }

  def DFixedPoint(statement: Statement, st0: State): State = statement match {
    case Malformed =>
      throw error.InvalidProgram("parser")

    case Atomic(expr) =>
      val st1 = DFixedPoint(expr, st0)
      st1.resetReadWrite()

    case block: Block =>
      DFixedPoint(block.statements, st0)

    case Assignment(lhs, rhs) =>
      val st1 = DFixedPoint(rhs, st0)
      val st2 = st1.updateWritten(lhs)
      st2.updateDAssign(lhs, rhs)

    case Fence =>
      // reset D
      st0.updateDFence()

    case If(test, left, None) =>
      // evaluate test which updates D
      val st1 = DFixedPoint(test, st0)

      // right branch is empty
      val _left = DFixedPoint(left, st1)
      st1.copy(D = _left.mergeD(st1))

    case If(test, left, Some(right)) =>
      // evaluate test which updates D
      val st1 = DFixedPoint(test, st0)

      val _left = DFixedPoint(left, st1)
      val _right = DFixedPoint(right, st1)
      st1.copy(D =_left.mergeD(_right))

    case While(test, invariants, gamma, body) =>
      st0.copy(D = DFixedPoint(test, body, st0))

    case _ =>
      throw error.InvalidProgram("unimplemented statement " + statement)
  }

  def DFixedPoint(expr: Expression, st0: State): State = expr match {
    case id: Id =>
      st0.updateRead(id)

    case res: Lit =>
      st0

    case res: Const =>
      st0

    case BinOp(_, arg1, arg2) =>
      val st1 = DFixedPoint(arg1, st0)
      DFixedPoint(arg2, st1)

    case PreOp(_, arg) =>
      DFixedPoint(arg, st0)

    case _ =>
      throw error.InvalidProgram("unimplemented expression " + expr)
  }

  def rval(expr: Expression, st0: State): (Expression, State) = expr match {
    case id: Id =>
      // value has been READ
      val st1 = st0.updateRead(id)
      (id.toVar, st1)

    case res: Lit =>
      (res, st0)

    case res: Const =>
      (res, st0)

    case BinOp("==", arg1, arg2) =>
      val (List(_arg1, _arg2), st1) = rvals(List(arg1, arg2), st0)
      (BinOp("==", _arg1, _arg2), st1)

    case BinOp("!=", arg1, arg2) =>
      val (List(_arg1, _arg2), st1) = rvals(List(arg1, arg2), st0)
      (PreOp("!", BinOp("==", _arg1, _arg2)), st1)

    case PreOp("!", arg) =>
      val (_arg, st1) = rval(arg, st0)
      (PreOp("!", _arg), st1)

    case PreOp("+", arg) =>
      rval(arg, st0)

    case PreOp("-", arg) =>
      val (_arg, st1) = rval(arg, st0)
      (PreOp("-", _arg), st1)

    case BinOp("+", arg1, arg2) =>
      val (List(_arg1, _arg2), st1) = rvals(List(arg1, arg2), st0)
      (BinOp("+", _arg1, _arg2), st1)

    case BinOp("-", arg1, arg2) =>
      val (List(_arg1, _arg2), st1) = rvals(List(arg1, arg2), st0)
      (BinOp("-", _arg1, _arg2), st1)

    case BinOp("*", arg1, arg2) =>
      val (List(_arg1, _arg2), st1) = rvals(List(arg1, arg2), st0)
      (BinOp("*", _arg1, _arg2), st1)

    case BinOp("/", arg1, arg2) =>
      val (List(_arg1, _arg2), st1) = rvals(List(arg1, arg2), st0)
      (BinOp("/", _arg1, _arg2), st1)

    case BinOp("%", arg1, arg2) =>
      val (List(_arg1, _arg2), st1) = rvals(List(arg1, arg2), st0)
      (BinOp("%", _arg1, _arg2), st1)

    case BinOp("<=", arg1, arg2) =>
      val (List(_arg1, _arg2), st1) = rvals(List(arg1, arg2), st0)
      (BinOp("<=", _arg1, _arg2), st1)

    case BinOp("<", arg1, arg2) =>
      val (List(_arg1, _arg2), st1) = rvals(List(arg1, arg2), st0)
      (BinOp("<", _arg1, _arg2), st1)

    case BinOp(">=", arg1, arg2) =>
      val (List(_arg1, _arg2), st1) = rvals(List(arg1, arg2), st0)
      (BinOp(">=", _arg1, _arg2), st1)

    case BinOp(">", arg1, arg2) =>
      val (List(_arg1, _arg2), st1) = rvals(List(arg1, arg2), st0)
      (BinOp(">", _arg1, _arg2), st1)

    case BinOp("||", arg1, arg2) =>
      val (List(_arg1, _arg2), st1) = rvals(List(arg1, arg2), st0)
      (BinOp("||", _arg1, _arg2), st1)

    case BinOp("&&", arg1, arg2) =>
      val (List(_arg1, _arg2), st1) = rvals(List(arg1, arg2), st0)
      (BinOp("&&", _arg1, _arg2), st1)

    case BinOp("|", arg1, arg2) =>
      val (List(_arg1, _arg2), st1) = rvals(List(arg1, arg2), st0)
      (BinOp("|", _arg1, _arg2), st1)

    case BinOp("&", arg1, arg2) =>
      val (List(_arg1, _arg2), st1) = rvals(List(arg1, arg2), st0)
      (BinOp("&", _arg1, _arg2), st1)

    case BinOp("^", arg1, arg2) =>
      val (List(_arg1, _arg2), st1) = rvals(List(arg1, arg2), st0)
      (BinOp("^", _arg1, _arg2), st1)

    case BinOp(">>", arg1, arg2) =>
      val (List(_arg1, _arg2), st1) = rvals(List(arg1, arg2), st0)
      (BinOp(">>", _arg1, _arg2), st1)

    case BinOp(">>>", arg1, arg2) =>
      val (List(_arg1, _arg2), st1) = rvals(List(arg1, arg2), st0)
      (BinOp(">>>", _arg1, _arg2), st1)

    case BinOp("<<", arg1, arg2) =>
      val (List(_arg1, _arg2), st1) = rvals(List(arg1, arg2), st0)
      (BinOp("<<", _arg1, _arg2), st1)

    case PreOp("~", arg) =>
      val (_arg, st1) = rval(arg, st0)
      (PreOp("~", _arg), st1)

    case _ =>
      throw error.InvalidProgram("unimplemented expression: " + expr)

  }

  def assignRule(lhs: Id, rhs: Expression, st0: State): State = {
    // ASSIGN rule
    println("ASSIGN applying")

    // calculate P_x:=e
    val PRestrict = st0.restrictP(st0.knownW())

    // if x's mode is not NoRW, ensure that e's security level is not higher than x's security level, given P_x:=e
    if (!st0.noReadWrite.contains(lhs)) {
      val t = st0.security(rhs, PRestrict)
      val xSecurity = !st0.highP(lhs, PRestrict) // this is equivalent to evalP
      if (!t && xSecurity) {
        throw error.SecurityError("ASSIGN rule not valid for " + lhs + " = " + rhs + " as HIGH expression assigned to LOW variable")
      }
    }
    st0.updateGammaAssign(lhs, rhs)
  }

  def assignCRule(lhs: Id, rhs: Expression, st0: State): State = {
    // ASSIGNC rule
    println("ASSIGNC applying")

    // calculate P_x:=e
    val PRestrict = st0.restrictP(st0.knownW())

    // check _rhs is LOW
    val t = st0.security(rhs, PRestrict)
    if (!t) {
      throw error.SecurityError("ASSIGNC rule not valid for " + lhs + " = " + rhs + " as HIGH expression assigned to control variable")
    }

    // secure_update
    val PPrime = st0.assign(lhs, rhs) // calculate PPrime
    val PPrimeRestrict = PPrime.restrictP(st0.knownW())

    val falling = for (i <- st0.controlledBy(lhs) if (!st0.lowP(i, PRestrict)) && !st0.highP(i, PPrimeRestrict))
      yield i

    println("falling: " + falling)
    println("knownW: " + st0.knownW)

    for (y <- falling -- st0.noReadWrite) {
      println("checking secureupdate falling for " + y)
      if (!st0.knownW().contains(y) || !st0.security(y, PRestrict)) {
        throw error.SecurityError("ASSIGNC rule not valid for " + lhs + " = " + rhs + " as secure update fails for falling set")
      }
    }

    val rising = for (i <- st0.controlledBy(lhs) if (!st0.highP(i, PRestrict)) && !st0.lowP(i, PPrimeRestrict))
      yield i

    println("rising: " + rising)

    for (y <- rising) {
      if (!st0.knownR().contains(y)) {
        throw error.SecurityError("ASSIGNC rule not valid for " + lhs + " = " + rhs + " as secure update fails for rising set")
      }
    }

    // no need to update gamma in ASSIGNC
    st0
  }

  // check lvalue is a variable
  def lval(expr: Expression, st0: State): (Id, State) = expr match {
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

}
