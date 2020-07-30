package wemelt

// highest level parsed data structure
case class Parsed(variables: Set[Definition], P_inv: List[Expression], P_0: Option[List[Expression]], gamma_0: Option[List[GammaMapping]], statements: List[Statement]) extends beaver.Symbol {
  def this(variables: Array[Definition], P_inv: Array[Expression],  P_0: Array[Expression], gamma_0: Array[GammaMapping], statements: Array[Statement]) = this(variables.toSet, P_inv.toList,  Some(P_0.toList), Some(gamma_0.toList), statements.toList)
  def this(variables: Array[Definition], P_inv: Array[Expression],  P_0: Array[Expression], statements: Array[Statement]) = this(variables.toSet, P_inv.toList, Some(P_0.toList), None, statements.toList)
  def this(variables: Array[Definition], P_inv: Array[Expression],  gamma_0: Array[GammaMapping], statements: Array[Statement]) = this(variables.toSet, P_inv.toList, None, Some(gamma_0.toList), statements.toList)
  def this(variables: Array[Definition], P_inv: Array[Expression],  statements: Array[Statement]) = this(variables.toSet, P_inv.toList, None, None, statements.toList)
}

case class GammaMapping(label: Id, security: Expression) extends beaver.Symbol {
  //def this(variable: Var, index: Int, security: Expression) = this(Var(variable.name + "[" + index + "]"), security)
  def this(name: String, security: Expression) = this(Id(name), security)
  /*
  def toPair(arrays: Map[Var, VarArray] ): Seq[(Var, Security)] = this match {
    // array wildcard case
    case g if arrays.keySet.contains(g.variable) =>
      for (i <- arrays(g.variable).array)
        yield i -> g.security
    case g =>
      Seq(g.variable -> g.security)
  } */
}

case class Relation(condition: Expression, relation: Expression) extends beaver.Symbol

sealed trait Definition extends beaver.Symbol

case class LocalVarDef(variable: Var) extends Definition {
  def this(name: String, size: Int) = this(Var(name, size))
}

case class GlobalVarDef(variable: Var, lpredr: Expression, lpredg: Expression, rvar: Option[List[Relation]], gvar: Option[List[Relation]]) extends Definition {
  def this(name: String, size: Int, lpred: Expression) = this(Var(name, size, None), lpred, lpred, None, None)
  def this(name: String, size: Int, lpredr: Expression, lpredg: Expression) = this(Var(name, size, None), lpredr, lpredg, None, None)
  def this(name: String, size: Int, lpred: Expression, rvar: Array[Relation]) = this(Var(name, size, None), lpred, lpred, Some(rvar.toList), None)
  def this(name: String, size: Int, lpredr: Expression, lpredg: Expression, rvar: Array[Relation]) = this(Var(name, size, None), lpredr, lpredg, Some(rvar.toList), None)
  def this(name: String, size: Int, lpred: Expression, rvar: Array[Relation], gvar: Array[Relation]) = this(Var(name, size, None), lpred, lpred, Some(rvar.toList), Some(gvar.toList))
  def this(name: String, size: Int, lpredr: Expression, lpredg: Expression, rvar: Array[Relation], gvar: Array[Relation]) = this(Var(name, size, None), lpredr, lpredg, Some(rvar.toList), Some(gvar.toList))
  def this(name: String, size: Int, gvar: Array[Relation], lpred: Expression) = this(Var(name, size, None), lpred, lpred, None, Some(gvar.toList))
  def this(name: String, size: Int, gvar: Array[Relation], lpredr: Expression, lpredg: Expression) = this(Var(name, size, None), lpredr, lpredg, None, Some(gvar.toList))
}

/*
case class ArrayDef(name: Var, size: Int, preds: IndexedSeq[Expression], mode: Mode) extends Definition {
  def this(name: String, size: Int, lpred: Expression, mode: Mode) = this(name, size, ArrayDef.predArray(size, lpred), mode)
  def this(name: String, size: Int, lpreds: Array[Expression], mode: Mode) = this(name, size, lpreds.toIndexedSeq, mode)
  def this(name: String, size: Int, mode: Mode) = this(name, size, ArrayDef.predArray(size, Const._true), mode)
  def this(name: String, size: Int, lpred: Expression) = this(name, size, ArrayDef.predArray(size, lpred), Reg)
  def this(name: String, size: Int, lpreds: Array[Expression]) = this(name, size, lpreds.toIndexedSeq, Reg)
  def this(name: String, size: Int) = this(name, size, ArrayDef.predArray(size, Const._true), Reg)

  def toVarDefs: Set[VarDef] = {
    for (i <- 0 until size)
      yield VarDef(Var(name.toString.arrayIndex(i)), preds(i), mode)
  }.toSet
}

object ArrayDef {
  def predArray(size: Int, lpred: Expression): IndexedSeq[Expression] = {
    for (i <- 0 until size)
      yield lpred
  }
}

case class VarArray(name: Var, array: IndexedSeq[Var])

object VarArray {
  def apply(name: Var, size: Int): VarArray = {
    val array = for (i <- 0 until size)
      yield Var(name.toString.arrayIndex(i))
    this(name, array)
  }
}
*/

