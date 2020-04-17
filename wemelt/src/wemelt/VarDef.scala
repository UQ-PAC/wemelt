package wemelt

// highest level parsed data structure
case class Parsed(variables: Set[Definition], rely: List[Expression], guarantee: List[Expression],P_0: Option[List[Expression]], gamma_0: Option[List[GammaMapping]], statements: List[Statement]) extends beaver.Symbol {
  def this(variables: Array[Definition], rely: Array[Expression], guarantee: Array[Expression], P_0: Array[Expression], gamma_0: Array[GammaMapping], statements: Array[Statement]) = this(variables.toSet, rely.toList, guarantee.toList, Some(P_0.toList), Some(gamma_0.toList), statements.toList)
  def this(variables: Array[Definition], rely: Array[Expression], guarantee: Array[Expression], P_0: Array[Expression], statements: Array[Statement]) = this(variables.toSet, rely.toList, guarantee.toList, Some(P_0.toList), None, statements.toList)
  def this(variables: Array[Definition], rely: Array[Expression], guarantee: Array[Expression], gamma_0: Array[GammaMapping], statements: Array[Statement]) = this(variables.toSet, rely.toList, guarantee.toList, None, Some(gamma_0.toList), statements.toList)
  def this(variables: Array[Definition], rely: Array[Expression], guarantee: Array[Expression], statements: Array[Statement]) = this(variables.toSet, rely.toList, guarantee.toList, None, None, statements.toList)
}

sealed trait Security extends beaver.Symbol {
  def >(security: Security): Boolean
  def <(security: Security): Boolean
  def >=(security: Security): Boolean
  def <=(security: Security): Boolean
}
case object High extends Security {
  def instance = this
  def >(security: Security): Boolean = if (security == Low) { true } else { false }
  def <(security: Security): Boolean = false
  def >=(security: Security): Boolean = true
  def <=(security: Security): Boolean = if (security == Low) { false } else { true }
}
case object Low extends Security {
  def instance = this
  def >(security: Security): Boolean = false
  def <(security: Security): Boolean = if (security == High) { true } else { false }
  def >=(security: Security): Boolean = if (security == High) { false } else { true }
  def <=(security: Security): Boolean = true
}

case class GammaMapping(variable: Id, security: Security) extends beaver.Symbol {
  def this(variable: Id, index: Int, security: Security) = this(Id(variable.name + "[" + index + "]"), security)
  def this(variable: String, security: Security) = this(Id(variable), security)

  /*
  def toPair(arrays: Map[Id, IdArray] ): Seq[(Id, Security)] = this match {
    // array wildcard case
    case g if arrays.keySet.contains(g.variable) =>
      for (i <- arrays(g.variable).array)
        yield i -> g.security
    case g =>
      Seq(g.variable -> g.security)
  } */

}

sealed trait Definition extends beaver.Symbol

case class LocalVarDef(name: Id) extends Definition {
  def this(name: String) = this(Id(name))
}

case class GlobalVarDef(name: Id, lpredr: Expression, lpredg: Expression, local: Boolean) extends Definition {
  def this(name: String, lpred: Expression, local: Boolean) = this(Id(name), lpred, lpred, local)
  def this(name: String, lpredr: Expression, lpredg: Expression, local: Boolean) = this(Id(name), lpredr, lpredg, local)
}

/*
case class ArrayDef(name: Id, size: Int, preds: IndexedSeq[Expression], mode: Mode) extends Definition {
  def this(name: String, size: Int, lpred: Expression, mode: Mode) = this(Id(name), size, ArrayDef.predArray(size, lpred), mode)
  def this(name: String, size: Int, lpreds: Array[Expression], mode: Mode) = this(Id(name), size, lpreds.toIndexedSeq, mode)
  def this(name: String, size: Int, mode: Mode) = this(Id(name), size, ArrayDef.predArray(size, Const._true), mode)
  def this(name: String, size: Int, lpred: Expression) = this(Id(name), size, ArrayDef.predArray(size, lpred), Reg)
  def this(name: String, size: Int, lpreds: Array[Expression]) = this(Id(name), size, lpreds.toIndexedSeq, Reg)
  def this(name: String, size: Int) = this(Id(name), size, ArrayDef.predArray(size, Const._true), Reg)

  def toVarDefs: Set[VarDef] = {
    for (i <- 0 until size)
      yield VarDef(Id(name.toString.arrayIndex(i)), preds(i), mode)
  }.toSet
}

object ArrayDef {
  def predArray(size: Int, lpred: Expression): IndexedSeq[Expression] = {
    for (i <- 0 until size)
      yield lpred
  }
}

case class IdArray(name: Id, array: IndexedSeq[Id])

object IdArray {
  def apply(name: Id, size: Int): IdArray = {
    val array = for (i <- 0 until size)
      yield Id(name.toString.arrayIndex(i))
    this(name, array)
  }
}
*/

