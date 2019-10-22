package tool

import java.io.FileReader
import collection.JavaConverters._

object Tool {

  def main(args: Array[String]): Unit = {
    if (args.isEmpty) {

    } else {
      for (file <- args) {
        Console.out.println(file)
        val (statements, variables) = parse(file)
        val state0: State = State.init(variables)
        Exec.execute(statements, state0)
      }
    }
  }

  def parse(file: String): (List[Statement], Set[Variable]) = {
    val reader = new FileReader(file)
    val scanner = new Scanner(reader)
    val parser = new Parser()

    val variables = new java.util.HashSet[Variable]
    parser.variables = variables

    val result = parser.parse(scanner)

    //result
    val globals: List[Statement] = result.asInstanceOf[java.util.ArrayList[Statement]].asScala.toList

    val variables2: Set[Variable] = variables.asInstanceOf[java.util.HashSet[Variable]].asScala.toSet
    println(globals)
    println(variables2)
    (globals, variables2)
  }



}
