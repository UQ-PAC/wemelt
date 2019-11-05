package tool

import java.io.FileReader
import collection.JavaConverters._

object Tool {

  def main(args: Array[String]): Unit = {
    if (args.isEmpty) {
      println("usage: ./armlogictool.sh file1 file2...")
    } else {
      for (file <- args) {
        try {
          println(file)
          val res = parse(file)
          val variables = res.variables
          val statements = res.statements
          val P_0 = res.P_0
          val gamma_0 = res.gamma_0
          println(statements)
          println(variables)
          println(P_0)
          println(gamma_0)
          val state0: State = State.init(variables, P_0, gamma_0)
          Exec.execute(statements, state0)
        } catch {
          case e: java.io.FileNotFoundException =>
            println("file does not exist")
        }
      }
    }
  }

  def parse(file: String): Global = {
    val reader = new FileReader(file)
    val scanner = new Scanner(reader)
    val parser = new Parser()

    val result = parser.parse(scanner).asInstanceOf[Global]

    result
  }



}
