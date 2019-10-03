package tool

import java.io.FileReader
import collection.JavaConverters._

object Tool {
  def main(args: Array[String]): Unit = {
    if (args.isEmpty) {

    } else {
      for (file <- args) {
          Console.out.println(file)
          parse(file)
      }
    }

  }

  def parse(file: String) /* List[Statement] */ = {
    val reader = new FileReader(file)
    val scanner = new Scanner(reader)
    val parser = new Parser()

    //val pure = new java.util.HashSet[String]
   // scanner.pure = pure

    val result = parser.parse(scanner)

    //result
    val globals: List[Statement] = result.asInstanceOf[java.util.ArrayList[Statement]].asScala.toList
    println(globals)
    globals

  }
}
