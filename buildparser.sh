jflex -nobak wemelt/src/wemelt/Scanner.flex
java -jar beaver.jar -t wemelt/src/wemelt/Parser.grammar
