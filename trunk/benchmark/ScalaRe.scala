import scalare.regex.pderiv.PDeriv._;

object ScalaRe {
  def main(args:Array[String]) = {
    val usPat = {
      val pSpace = PVar (-1, List(), PRE(Label(' ')))
      val p1 = PVar (1,List(), PRE(Star(dot)))
      val p2 = PVar (2,List(), PRE(Pair(char,char)))
      val p3 = PVar (3,List(), PRE(repeatPair(digit)(5)))
      val p4 = PVar (4,List(), PRE(Choice(Empty, Pair(Label('-'), repeatPair(digit)(4)))))
      PPair(p1,PPair(pSpace,PPair(p2,PPair(pSpace, PPair(p3,p4)))))
    }
    val cp = compilePat(usPat)
    val lines = scala.io.Source.fromFile(args(0), "utf-8").getLines
    while (lines.hasNext) {
      println(compiledGreedyPatMatch(cp)(lines.next()))
      /*
      val result = compiledGreedyPatMatch(cp)(lines.next())
      println(result)
      result match {
	case Some(_) => println("matched.")
	case None    => println("not matched.")
      }
      */
    }
  }
}
