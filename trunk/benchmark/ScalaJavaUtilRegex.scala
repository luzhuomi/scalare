import java.util.regex.Matcher
import java.util.regex.Pattern


object ScalaJavaUtilRegex {
  def main(args:Array[String]) = {
    val pattern = Pattern.compile("(.*) ([A-Za-z]{2}) ([0-9]{5})(-[0-9]{4})?")
    // val _ = readLine()
    val lines = scala.io.Source.fromFile(args(0), "utf-8").getLines
    while (lines.hasNext) {
      val matcher = pattern.matcher(lines.next())
      if (matcher.find()) {
	val count = matcher.groupCount()
	var s  = ""
	var i = 1
	while (i <= count) 
	{
	  s += "(" + i + ":" + matcher.group(i) +")"
	  i += 1
	}
	println(s)
      } else {
	println("not matched.")
      }
    }
  }
}
