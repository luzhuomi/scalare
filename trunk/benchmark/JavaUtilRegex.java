import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.io.*;

public class JavaUtilRegex {
    public static final String EXAMPLE_TEST = "This is my small example string which I'm going to use for pattern matching.";

    public static void main(String[] args) {
	Pattern pattern = Pattern.compile("(.*) ([A-Za-z]{2}) ([0-9]{5})(-[0-9]{4})?");

	try {
	    FileInputStream fis = new FileInputStream(args[0]);
	    DataInputStream in = new DataInputStream(fis);
	    BufferedReader br = new BufferedReader(new InputStreamReader(in));
	    String strLine;

	    while ((strLine = br.readLine()) != null) {
		try {
		    Matcher matcher = pattern.matcher(strLine);
		    // Matcher matcher = pattern.matcher("Mountain View CA 90410");
		    if (matcher.find()) {
			System.out.println(matcher.group());
			// System.out.println("matched");
		    } else {
			System.out.println("not matched.");
		    }
		} catch (IllegalStateException e) {
		    System.out.println("not matched.");
		}
	    }
	} catch (FileNotFoundException e) {
	    // TODO Auto-generated catch block
	    e.printStackTrace();
	} catch (IOException e) {
	    // TODO Auto-generated catch block
	    e.printStackTrace();
	}	
    }
} 