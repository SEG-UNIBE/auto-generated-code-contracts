import java.util.*;



import java.io.*;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.net.MalformedURLException;
import java.net.URL;
import java.nio.file.FileVisitResult;
import java.nio.file.FileVisitor;
import java.nio.file.attribute.BasicFileAttributes;

/**
* The scanner compiles a list of the most frequent compilation error Strings, reported by OpenJML. 
* It scans a file line-wise and counts how often each error occurs.
* @author anonymous
*/
public class CompilationAnalysisScanner {

	public static final String PROTECTED_IN_PUBLIC_E = "An identifier with protected visibility may not be used in a ensures clause with public visibility";
	public static final String PROTECTED_IN_PUBLIC_R = "An identifier with protected visibility may not be used in a requires clause with public visibility";
    	public static final String MISSING_SEMICOLON = "perhaps a missing semicolon";
	
	public static final String CANNOT_FIND_SYMBOL = "cannot find symbol";
    	public static final String RESULT_USED_IN_VOID_METHOD = "result expression may not be used in the specification of a method that returns void";
	public static final String UNKNOWN_BACKSLASH = "This backslash token is unknown:";
    
	public static final String ILLEGAL_START_OF_EXPRESSION =    "error: illegal start of ";
	public static final String SOMECHARACTER_EXPECTED = "expected";
	public static final String UNEXPECTED_JML_TOKEN = "Unexpected or misspelled JML token";
	
	public static final String KEYWORD_MISUSE    = "is a keyword, and may not be used as an identifier";
	public static final String EMPTY_CHARACTER_LITERAL    = "error: empty character literal";
	public static final String UNCLOSED_STRING_LITERAL = "unclosed string literal";
	public static final String UNCLOSED_EXPR = "The informal expression is not closed";
	
	public static final String INCORRECTLY_FORMED = "Incorrectly formed or terminated "; //requires or ensures statement
	public static final String TRANSITIVE_ERROR_FROM_IMPROPER_CLOSING = "class, interface, enum, or record expected";
	public static final String SEMICOLON_TOSEPARATE = "Expected a semicolon to separate the parts of a JML quantified expression"; 
	    

	public static void main(String[] args) throws FileNotFoundException {

		if (args.length <= 0){
	      	      	System.out.println( "please specify the path of the project that should be analysed relative from to where this file is executed as argument");
	          	return;
		}
		long lineCT = 0;

		long visibilityViolationProtected = 0;
		long semicolonError = 0;
		long symbolNotFound = 0;

	        long resultUsedInVoidMethod = 0;
	        long unknownBackslash = 0;
	        long illegalStartOfExpression = 0;
	        
	        long doubleColonExpected = 0; 
	        long unexpectedJMLToken = 0;
	        long keywordMisuse = 0;
	        
	        long emptyCharacterLiteral = 0;
	        long unclosedExpr = 0;
	        long unclosedStringLiteral = 0;
	        long incorrectlyFormedStatement = 0; // e.g., @requires requires
	
	        long errorFromImproperClosing = 0; // e.g., missing ')'


		File file = new File(args[0]);
		Scanner in = new Scanner(file);
		String res = "";

		while (in.hasNextLine()) {
			res = in.nextLine();
			lineCT ++;				
			if (res.contains(PROTECTED_IN_PUBLIC_E) || res.contains(PROTECTED_IN_PUBLIC_R))
                    		visibilityViolationProtected++;
	                else if (res.contains(CANNOT_FIND_SYMBOL))
	                    symbolNotFound++;
	                else if (res.contains(MISSING_SEMICOLON))
	                    semicolonError++;
	
	                else if (res.contains(RESULT_USED_IN_VOID_METHOD))
	                    resultUsedInVoidMethod++;
	                else if (res.contains(UNKNOWN_BACKSLASH))
	                    unknownBackslash++;
	                else if (res.contains(ILLEGAL_START_OF_EXPRESSION))
	                    illegalStartOfExpression++;
	
	                else if (res.contains(UNEXPECTED_JML_TOKEN))
	                    unexpectedJMLToken++;
	                else if (res.contains("error:") && res.endsWith("expected"))
	                    doubleColonExpected++;
	                else if (res.contains(KEYWORD_MISUSE))
	                    keywordMisuse++;
	
	                else if (res.contains(EMPTY_CHARACTER_LITERAL))
	                    emptyCharacterLiteral++;
	                else if (res.contains(UNCLOSED_EXPR))
	                    unclosedExpr++;
	                else if (res.contains(UNCLOSED_STRING_LITERAL))
	                    unclosedStringLiteral++;
	                else if (res.contains(INCORRECTLY_FORMED))
	                    incorrectlyFormedStatement++;
	                else if (res.contains(TRANSITIVE_ERROR_FROM_IMPROPER_CLOSING))
	                    errorFromImproperClosing++;
                }

		in.close();
            	long summary =  visibilityViolationProtected +
                            + symbolNotFound
                            + resultUsedInVoidMethod
                            
                            + semicolonError 
                            + unknownBackslash 
                            + illegalStartOfExpression
                            
                            + doubleColonExpected 
                            + unexpectedJMLToken
                            + keywordMisuse
                            
                            + emptyCharacterLiteral
                            + unclosedExpr
                            + unclosedStringLiteral
                            + incorrectlyFormedStatement
                            + errorFromImproperClosing;

		System.out.println("--------------------------------------------");
	    	System.out.println("I could classify " + summary + " of 242 errors in " + lineCT + " analyzed lines.");
	    	System.out.println("--------------------------------------------\n");
	
		System.out.println("Number of semicolon missing: \t" + semicolonError);
		System.out.println("Number of visibilityViolations: " + visibilityViolationProtected);
		System.out.println("Number of result used in void: " + resultUsedInVoidMethod);
		
	        System.out.println("Number of unkown backslash: \t" + unknownBackslash);
		System.out.println("Number of symbol not found: \t" + symbolNotFound);
		System.out.println("Number of illegal start of expr or type: " + illegalStartOfExpression);

	        System.out.println("Number of unexpected JML token: " + unexpectedJMLToken);
	        System.out.println("Number of some character missing/expected: " + doubleColonExpected);
	        System.out.println("Number of keyword misuse: " + keywordMisuse);
	
	        System.out.println("Number of empty character literal: " + emptyCharacterLiteral);
	        System.out.println("Number of unclose expressions: " + unclosedExpr);
	        System.out.println("Number of unclose incorrectlyFormedStatements: " + incorrectlyFormedStatement);
	
	        System.out.println("Number of unclosed String: " + unclosedStringLiteral);
	}

	public static List<String> extractFilesFromPath(String path) {
		List<String> mvFiles = new LinkedList<String>();
		// get multi-variant source files
		FileIterator<Path> fiMV = new FileIterator<Path>();
		try {
			Files.walkFileTree(Paths.get(path), fiMV);
	        } catch (IOException e) {
			e.printStackTrace();
		}
		// store the java-files
		for (Path srcFile : fiMV.getRegFiles()) {
			String fileName = srcFile.getFileName().toString();
			if (fileName.lastIndexOf(".") > -1 && fileName.substring(fileName.lastIndexOf(".")).equals(".java")) {
				mvFiles.add(srcFile.toString());
			}
		}
		return mvFiles;
	}

	static class FileIterator<Path> implements FileVisitor<Path> {
        	private List<Path> regFiles = new LinkedList<Path>();

	        @Override
	        public FileVisitResult preVisitDirectory(Path dir, BasicFileAttributes attrs) throws IOException {
	                return FileVisitResult.CONTINUE;
	        }
	
	        @Override
	        public FileVisitResult visitFile(Path file, BasicFileAttributes attr) throws IOException {
	            if (attr.isSymbolicLink()) {
	                    System.out.format("Symbolic link: %s ", file);
	                } else if (attr.isRegularFile()) {
	                    regFiles.add(file);
	                } else {
	                    System.out.format("Other: %s ", file);
	                }
	                System.out.println("(" + attr.size() + "bytes)");
	
	                return FileVisitResult.CONTINUE;
	
	        }
	        public List<Path> getRegFiles() {
	            return regFiles;
	        }

	        public URL[] getFileURIs() {
	            URL[] list = new URL[regFiles.size()];
	            for (int i = 0; i < regFiles.size(); i++) {
	                Path p = regFiles.get(i);
	                try {
	                    list[i] = new URL(p.toString());
	                } catch (MalformedURLException e) {
	                    e.printStackTrace();
	                }
	            }
	
	            return list;
	        }
	
	        @Override
	        public FileVisitResult visitFileFailed(Path file, IOException exc) throws IOException {
	            return FileVisitResult.CONTINUE;
	        }
	        @Override
	        public FileVisitResult postVisitDirectory(Path dir, IOException exc) throws IOException {
	            return FileVisitResult.CONTINUE;
	        }
    	}
}
