package tictactoe;
import java.io.IOException;
import java.io.OutputStream;

/**
 * Needed for silent testing. We will instantiate a
 * silent PrintStream by instantiating:
 * 		new PrintStream(new NullOutputStream())
 * in TicTacToeTest ...
 * @author $Author: oscar $
 * @version $Id: NullOutputStream.java 16460 2008-02-27 14:01:17Z oscar $
 */
public class NullOutputStream extends OutputStream {

	public NullOutputStream() {
		super();
	}

	/**
	 * Null implementation of inherited abstract method
	 */
//@ requires b >= 0;
	public void write(int b) throws IOException { }
}
