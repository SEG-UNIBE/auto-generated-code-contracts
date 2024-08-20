package tictactoe;
import java.io.IOException;
import java.io.OutputStream;

/**
 * Needed for silent testing. We will instantiate a
 * silent PrintStream by instantiating:
 * 		new PrintStream(new NullOutputStream())
 * in TicTacToeTest ...
 */
public class NullOutputStream extends OutputStream {

	public NullOutputStream() {
		super();
	}

	/**
	 * Null implementation of inherited abstract method
	 */
//S_I //@ requires b >= 0;
	public void write(int b) throws IOException { }
}
