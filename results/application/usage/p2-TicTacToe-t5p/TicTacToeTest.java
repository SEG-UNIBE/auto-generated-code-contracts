package tictactoe;
import static org.junit.Assert.*;

import java.io.PrintStream;
import org.junit.Before;
import org.junit.Test;

/**
 * Test cases for TicTacToe.
 * @author $Author: oscar $
 * @version $Id: TicTacToeTest.java 16511 2008-02-28 10:24:28Z oscar $
 */
public class TicTacToeTest {
	protected TicTacToe game;

//@ ensures game!= null;
	@Before public void setUp() throws Exception {
		game = new TicTacToe(new Player('X'), new Player('O'));
	}
	
	/**
	 * Test the getters and setters.
	 */
//@ requires game!= null;
	@Test public void testState() {
		assertEquals(game.get('a','1'), ' ');
		assertEquals(game.get('c','3'), ' ');
		game.set('c','3','X');
		assertEquals(game.get('c','3'), 'X');
		game.set('c','3',' ');
		assertEquals(game.get('c','3'), ' ');
		assertFalse(game.inRange('d','4'));
	}
	
//@ requires a1!= null && a1.length == 10;
//@ requires b1!= null && b1.length == 10;
//@ requires \nonnullelements(a1, b1);
	@Test public void testXWinDiagonal() {
		checkGame("a1\nb2\nc3\n", "b1\nc1\n", "X", 4);
	}

//@ requires gameOver(0);
	@Test public void testNoWinner() {
		checkGame("b2\na1\nb3\na2\nc1\n",
				"a3\nc3\nb1\nc2\n", "nobody",0);
	}
	
//@ requires a1!= null && a1.length == 10;
//@ requires b2!= null && b2.length == 30;
//@ requires \nonnullelements(a1, b2);
	@Test public void testOWinReverseDiagonal() {
		checkGame("a1\nb1\n"
				+ "a1\nb1\nb2\nc1\nd0\nxxx\n\n" // invalid moves
				+ "a2\n",
				"b2\nc1\na3\n", "O", 3);
	}
	
//@ requires b2!= null && b1!= null && b3!= null;
//@ requires a1!= null && a0!= null && a3!= null;
	@Test public void testXWinCentreColumn() {
		checkGame("b2\nb1\nb3\n",
				"a1\n"
				+ "b1\nA0\n" // invalid moves
				+ "a3\n", "X", 4);
	}
	
//@ requires b2!= null && a3!= null && nb3!= null;
	@Test public void testOWinTopRow() {
		checkGame("b2\na1\nc1\n",
				"a3\nc3\nb3\n", "O", 3);
	}
	
	/**
	 * Run a game with simulated input for X and Y, and check that
	 * the winner is as expected.
	 * Game results are sent to a NullOutputStream.
	 */
//@ requires Xmoves!= null && Omoves!= null;
//@ requires winner!= null;
//@ requires squaresLeft > 0;
//@ ensures GameDriver.isGameOpen(game) == true;
	public void checkGame(String Xmoves, String Omoves, String winner, int squaresLeft) {
		Player X = new Player('X', Xmoves);
		Player O = new Player('O', Omoves);
		TicTacToe game = new TicTacToe(X, O);
		GameDriver.playGame(game, new PrintStream(new NullOutputStream()));
		assertEquals(winner, game.winner().name());
		assertEquals(squaresLeft, game.squaresLeft());
	}
}
