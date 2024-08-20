package tictactoe;
import java.io.IOException;
import java.io.PrintStream;

/**
 * Driver for TicTacToe.
 * @author $Author: oscar $
 * @version $Id: GameDriver.java 16460 2008-02-27 14:01:17Z oscar $
 */

public class GameDriver {
//@ requires true;
//@ ensures true;
	public static void main(String args[]) {
		Player X = new Player('X');
		Player O = new Player('O');
		playGame(new TicTacToe(X, O));
	}
	
//@ requires game!= null;
//@ requires System.out!= null;
	public static void playGame(BoardGame game) {
		playGame(game, System.out);
	}
	
//@ requires out!= null;
	public static void playGame(BoardGame game, PrintStream out) {
		try {
			do {
				out.println();
				out.println(game);
				out.print("Player "
					+ game.currentPlayer().mark() + " moves: ");
				try {
					game.update();
				} catch (AssertionError err) {
					out.println("Invalid move!");
				}
			} while(game.notOver());
			out.print(game);
			out.println("game over -- " + game.winner().name() + " wins!");
		} catch (IOException err) {
			out.println("game terminated!");
		}
	}
}