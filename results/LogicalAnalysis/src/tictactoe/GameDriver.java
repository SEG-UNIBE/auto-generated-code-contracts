package tictactoe;
import java.io.IOException;
import java.io.PrintStream;

/**
 * Driver for TicTacToe.
 */
public class GameDriver {
//E //@ requires true;
//E //@ ensures true;
	public static void main(String args[]) {
		Player X = new Player('X');
		Player O = new Player('O');
		playGame(new TicTacToe(X, O));
	}
	
//S_V //@ requires game!= null;
//S_V //@ requires System.out!= null;
	public static void playGame(BoardGame game) {
		playGame(game, System.out);
	}
	
//S_V //@ requires out!= null;
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