package tictactoe;
import java.io.*;

/**
 * Interface for TicTacToe and Gomoku.
 */
public interface BoardGame {
	public void update() throws IOException;
	public void move(char col, char row, char mark);
	public Player currentPlayer(); // NB: new method
	public Player winner();
	public boolean notOver();
	public int squaresLeft();
}

