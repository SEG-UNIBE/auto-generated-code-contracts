package tictactoe;
import java.io.*;

/**
 * Interface for TicTacToe and Gomoku.
 * @author $Author: oscar $
 * @version $Id: BoardGame.java 16460 2008-02-27 14:01:17Z oscar $
 */
public interface BoardGame {
	public void update() throws IOException;
	public void move(char col, char row, char mark);
	public Player currentPlayer(); // NB: new method
	public Player winner();
	public boolean notOver();
	public int squaresLeft();
}

