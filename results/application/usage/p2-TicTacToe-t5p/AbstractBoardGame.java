package tictactoe;
import java.io.IOException;


/**
 * AbstractBoardGame implements common methods to
 * TicTacToe and Gomoku.
 * For now, this class holds everything that used to be
 * in TicTacToe.  Next, we will refactor this to hold
 * only generic features for both TicTacToe and Gomoku.
 * In fact, there are no abstract methods for the moment.
 * 
 * @author $Author: oscar $
 * @version $Id: AbstractBoardGame.java 16603 2008-03-01 15:18:39Z oscar $
 */
public abstract class AbstractBoardGame implements BoardGame {
	static final int X = 0;
	static final int O = 1;

	protected char[][] gameState;	
	protected Player winner = new Player(); // nobody
	protected Player[] player;
	protected int turn = X; // initial turn
	protected int squaresLeft = 9;
	// hm ... should define a constant?

	/**
	 * The state of the game is represented as 3x3
	 * array of chars marked ' ', 'X', or 'O'.
	 * We index the state using chess notation,
	 * i.e., column is 'a' through 'c' and row is
	 * '1' through '3'.
	 */
	public AbstractBoardGame(Player playerX, Player playerO)
	{
		gameState = new char[3][3];
		for (char col='a'; col <='c'; col++)
			for (char row='1'; row<='3'; row++)
				this.set(col,row,' ');
		player = new Player[2];
		player[X] = playerX;
		player[O] = playerO;
	}

	/**
	 * set() and get() translate between chess coordinates
	 * and array indices.
	 * NB: Use package scope.
	 */
//@ requires gameState.containsKey(col) && gameState.containsKey(row);
//@ ensures mark == gameState[col-'a'][row-'1'];
	void set(char col, char row, char mark) {
		assert inRange(col, row);
		gameState[col-'a'][row-'1'] = mark;
	}
	
//@ requires col >= 0 && col <= gameState.length;
//@ requires row >= 0 && row <= gameState.length;
//@ ensures (\forall int i; 0 <= i && i < gameState.length; \result == gameState[i][col]);
//@ ensures (\forall int i; 0 <= i && i < gameState.length; \result == gameState[i][row]);
	char get(char col, char row) {
		assert inRange(col, row);
		return gameState[col-'a'][row-'1'];
	}
	
	/**
	 * The game is not over as long as there is no winner
	 * and somebody can still make a move ...
	 */
//@ ensures \result == (this.squaresLeft() > 0);
	public boolean notOver() {
		return this.winner().isNobody()
		&& this.squaresLeft() > 0;
	}
	
	/**
	 * A plain ascii representation of the game,
	 * mainly for debugging purposes.
	 */
//@ ensures \result!= null;
	public String toString() {
		StringBuffer rep = new StringBuffer();
		
		for (char row='3'; row>='1'; row--) {
			rep.append(row);
			rep.append("  ");
			for (char col='a'; col <='c'; col++) {
				rep.append(this.get(col,row));
				if (col<'c') {
					rep.append(" | ");
				}
			}
			rep.append('\n');
			if (row>'1') {
				rep.append("  ---+---+---\n");
			}
		}
		rep.append("   a   b   c\n");
		return(rep.toString());
	}
	
	/**
	 * Needed for getter and setter preconditions.
	 * Reports true if coordinates are valid.
	 */
//@ ensures \result == (('a'<=col) && (col<='c')
//@ ensures \result == (('1'<=row) && (row<='3'));
	boolean inRange(char col, char row) {
		return (('a'<=col) && (col<='c')
				&& ('1'<=row) && (row<='3'));
	}
	
	/**
	 * Called by the current player during an update().
	 * The player attempts to put a mark at a location.
	 */
//@ requires col >= 0 && col < this.width() && row >= 0 && row < this.height();
	public void move(char col, char row, char mark)
	{
		assert this.notOver();
		assert inRange(col, row);
		assert this.get(col, row) == ' ';
		this.set(col, row, mark);
		this.squaresLeft--;
		this.swapTurn();
		this.checkWinner();
		assert this.invariant();
	}
	
	/**
	 * Ask the current player to make a move.
	 */
//@ requires turn >= 0;
	public void update() throws IOException {
		this.player[turn].move(this);
	}

//@ requires turn >= 0;
//@ requires player!= null;
	public Player currentPlayer() {
		return player[turn];
	}

//@ ensures \result == this.winner;
	public Player winner() {
		return this.winner;
	}
	
//@ requires this.squaresLeft > 0;
	public int squaresLeft() {
		return this.squaresLeft;
	}
	
//@ requires turn!= O;
	protected void swapTurn() {
		turn = (turn == X) ? O : X;
	}
	
	/**
	 * Check for a winning row, column or diagonal.
	 * (This code smells!  How can we clean it up?)
	 */
//@ requires this.valid();
//@ ensures this.valid();
	protected void checkWinner()
	{
		char player;
		for (char row='3'; row>='1'; row--) {
			player = this.get('a',row);
			if (player == this.get('b',row)
					&& player == this.get('c',row)) {
				this.setWinner(player);
				return;
			}
		}
		for (char col='a'; col <='c'; col++) {
			player = this.get(col,'1');
			if (player == this.get(col,'2')
					&& player == this.get(col,'3')) {
				this.setWinner(player);
				return;
			}
		}
		player = this.get('b','2');
		if (player == this.get('a','1')
				&& player == this.get('c','3')) {
			this.setWinner(player);
			return;
		}
		if (player == this.get('a','3')
				&& player == this.get('c','1')) {
			this.setWinner(player);
			return;
		}
	}
	
	/**
	 * Look up which player is the winner, and set winner
	 * accordingly. Hm. Maybe we should store Players
	 * instead of chars in our array!
	 */
//@ requires player.length > 0;
//@ ensures this.winner == player[X].winner;
	protected void setWinner(char aPlayer) {
		if (aPlayer == ' ')
			return;
		if (aPlayer == player[X].mark())
			winner = player[X];
		else
			winner = player[O];
	}
	
	/**
	 * These seem obvious, which is exactly why
	 * they should be checked.
	 */
//@ ensures \result == (turn == X || turn == O);
	protected boolean invariant() {
		return (turn == X || turn == O)
			&& (this.notOver() 
				|| this.winner() == player[X]
				|| this.winner() == player[O]
				|| this.winner().isNobody())
			&& (squaresLeft < 9
				// else, initially:
				|| turn == X && this.winner().isNobody());
	}
}
