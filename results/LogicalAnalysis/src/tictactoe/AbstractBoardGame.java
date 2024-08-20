package tictactoe;
import java.io.IOException;


/**
 * AbstractBoardGame implements common methods to
 * TicTacToe and Gomoku.
 * For now, this class holds everything that used to be
 * in TicTacToe.  Next, we will refactor this to hold
 * only generic features for both TicTacToe and Gomoku.
 * In fact, there are no abstract methods for the moment.
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
//E //@ requires gameState.containsKey(col) && gameState.containsKey(row);
//S_V //@ ensures mark == gameState[col-'a'][row-'1'];
	void set(char col, char row, char mark) {
		assert inRange(col, row);
		gameState[col-'a'][row-'1'] = mark;
	}
	
//U_I //@ requires col >= 0 && col <= gameState.length;
//E //@ requires row >= 0 && row <= gameState.length;
//S_I //@ ensures (\forall int i; 0 <= i && i < gameState.length; \result == gameState[i][col]);
//S_I //@ ensures (\forall int i; 0 <= i && i < gameState.length; \result == gameState[i][row]);
	char get(char col, char row) {
		assert inRange(col, row);
		return gameState[col-'a'][row-'1'];
	}
	
	/**
	 * The game is not over as long as there is no winner
	 * and somebody can still make a move ...
	 */
//S_V //@ ensures \result == (this.squaresLeft() > 0);
	public boolean notOver() {
		return this.winner().isNobody()
		&& this.squaresLeft() > 0;
	}
	
	/**
	 * A plain ascii representation of the game,
	 * mainly for debugging purposes.
	 */
//S_V //@ ensures \result!= null;
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
//S_V //@ ensures \result == (('a'<=col) && (col<='c')
//S_V //@ ensures \result == (('1'<=row) && (row<='3'));
	boolean inRange(char col, char row) {
		return (('a'<=col) && (col<='c')
				&& ('1'<=row) && (row<='3'));
	}
	
	/**
	 * Called by the current player during an update().
	 * The player attempts to put a mark at a location.
	 */
//U_I //@ requires col >= 0 && col < this.width() && row >= 0 && row < this.height();
//W
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
//S_V //@ requires turn >= 0;
	public void update() throws IOException {
		this.player[turn].move(this);
	}

//S_V //@ requires turn >= 0;
//S_V //@ requires player!= null;
	public Player currentPlayer() {
		return player[turn];
	}

//S_V //@ ensures \result == this.winner;
	public Player winner() {
		return this.winner;
	}
	
//S_I //@ requires this.squaresLeft > 0;
	public int squaresLeft() {
		return this.squaresLeft;
	}
	
//S_V //@ requires turn!= O;
	protected void swapTurn() {
		turn = (turn == X) ? O : X;
	}
	
	/**
	 * Check for a winning row, column or diagonal.
	 * (This code smells!  How can we clean it up?)
	 */
//U_I //@ requires this.valid();
//U_I //@ ensures this.valid();
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
//S_V //@ requires player.length > 0;
//S_I //@ ensures this.winner == player[X].winner;
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
//S_V //@ ensures \result == (turn == X || turn == O);
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
