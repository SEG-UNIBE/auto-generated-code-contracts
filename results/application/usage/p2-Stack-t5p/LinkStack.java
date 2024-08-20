package p2.StackTest3;

/**
 * This Stack implementation uses a linked list of Cells.<p>
 * <i>NB:</i> LinkStack is <i>not</i> thread safe!
 *
 * @author Oscar.Nierstrasz@acm.org
 * @version $Id: LinkStack.java 17003 2008-03-13 10:20:41Z oscar $
 */
public class LinkStack<E> implements StackInterface<E> {
	protected Cell top;
	protected int size;
	
	public LinkStack() {
		// Establishes the invariant.
		top = null;
		size = 0;
	}
	
	/**
	 * This inner class is just a glorified data structure
	 * to hold items and links to other cells.
	 */
	protected class Cell {
		E item;
		Cell next;
		Cell(E item, Cell next) {
			this.item = item;
			this.next = next;
		}
	}
	
//@ ensures \result <==> this.size() == 0;
	public boolean isEmpty() { return this.size() == 0; }
//@ ensures \result == size;
	public int size() { return size; }
	
	/**
	 * Links a new Cell to the head of the list
	 * pointed to by top.
	 */
//@ ensures!isEmpty();
	public void push(E item) {
		top = new Cell(item, top);
		size++;
		assert !this.isEmpty();
		assert this.top() == item;
		assert invariant();
	}
	
//@ ensures \result == top.item;
	public E top() {
		assert !this.isEmpty();
		return top.item;
	}
	
	/**
	 * Unlinks the head Cell and sets top to
	 * point to the tail of the list.
	 */
//@ requires top!= null;
//@ requires size > 0;
	public void pop() {
		assert !this.isEmpty();
		top = top.next;
		size--;
		assert invariant();
	}
	
	/**
	 * The invariant is established by the constructor, and
	 * must hold at the start <I>and</i> end of each method.
	 * (To keep things simple, we only check at the end of
	 * methods that modify the state.)
	 */
//@ ensures \result == (size >= 0);
	protected boolean invariant() {
		return (size >= 0) &&
		((size == 0 && this.top == null)
				|| (size > 0 && this.top != null));
	}
	
}