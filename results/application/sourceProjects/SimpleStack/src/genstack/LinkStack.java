package genstack;

/**
 * This Stack implementation uses a linked list of Cells.<p>
 * <i>NB:</i> LinkStack is <i>not</i> thread safe!
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
	
	public boolean isEmpty() { return this.size() == 0; }
	public int size() { return size; }
	
	/**
	 * Links a new Cell to the head of the list
	 * pointed to by top.
	 */
	public void push(E item) {
		top = new Cell(item, top);
		size++;
		assert !this.isEmpty();
		assert this.top() == item;
		assert invariant();
	}
	
	public E top() {
		assert !this.isEmpty();
		return top.item;
	}
	
	/**
	 * Unlinks the head Cell and sets top to
	 * point to the tail of the list.
	 */
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
	protected boolean invariant() {
		return (size >= 0) &&
		((size == 0 && this.top == null)
				|| (size > 0 && this.top != null));
	}
	
}