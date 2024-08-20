package genstack;

/**
 * Generic version of StackInterface
 */
public interface StackInterface<E> {
	public boolean isEmpty();
	public int size();
	public void push(E item);
	public E top();
	public void pop();
}
