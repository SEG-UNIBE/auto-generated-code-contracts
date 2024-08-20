package p2.StackTest3;

/**
 * Generic version of StackInterface
 *
 * @author Oscar.Nierstrasz@acm.org
 * @version $Id: StackInterface.java 17003 2008-03-13 10:20:41Z oscar $
 */
public interface StackInterface<E> {
	public boolean isEmpty();
	public int size();
	public void push(E item);
	public E top();
	public void pop();
}
