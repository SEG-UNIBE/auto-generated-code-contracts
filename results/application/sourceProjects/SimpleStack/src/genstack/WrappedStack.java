
package genstack;

import java.util.Stack;

/**
 * This class is an adaptor that delegates StackInterface
 * messages to a java.util.Stack instance.
 */
public class WrappedStack<E> implements StackInterface<E> {

	protected java.util.Stack<E> stack;
	
	public WrappedStack() {
		this(new Stack<E>());
	}
	
	public WrappedStack(Stack<E> stack) {
		this.stack = stack;
	}
	
	public void push(E item) {
		stack.push(item);
		assert this.top() == item;
		assert invariant();
	}
	
	public E top() {
		assert !this.isEmpty();
		return stack.peek();
	}
	
	public void pop() {
		assert !this.isEmpty();
		stack.pop();
		assert invariant();
	}
	
	protected boolean invariant() {
		return this.size() >= 0;
	}

	public boolean isEmpty() {
		return stack.empty();
	}

	public int size() {
		return stack.size();
	}
}
