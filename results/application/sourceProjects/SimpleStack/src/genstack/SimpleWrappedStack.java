
package genstack;

import java.util.Stack;

/**
 * This class is an adaptor that delegates StackInterface
 * messages to a java.util.Stack instance.
 * This version is broken because it does not check the contract.
 */
public class SimpleWrappedStack<E> implements StackInterface<E> {

	protected java.util.Stack<E> stack;
	
	public SimpleWrappedStack() {
		this(new Stack<E>());
	}
	
	public SimpleWrappedStack(Stack<E> stack) {
		this.stack = stack;
	}
	
	public void push(E item) {
		stack.push(item);
	}
	
	public E top() {
		return stack.peek();
	}
	
	public void pop() {
		stack.pop();
	}

	public boolean isEmpty() {
		return stack.empty();
	}

	public int size() {
		return stack.size();
	}
}
