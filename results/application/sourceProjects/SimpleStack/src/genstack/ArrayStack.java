package genstack;

/**
 * This Stack implementation uses arrays of fixed length.
 * Whenever the array runs out of space, a new one is
 * allocated and the old data is copied.
 */
public class ArrayStack<T> implements StackInterface<T> {
	protected T store []; 
	protected int capacity;
	protected int size;

	public ArrayStack() {
		store = null;	// default value
		capacity = 0;	// available slots
		size = 0;		// used slots
	}

	@Override
	public boolean isEmpty() {
		return size == 0;
	}

	@Override
	public int size() {
		return size;
	}

	@Override
	public void push(T item) {
		if (size == capacity) {
			grow();
		}
		store[++size] = item;			// NB: bug to be fixed in demo
		assert this.top() == item;
		assert invariant();
	}

	@Override
	public T top() {
		assert !this.isEmpty();
		return store[size-1];
	}
	
	@Override
	public void pop() {
		assert !this.isEmpty();
		size--;
		// should we have a shrink() method?
		assert invariant();
	}

	/**
	 * This is where the magic occurs.  If the stack's
	 * store runs out of space, we allocate a new one
	 * and copy the old values.  The old array will eventually
	 * be garbage-collected.  Note that initially capacity == 0,
	 * so we add one before doubling it!
	 * <p>
	 * There should probably be a shrink() method to free up
	 * space when the size becomes siginicantly smaller than
	 * the capacity!
	 */
	@SuppressWarnings("unchecked")
	protected void grow() {
		int oldCapacity = capacity;
		T oldStore[] = store;

		capacity = 2 * (1 + oldCapacity);
		store = (T[]) new Object[capacity];

		for (int i = 0; i < size; i++) {
			store[i] = oldStore[i];
		}
	}
	
	protected boolean invariant() {
		return (size >= 0) && (size <= capacity) &&
			(capacity == 0 || (store != null && store.length == capacity));

	}
}
