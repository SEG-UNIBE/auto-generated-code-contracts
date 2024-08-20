package genstack;

import org.junit.jupiter.api.*;
import static org.junit.jupiter.api.Assertions.*;

/**
 * A stack implemented as a linked list of cells.
 */
public class LinkStackTest {
    
	protected StackInterface<String> stack;

	@BeforeEach
    public void setUp() {
		stack = new LinkStack<String>();
	}

	@Test
    public void empty() {
		assertTrue(stack.isEmpty());
		assertEquals(0, stack.size());
	}

	@Test
	public void emptyTopFails() {
		assertThrows(AssertionError.class, () -> stack.top());
	}

	@Test
	public void emptyRemoveFails() {
		assertThrows(AssertionError.class, () -> stack.pop());
	}

	@Test
    public void pushOneElement() {
		stack.push("a");
		assertFalse(stack.isEmpty());
		assertEquals(1, stack.size());
		assertEquals("a", stack.top());
	}

	@Test
    public void pushPopOneElement() {
		stack.push("a");
		stack.pop();
		assertTrue(stack.isEmpty());
		assertEquals(0, stack.size());	
	}

	@Test
    public void pushNull() {
		stack.push(null);
		assertFalse(stack.isEmpty());
		assertEquals(1, stack.size());
		assertNull(stack.top());
	}

	@Test
    public void twoElement() {
		stack.push("a");
		assertEquals("a", stack.top());
		stack.push("b");
		assertEquals("b", stack.top());
		stack.pop();
		assertEquals("a", stack.top());
		stack.pop();
		assertTrue(stack.isEmpty());
	}

	@Test
    public void firstInLastOut() {
		stack.push("a");
		stack.push("b");
		stack.push("c");
		assertEquals("c", stack.top());
		stack.pop();
		assertEquals("b", stack.top());
		stack.pop();
		assertEquals("a", stack.top());
		stack.pop();
		assertTrue(stack.isEmpty());	
	}

	@Test
	public void brokenSequence() {
		stack.push("a");
		stack.pop();
		assertThrows(AssertionError.class, () -> stack.pop());
	}

}
