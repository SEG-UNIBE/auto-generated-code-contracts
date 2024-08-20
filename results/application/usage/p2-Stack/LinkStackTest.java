package p2.StackTest3;

import junit.framework.TestCase;

public class LinkStackTest extends TestCase {
	protected StackInterface<String> stack;
	protected int size;

	protected void setUp() throws Exception {
		super.setUp();
		stack = new LinkStack<String>();
	}

	public void testEmpty() {
		assertTrue(stack.isEmpty());
		assertEquals(0, stack.size());
	}

	public void testEmptyTopFails() {
		try {
			stack.top();
			fail("emptyTop should fail");
		} catch (AssertionError e) {
			assertEquals(null, e.getMessage());
		}
	}

	public void testEmptyPopFails() {
		try {
			stack.pop();
			fail("emptyPop should fail");
		} catch (AssertionError e) {
			assertEquals(null, e.getMessage());
		}
	}

	public void testNullPush() {
		stack.push(null);
		assertFalse(stack.isEmpty());
		assertEquals(null, stack.top());
		assertEquals(1, size = stack.size());
		stack.pop();
		assertEquals(size - 1, stack.size());
	}

	public void testOneElement() {
		stack.push("a");
		assertFalse(stack.isEmpty());
		assertEquals(1, size = stack.size());
		stack.pop();
		assertEquals(size - 1, stack.size());
	}

	public void testTwoElement() {
		stack.push("a");
		stack.push("b");
		assertFalse(stack.isEmpty());
		assertEquals(2, size = stack.size());
		stack.pop();
		assertEquals(size - 1, stack.size());
	}

	public void testSevenElement() {
		size = 7;
		for (int n = 0; n < 7; n++)
			stack.push((new Integer(n)).toString());
		assertFalse(stack.isEmpty());
		assertEquals(size, stack.size());
		stack.pop();
		stack.pop();
		stack.pop();
		assertEquals(size - 3, stack.size());
	}

	public void testFirstInLastOut() {
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

}