package genstack;

import org.junit.jupiter.api.BeforeEach;

/**
 * Override setUp to run the same generic tests with
 * a different Stack implementation.
 */
public class ArrayStackTest extends LinkStackTest {

	@BeforeEach
    public void setUp() {
		stack = new ArrayStack<String>();
	}
	
}
