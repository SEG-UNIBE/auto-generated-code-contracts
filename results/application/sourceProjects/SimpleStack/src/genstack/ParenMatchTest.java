package genstack;

import org.junit.jupiter.api.*;
import static org.junit.jupiter.api.Assertions.*;

public class ParenMatchTest {
	protected ParenMatch pm;

	protected ParenMatch makePm(String input) {
		return new ParenMatch(input, new LinkStack<Character>());
	}

	@Test
	public void empty() {
		pm = makePm("");
		assertTrue(pm.parenMatch()); // (6)
	}

	@org.junit.jupiter.api.Test
	public void balancedSequence() {
		pm = makePm("()[]{}");
		assertTrue(pm.parenMatch()); // (1) (3) (6)
	}

	@Test
	public void balancedWithOtherChars() {
		pm = makePm("public void main() { return true; }");
		assertTrue(pm.parenMatch()); // (1) (3) (5) (6)
	}

	@Test
	public void missingRightParen() {
		pm = makePm("[(");
		assertFalse(pm.parenMatch()); // (1) (6)
	}

	@org.junit.jupiter.api.Test
	public void missingLeftParen() {
		pm = makePm("]");
		assertFalse(pm.parenMatch()); // (2)
	}

	@Test
	public void mismatch() {
		pm = makePm("(]");
		assertFalse(pm.parenMatch()); // (1) (4)
	}

	@Test
	public void balancedNested() {
		pm = makePm("{()[()()[]]}");
		assertTrue(pm.parenMatch()); // (1) (3) (6)
	}

}
