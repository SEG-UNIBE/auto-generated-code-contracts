package genstack;

import java.util.Stack;

/**
 * Run timing benchmarks for various Stack implementations.
 */
public class StackBenchmark {
	static int iterations = 10000000; // 10M

	static public void main(String args[]) {
		benchmark(new LinkStack<Integer>());
		// benchmark(new BrokenArrayStack<Integer>());
		benchmark(new ArrayStack<Integer>());
		// benchmark(new SimpleWrappedStack<Integer>());
		benchmark(new WrappedStack<Integer>());
		benchmark(new Stack<Integer>());
	}

	/**
	 * Times how long it takes to do a large number of pushes/pops.
	 */
	static public void benchmark(StackInterface<Integer> stack) {
		Integer item = 0;
		Timer timer = new Timer();
		long pushTime, popTime;
		
		// System.out.println("Timing " + stack.getClass().getName());
		
		timer.reset();
		for (int i=0; i<iterations; i++) {
			stack.push(item);
		}
		pushTime = timer.timeElapsed();
		// System.out.println(pushTime + " milliseconds for " + iterations + " pushes");
		
		timer.reset();
		for (int i=0; i<iterations; i++) {
			stack.pop();
		}
		popTime = timer.timeElapsed();
		// System.out.println(popTime + " milliseconds for " + iterations + " pops");
		System.out.println(stack.getClass().getName() + '\t'
				+ pushTime + '\t' + popTime);
		
	}


	/**
	 * Duplicated code cannot be refactored due to Java's type system!
	 */
	static public void benchmark(Stack<Integer> stack) {
		Integer item = 0;
		Timer timer = new Timer();
		long pushTime, popTime;
		
		// System.out.println("Timing " + stack.getClass().getName());
		
		timer.reset();
		for (int i=0; i<iterations; i++) {
			stack.push(item);
		}
		pushTime = timer.timeElapsed();
		// System.out.println(pushTime + " milliseconds for " + iterations + " pushes");
		
		timer.reset();
		for (int i=0; i<iterations; i++) {
			stack.pop();
		}
		popTime = timer.timeElapsed();
		// System.out.println(popTime + " milliseconds for " + iterations + " pops");
		System.out.println(stack.getClass().getName() + '\t'
				+ pushTime + '\t' + popTime);
		
	}

}
