import java.util.Random;
import java.util.concurrent.locks.ReentrantLock;
import java.util.Arrays;

// main class
public class Test {
  // The threads
  SMCThread T_SMC;
  ComThread T_Com;

  // Enum type for state machine states
  public enum State {
  SMC1, SMC0, Com1, Com2, Com0
  }

  // Global variables
  public static boolean[] x;
  public static int y;

	// Lock class to handle locks of global variables
	class Keeper {
		ReentrantLock[] locks;

		// Constructor
		Keeper() {
			locks = new ReentrantLock[3];
			for (int i = 0; i < 3; i++) {
				locks[i] = new ReentrantLock(true);
			}
		}

		// Lock method
		public void lock(int[] l, int size) {
			for (int i = 0; i < size; i++) {
        locks[l[i]].lock();
      }
		}

		// Unlock method
		public void unlock(int[] l, int size) {
		  for (int i = 0; i < size; i++) {
        locks[l[i]].unlock();
      }
		}
	}

	class SMCThread extends Thread {
		private Thread t;
		private String threadName = "SMCThread";
		// Current state
		private Test.State currentState;
		// Random number generator to handle non-determinism
		private Random randomGenerator;
		// Keeper of global variables
		private Test.Keeper kp;
		// Array to store IDs of locks to be acquired
		private int[] lockIDs;
		// Thread local variables
		private int i;

		// Constructor
		SMCThread (Test.Keeper k) {
			randomGenerator = new Random();
			currentState = Test.State.SMC0;
      kp = k;
      lockIDs = new int[3];
			i = 0;
		}

		// Execute method
		public synchronized void exec() {
			while(true) {
				switch(currentState) {
					case SMC0:
						int choice = randomGenerator.nextInt(2);
						switch(choice) {
							case 0:
								// [not x[i]; i := i + 1; x[i] := i == 2; i := 3; x[0] := False]
							  lockIDs[0] = 0 + (i + 1);
							  lockIDs[1] = 0 + 0;
							  lockIDs[2] = 0 + i;
								Arrays.sort(lockIDs,0,3);
								kp.lock(lockIDs, 3);
								while(!(!(x[i]))) { kp.unlock(lockIDs, 3); try{ wait(); } catch (InterruptedException e) {} kp.lock(lockIDs, 3);}
                i = i + 1;
                x[i] = i == 2;
                i = 3;
                x[0] = false;
								kp.unlock(lockIDs, 3);
                notifyAll();
								// Change state
								currentState = Test.State.SMC1;
								break;
							case 1:
								// i := 0
								Arrays.sort(lockIDs,0,0);
								kp.lock(lockIDs, 0);
								i = 0;
								kp.unlock(lockIDs, 0);
                notifyAll();
								// Change state
								currentState = Test.State.SMC0;
								break;
						}
					default:
						return;
				}
			}
		}

		// Run method
		public void run() {
			exec();
		}

		// Start method
		public void start() {
			if (t == null) {
				t = new Thread(this);
				t.start();
			}
		}
	}
	class ComThread extends Thread {
		private Thread t;
		private String threadName = "ComThread";
		// Current state
		private Test.State currentState;
		// Random number generator to handle non-determinism
		private Random randomGenerator;
		// Keeper of global variables
		private Test.Keeper kp;
		// Array to store IDs of locks to be acquired
		private int[] lockIDs;
		// Thread local variables
		private int lx;

		// Constructor
		ComThread (Test.Keeper k) {
			randomGenerator = new Random();
			currentState = Test.State.Com0;
      kp = k;
      lockIDs = new int[3];
			lx = 0;
		}

		// Execute method
		public synchronized void exec() {
			while(true) {
				switch(currentState) {
					case Com0:
						// lx == 0
						Arrays.sort(lockIDs,0,0);
						kp.lock(lockIDs, 0);
						while(!(lx == 0)) { kp.unlock(lockIDs, 0); try{ wait(); } catch (InterruptedException e) {} kp.lock(lockIDs, 0);}
						kp.unlock(lockIDs, 0);
						// Change state
						currentState = Test.State.Com1;
						break;
					default:
						return;
				}
			}
		}

		// Run method
		public void run() {
			exec();
		}

		// Start method
		public void start() {
			if (t == null) {
				t = new Thread(this);
				t.start();
			}
		}
	}

  // Constructor for main class
  Test() {
    // Instantiate global variables
    x = new boolean[] {false,true};
    y = 0;
	  Test.Keeper k = new Test.Keeper();
		T_SMC = new Test.SMCThread(k);
		T_Com = new Test.ComThread(k);
  }

  // Start all threads
  public void startThreads() {
    T_SMC.start();
    T_Com.start();
  }

	// Run application
	public static void main(String args[]) {
    Test ap = new Test();
    ap.startThreads();
	}
}
