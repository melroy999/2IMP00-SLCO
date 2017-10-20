import java.util.Random;
import java.util.concurrent.locks.ReentrantLock;
import java.util.Arrays;

// main class
public class Test {
  // The threads
  SMCThread T_SMC;
  ComThread T_Com;

  // Upperbound for transition counter
  public static final long COUNTER_BOUND = 9999999999L;

  // Enum type for state machine states
  public enum State {
  SMC1, SMC0, Com1, Com2, Com0
  }

	// Flag indicating whether threads should terminate execution
	public static boolean terminate;

  // Global variables
  public static boolean[] x;
  public static int y;

	// Lock class to handle locks of global variables
	class Keeper {
    // The locks
		ReentrantLock[] locks;
    // Which locks need to be acquired?
    boolean[] lockneeded;

		// Constructor
		Keeper() {
			locks = new ReentrantLock[3];
			lockneeded = new boolean[] { true,true,true };
			for (int i = 0; i < 3; i++) {
				locks[i] = new ReentrantLock(true);
			}
		}

		// Lock method
		public void lock(int[] l, int size) {
			for (int i = 0; i < size; i++) {
				if (lockneeded[i]) {
          locks[l[i]].lock();
        }
      }
		}

		// Unlock method
		public void unlock(int[] l, int size) {
		  for (int i = 0; i < size; i++) {
			  if (lockneeded[i]) {
          locks[l[i]].unlock();
        }
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
		// Counter of main while-loop iterations
		long transcounter;
		// Keeper of global variables
		private Test.Keeper kp;
		// Array to store IDs of locks to be acquired
		private int[] lockIDs;
		// Thread local variables
		private int i;

		// Constructor
		SMCThread (Test.Keeper k) {
			randomGenerator = new Random();
			transcounter = 0;
			currentState = Test.State.SMC0;
      kp = k;
      lockIDs = new int[3];
			i = 0;
		}

		// Execute method
		public synchronized void exec() {
			while(transcounter < COUNTER_BOUND && !terminate) {
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
								if (!(!(x[i]))) { kp.unlock(lockIDs, 3); transcounter++; break; }
                i = i + 1;
                x[i] = i == 2;
                i = 3;
                x[0] = false;
								kp.unlock(lockIDs, 3);
                notifyAll();
								// Change state
								currentState = Test.State.SMC1;
                // Increment counter
                transcounter++;
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
                // Increment counter
                transcounter++;
								break;
						}
					default:
						return;
				}
			}
			// Terminate program
			terminate = true;
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
		// Counter of main while-loop iterations
		long transcounter;
		// Keeper of global variables
		private Test.Keeper kp;
		// Array to store IDs of locks to be acquired
		private int[] lockIDs;
		// Thread local variables
		private int lx;

		// Constructor
		ComThread (Test.Keeper k) {
			randomGenerator = new Random();
			transcounter = 0;
			currentState = Test.State.Com0;
      kp = k;
      lockIDs = new int[3];
			lx = 0;
		}

		// Execute method
		public synchronized void exec() {
			while(transcounter < COUNTER_BOUND && !terminate) {
				switch(currentState) {
					case Com0:
						// lx == 0
						Arrays.sort(lockIDs,0,0);
						kp.lock(lockIDs, 0);
						while(!(lx == 0)) { kp.unlock(lockIDs, 0); try{ wait(10000); } catch (InterruptedException e) {} kp.lock(lockIDs, 0);}
						kp.unlock(lockIDs, 0);
						// Change state
						currentState = Test.State.Com1;
            // Increment counter
            transcounter++;
						break;
					default:
						return;
				}
			}
			// Terminate program
			terminate = true;
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
		terminate = false;
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