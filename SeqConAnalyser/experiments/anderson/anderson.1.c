// #include <assert.h>

int Slot[2] = {1,0};
int next = 0;

void* P0(void * arg) {
    int myplace;

    // NCS
    while (1) {
			myplace = next;
			next = next+1;
			// p1
			if (myplace == 2-1) {
				next = next-2;
			}
			else {
				myplace = myplace % 2;
			}
			// p2
			while (Slot[myplace] == 1) {};
			// p3
			Slot[(myplace+2-1)%2] = 0;
			// CS
			Slot[(myplace+1)%2] = 1;
	 }
}

void* P1(void * arg) {
    int myplace;

    // NCS
    while (1) {
			myplace = next;
			next = next+1;
			// p1
			if (myplace == 2-1) {
				next = next-2;
			}
			else {
				myplace = myplace % 2;
			}
			// p2
			while (Slot[myplace] == 1) {};
			// p3
			Slot[(myplace+2-1)%2] = 0;
			// CS
			Slot[(myplace+1)%2] = 1;
	 }
}

int main()
{
  __CPROVER_ASYNC_1: P0(0);
  P1(0);
}
