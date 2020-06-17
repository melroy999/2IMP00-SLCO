int x;
int y;
int b1, b2, b3, b4, b5, b6; // N boolean flags

void* thr1(void * arg) {
  L0:
    b1 = 1;
    x = 1;
    if (y != 0) {
      b1 = 0;
      __CPROVER_assume(y == 0);
      goto L0;
    }
    y = 1;
    if (x != 1) {
      b1 = 0;
      __CPROVER_assume (b2 == 0 && b3 == 0 && b4 == 0 && b5 == 0 && b6 == 0);
      if (y != 1) {
	__CPROVER_assume (y == 0);
	goto L0;
      }
    }
  // begin: critical section
  // end: critical section
  y = 0;
  b1 = 0;
}

void* thr2(void * arg) {
  L1:
    b2 = 1;
    x = 2;
    if (y != 0) {
      b2 = 0;
      __CPROVER_assume (y == 0);
      goto L1;
    }
    y = 2;
    if (x != 2) {
      b2 = 0;
      __CPROVER_assume (b1 == 0 && b3 == 0 && b4 == 0 && b5 == 0 && b6 == 0);
      if (y != 2) {
	__CPROVER_assume (y == 0);
	goto L1;
      }
    }
  // begin: critical section
  // end: critical section
  y = 0;
  b2 = 0;
}

void* thr3(void * arg) {
  L2:
    b3 = 1;
    x = 3;
    if (y != 0) {
      b3 = 0;
      __CPROVER_assume (y == 0);
      goto L2;
    }
    y = 3;
    if (x != 3) {
      b3 = 0;
      __CPROVER_assume (b1 == 0 && b2 == 0 && b4 == 0 && b5 == 0 && b6 == 0);
      if (y != 3) {
    __CPROVER_assume (y == 0);
    goto L2;
      }
    }
  // begin: critical section
  // end: critical section
  y = 0;
  b3 = 0;
}

void* thr4(void * arg) {
  L3:
    b4 = 1;
    x = 4;
    if (y != 0) {
      b4 = 0;
      __CPROVER_assume (y == 0);
      goto L3;
    }
    y = 4;
    if (x != 4) {
      b4 = 0;
      __CPROVER_assume (b1 == 0 && b2 == 0 && b3 == 0 && b5 == 0 && b6 == 0);
      if (y != 4) {
    __CPROVER_assume (y == 0);
    goto L3;
      }
    }
  // begin: critical section
  // end: critical section
  y = 0;
  b4 = 0;
}

void* thr5(void * arg) {
  L4:
    b5 = 1;
    x = 5;
    if (y != 0) {
      b5 = 0;
      __CPROVER_assume (y == 0);
      goto L4;
    }
    y = 5;
    if (x != 5) {
      b5 = 0;
      __CPROVER_assume (b1 == 0 && b2 == 0 && b3 == 0 && b4 == 0 && b6 == 0);
      if (y != 5) {
    __CPROVER_assume (y == 0);
    goto L4;
      }
    }
  // begin: critical section
  // end: critical section
  y = 0;
  b5 = 0;
}

void* thr6(void * arg) {
  L5:
    b6 = 1;
    x = 6;
    if (y != 0) {
      b6 = 0;
      __CPROVER_assume (y == 0);
      goto L5;
    }
    y = 6;
    if (x != 6) {
      b6 = 0;
      __CPROVER_assume (b1 == 0 && b2 == 0 && b3 == 0 && b4 == 0 && b5 == 0);
      if (y != 6) {
    __CPROVER_assume (y == 0);
    goto L5;
      }
    }
  // begin: critical section
  // end: critical section
  y = 0;
  b6 = 0;
}

int main()
{
  __CPROVER_ASYNC_1: thr1(0);
  thr2(0);
  thr3(0);
  thr4(0);
  thr5(0);
  thr6(0);
}
