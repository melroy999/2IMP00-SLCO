// #include <assert.h>

int flag1 = 0, flag2 = 0, flag3 = 0, flag4 = 0, flag5 = 0, flag6 = 0; // N boolean flags
int turn = 0; // integer variable to hold the ID of the thread whose turn is it
//int x; // variable to test mutual exclusion

void* thr1(void * arg) {
  flag1 = 1;
  while (flag2 >= 1 || flag3 >= 1 || flag4 >= 1 || flag5 >= 1 || flag6 >= 1) {
    if (turn != 0) {
      flag1 = 0;
      while (turn != 0) {};
      flag1 = 1;
    }
  }
  // begin: critical section
  //x = 0;
  //assert(x<=0);
  // end: critical section
  turn = 1;
  flag1 = 0;
}

void* thr2(void * arg) {
  flag2 = 1;
  while (flag1 >= 1 || flag3 >= 1 || flag4 >= 1 || flag5 >= 1 || flag6 >= 1) {
    if (turn != 1) {
      flag2 = 0;
      while (turn != 1) {};
      flag2 = 1;
    }
  }
  // begin: critical section
  //x = 1;
  //assert(x>=1);
  // end: critical section
  turn = 2;
  flag2 = 0;
}

void* thr3(void * arg) {
  flag3 = 1;
  while (flag1 >= 1 || flag2 >= 1 || flag4 >= 1 || flag5 >= 1 || flag6 >= 1) {
    if (turn != 2) {
      flag3 = 0;
      while (turn != 2) {};
      flag3 = 1;
    }
  }
  // begin: critical section
  //x = 1;
  //assert(x>=1);
  // end: critical section
  turn = 3;
  flag3 = 0;
}

void* thr4(void * arg) {
  flag4 = 1;
  while (flag1 >= 1 || flag2 >= 1 || flag3 >= 1 || flag5 >= 1 || flag6 >= 1) {
    if (turn != 3) {
      flag4 = 0;
      while (turn != 3) {};
      flag4 = 1;
    }
  }
  // begin: critical section
  //x = 1;
  //assert(x>=1);
  // end: critical section
  turn = 4;
  flag4 = 0;
}

void* thr5(void * arg) {
  flag5 = 1;
  while (flag1 >= 1 || flag2 >= 1 || flag3 >= 1 || flag4 >= 1 || flag6 >= 1) {
    if (turn != 4) {
      flag5 = 0;
      while (turn != 4) {};
      flag5 = 1;
    }
  }
  // begin: critical section
  //x = 1;
  //assert(x>=1);
  // end: critical section
  turn = 5;
  flag5 = 0;
}

void* thr6(void * arg) {
  flag6 = 1;
  while (flag1 >= 1 || flag2 >= 1 || flag3 >= 1 || flag4 >= 1 || flag5 >= 1) {
    if (turn != 5) {
      flag6 = 0;
      while (turn != 5) {};
      flag6 = 1;
    }
  }
  // begin: critical section
  //x = 1;
  //assert(x>=1);
  // end: critical section
  turn = 0;
  flag6 = 0;
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
