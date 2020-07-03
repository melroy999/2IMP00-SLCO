
int flag1 = 0, flag2 = 0, flag3 = 0; // N integer flags

void* thr1(void * arg) {
  while (1) {
    flag1 = 1;
    flag1 = 3;
    if (flag2 == 1 || flag3 == 1) {
      flag1 = 2;
    }
    flag1 = 4;
    // begin critical section
    // end critical section
    flag1 = 0;
  }
}

void* thr2(void * arg) {
  while (1) {
    flag2 = 1;
    flag2 = 3;
    if (flag1 == 1 || flag3 == 1) {
      flag2 = 2;
    }
    flag2 = 4;
    // begin critical section
    // end critical section
    flag2 = 0;
  }
}

void* thr3(void * arg) {
  while (1) {
    flag3 = 1;
    flag3 = 3;
    if (flag1 == 1 || flag2 == 1) {
      flag3 = 2;
    }
    flag3 = 4;
    // begin critical section
    // end critical section
    flag3 = 0;
  }
}

int main()
{
  __CPROVER_ASYNC_1: thr1(0);
  __CPROVER_ASYNC_2: thr2(0);
  thr3(0);
}
