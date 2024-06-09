#include <assert.h>
#define BOUND 10000
extern unsigned int __VERIFIER_nondet_uint(void);
extern short __VERIFIER_nondet_short(void);

void reach_error() {
  assert(0);
}

void __VERIFIER_assert(int cond) {
  if (!cond) {
    reach_error();
  }
}
