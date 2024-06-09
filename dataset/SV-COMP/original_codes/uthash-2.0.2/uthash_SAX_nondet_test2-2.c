#include "uthash_SAX.h"
#include <time.h>
#include <stdlib.h>   /* malloc */
#include "verifier.h"
#include <assert.h>// nondeterministic version of test2.c, instead of 10 we have a nondeterministic bound
// of hash table entries (up to 10000). Checking every even ID should always return a result.

typedef struct example_user_t {
    int id;
    int cookie;
    UT_hash_handle hh;
} example_user_t;

int main()
{
    int i;
    example_user_t *user, *tmp, *users=NULL;
    unsigned int bound = __VERIFIER_nondet_uint();
    if (bound > BOUND) return 1;

    /* create elements */
    for(i=0; i<bound; i++) {
        user = (example_user_t*)malloc(sizeof(example_user_t));
        if (user == NULL) {
            exit(-1);
        }
        user->id = i;
        user->cookie = i*i;
        HASH_ADD_INT(users,id,user);
    }

    /* find each even ID */
    for(i=0; i<bound; i+=2) {
        HASH_FIND_INT(users,&i,tmp);
        __VERIFIER_assert(tmp != NULL);
    }
    example_user_t* temp;
    HASH_ITER(hh, users, user, temp) {
      HASH_DEL(users, user);
      free(user);
    }
    return 0;
}