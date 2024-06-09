#include "uthash_JEN.h"
#include <stdlib.h>   /* malloc */
#include "verifier.h"
#include <assert.h>// version of test3.c with nondeterministic bound

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
    if (bound >= BOUND) return 1;

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

    /* delete each even ID */
    for(i=0; i<bound; i+=2) {
        HASH_FIND_INT(users,&i,tmp);
        if (tmp != NULL) {
            HASH_DEL(users,tmp);
            free(tmp);
        } else {
            __VERIFIER_assert(0);
        }
    }

    /* show the hash */
    for(user=users; user != NULL; user=(example_user_t*)(user->hh.next)) {
        __VERIFIER_assert(user->id % 2 != 0);
    }
    return 0;
}