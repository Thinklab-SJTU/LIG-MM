#include "uthash_OAT.h"
#include <stdlib.h>   /* malloc */
#include "verifier.h"
#include <assert.h>// version of test4.c with nondeterministic number of entries
// and an added consistency check for the user id.

typedef struct example_user_t {
    int id;
    int cookie;
    UT_hash_handle hh;
    UT_hash_handle alth;
} example_user_t;

int main()
{
    int i;
    example_user_t *user, *users=NULL, *altusers=NULL;
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
        HASH_ADD(alth,altusers,cookie,sizeof(int),user);
    }

    for(user=altusers; user != NULL; user=(example_user_t*)(user->alth.next)) {
        __VERIFIER_assert(user->id <= BOUND && user->id >= 0);
    }
    return 0;
}