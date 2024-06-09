struct sys_slist_t {
    struct sys_slist_t *next;
};

/*@ Let listrep(l) = l == 0 && emp ||
      exists t, data_at(field_addr(l, next), t) * listrep(t)
 */
 
/*@ Let lseg(x, y) = x == y && emp ||
      exists z, data_at(field_addr(x, next), z) * lseg(z, y)
 */

struct sys_slist_t *iter_twice(struct sys_slist_t *l)
/*@ Require listrep(l)
    Ensure  listrep(__return)
 */
{
    struct sys_slist_t *p;
    p = l;
    /*@ listrep(p) * lseg(l,p) */
    while (p) {
        p = p->next;
        if (p) {
          p = p -> next;
        }
    }
    return l;
}