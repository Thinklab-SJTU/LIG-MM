struct sys_dnode_t {
    struct sys_dnode_t *prev;
    struct sys_dnode_t *next;
};

/*@ Let dlistrep(l, p) = l == 0 && emp ||
      exists t, data_at(field_addr(l, next), t) *
                data_at(field_addr(l, prev), p) *
                dlistrep(t, l)
 */

/*@ Let dlseg(x, xp, yp, y) = x == y && xp == yp && emp ||
      exists z, data_at(field_addr(x, next), z) *
                data_at(field_addr(x, prev), xp) *
                dlseg(z, x, yp, y)
 */

struct sys_dnode_t *iter_twice(struct sys_dnode_t *l)
/*@ With prev
    Require dlistrep(l, prev)
    Ensure  dlistrep(__return, prev)
 */
{
    struct sys_dnode_t *p;
    p = l;
    /*@ exists p_prev,
        dlseg(l,prev,p_prev,p) * dlistrep(p, p_prev)
     */
    while (p) {
        p = p->next;
        if (p) {
          p = p -> next;
        }
      	else {
          return l;
        }
    }
    return l;
}