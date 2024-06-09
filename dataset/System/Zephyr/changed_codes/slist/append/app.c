struct sys_slist_t {
    struct sys_slist_t *next;
};

/*@ Let listrep(l) = l == 0 && emp ||
      exists t, data_at(field_addr(l, next), t) * listrep(t)
 */
 
/*@ Let lseg(x, y) = x == y && emp ||
      exists z, data_at(field_addr(x, next), z) * lseg(z, y)
 */

struct sys_slist_t * append(struct sys_slist_t * x, struct sys_slist_t * y)
/*@ Require listrep(x) * listrep(y)
    Ensure  listrep(__return)
 */
{
    struct sys_slist_t *t, *u;
    if (x == 0) {
        return y;
    } else {
        t = x;
        u = t->next;
        /*@ data_at(field_addr(t, next), u) * 
            listrep(y) *
            listrep(u) *
            lseg(x, t)
         */
        while (u) {
            t = u;
            u = t->next;
        }
        t->next = y;
        return x;
    }
}