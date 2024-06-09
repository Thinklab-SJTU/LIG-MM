struct sys_slist_t {
    struct sys_slist_t *next;
};

/*@ Let listrep(l) = l == 0 && emp ||
      exists t, data_at(field_addr(l, next), t) * listrep(t)
 */
 
/*@ Let lseg(x, y) = x == y && emp ||
      exists z, data_at(field_addr(x, next), z) * lseg(z, y)
 */

struct sys_slist_t *reverse(struct sys_slist_t *p)
/*@ Require listrep(p)
    Ensure  listrep(__return)
 */
{
    struct sys_slist_t *w, *t, *v;
    w = 0;
    v = p;
    /*@ listrep(w) * listrep(v) */
    while (v) {
        t = v->next;
        v->next = w;
        w = v;
        v = t;
    }
    return w;
}