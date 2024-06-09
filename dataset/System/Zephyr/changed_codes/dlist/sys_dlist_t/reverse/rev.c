struct sys_dlist_t {
    struct sys_dlist_t *head;
    struct sys_dlist_t *tail;
};

/*@ Let dlistrep(l, p) = l == 0 && emp ||
      exists t, data_at(field_addr(l, tail), t) *
                data_at(field_addr(l, head), p) *
                dlistrep(t, l)
 */

/*@ Let dlseg(x, xp, yp, y) = x == y && xp == yp && emp ||
      exists z, data_at(field_addr(x, tail), z) *
                data_at(field_addr(x, head), xp) *
                dlseg(z, x, yp, y)
 */

struct sys_dlist_t *reverse(struct sys_dlist_t *p)
/*@ Require dlistrep(p, 0)
    Ensure  dlistrep(__return, 0)
 */
{
    struct sys_dlist_t *w, *t, *v;
    w = (void *)0;
    v = p;
    /*@ dlistrep(w, v) *
        dlistrep(v, w)
     */
    while (v) {
        t = v->tail;
        v->tail = w;
        v->head = t;
        w = v;
        v = t;
    }
    return w;
}