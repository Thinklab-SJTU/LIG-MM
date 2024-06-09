struct list_head {
    struct list_head *prev;
    struct list_head *next;
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

struct list_head *reverse(struct list_head *p)
/*@ Require dlistrep(p, 0)
    Ensure  dlistrep(__return, 0)
 */
{
    struct list_head *w, *t, *v;
    w = (void *)0;
    v = p;
    /*@ dlistrep(w, v) *
        dlistrep(v, w)
     */
    while (v) {
        t = v->next;
        v->next = w;
        v->prev = t;
        w = v;
        v = t;
    }
    return w;
}