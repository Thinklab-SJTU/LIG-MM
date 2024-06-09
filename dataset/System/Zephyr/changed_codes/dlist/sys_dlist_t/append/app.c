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

struct sys_dlist_t * append(struct sys_dlist_t * x, struct sys_dlist_t * y)
/*@ Require dlistrep(x, 0) * dlistrep(y, 0)
    Ensure  dlistrep(__return, 0)
 */
{
    struct sys_dlist_t *t, *u;
    if (x == 0) {
        return y;
    } else {
        t = x;
        u = t->tail;
        /*@ u == t->tail &&
            dlistrep(y, 0) *
            dlistrep(u, t) *
            dlseg(x, 0, t->head, t)
         */
        while (u) {
            t = u;
            u = t->tail;
        }
        t->tail = y;
        if (y) {
            y->head = t;
        }
        return x;
    }
}