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

struct list_head * append(struct list_head * x, struct list_head * y)
/*@ Require dlistrep(x, 0) * dlistrep(y, 0)
    Ensure  dlistrep(__return, 0)
 */
{
    struct list_head *t, *u;
    if (x == 0) {
        return y;
    } else {
        t = x;
        u = t->next;
        /*@ u == t->next &&
            dlistrep(y, 0) *
            dlistrep(u, t) *
            dlseg(x, 0, t->prev, t)
         */
        while (u) {
            t = u;
            u = t->next;
        }
        t->next = y;
        if (y) {
            y->prev = t;
        }
        return x;
    }
}