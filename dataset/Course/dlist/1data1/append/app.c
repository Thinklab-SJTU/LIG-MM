struct dlist {
    int head;
    struct dlist *prev;
    struct dlist *next;
};

/*@ Let dlistrep(l, p) = l == 0 && emp ||
      exists v t, data_at(field_addr(l, head), v) * 
                data_at(field_addr(l, next), t) *
                data_at(field_addr(l, prev), p) *
                dlistrep(t, l)
 */

/*@ Let dlseg(x, xp, yp, y) = x == y && xp == yp && emp ||
      exists v z, data_at(field_addr(x, head), v) *
                data_at(field_addr(x, next), z) *
                data_at(field_addr(x, prev), xp) *
                dlseg(z, x, yp, y)
 */

struct dlist * append(struct dlist * x, struct dlist * y)
/*@ Require dlistrep(x, 0) * dlistrep(y, 0)
    Ensure  dlistrep(__return, 0)
 */
{
    struct dlist *t, *u;
    if (x == 0) {
        return y;
    } else {
        t = x;
        u = t->next;
        /*@ exists v, v == t->head && 
            u == t->next &&
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