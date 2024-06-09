struct pred {
    int data;
    struct pred *link1;
    struct pred *link2;
};

/*@ Let dlistrep(l, p) = l == 0 && emp ||
      exists v t, data_at(field_addr(l, data), v) * 
                data_at(field_addr(l, link2), t) *
                data_at(field_addr(l, link1), p) *
                dlistrep(t, l)
 */

/*@ Let dlseg(x, xp, yp, y) = x == y && xp == yp && emp ||
      exists v z, data_at(field_addr(x, data), v) *
                data_at(field_addr(x, link2), z) *
                data_at(field_addr(x, link1), xp) *
                dlseg(z, x, yp, y)
 */

struct pred * append(struct pred * x, struct pred * y)
/*@ Require dlistrep(x, 0) * dlistrep(y, 0)
    Ensure  dlistrep(__return, 0)
 */
{
    struct pred *t, *u;
    if (x == 0) {
        return y;
    } else {
        t = x;
        u = t->link2;
        /*@ exists v, v == t->data && 
            u == t->link2 &&
            dlistrep(y, 0) *
            dlistrep(u, t) *
            dlseg(x, 0, t->link1, t)
         */
        while (u) {
            t = u;
            u = t->link2;
        }
        t->link2 = y;
        if (y) {
            y->link1 = t;
        }
        return x;
    }
}