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

struct pred *reverse(struct pred *p)
/*@ Require dlistrep(p, 0)
    Ensure  dlistrep(__return, 0)
 */
{
    struct pred *w, *t, *v;
    w = (void *)0;
    v = p;
    /*@ dlistrep(w, v) *
        dlistrep(v, w)
     */
    while (v) {
        t = v->link2;
        v->link2 = w;
        v->link1 = t;
        w = v;
        v = t;
    }
    return w;
}