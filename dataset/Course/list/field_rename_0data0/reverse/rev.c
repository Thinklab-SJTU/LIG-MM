struct pred {
    struct pred *link;
};

/*@ Let listrep(l) = l == 0 && emp ||
      exists t, data_at(field_addr(l, link), t) * listrep(t)
 */
 
/*@ Let lseg(x, y) = x == y && emp ||
      exists z, data_at(field_addr(x, link), z) * lseg(z, y)
 */

struct pred *reverse(struct pred *p)
/*@ Require listrep(p)
    Ensure  listrep(__return)
 */
{
    struct pred *w, *t, *v;
    w = 0;
    v = p;
    /*@ listrep(w) * listrep(v) */
    while (v) {
        t = v->link;
        v->link = w;
        w = v;
        v = t;
    }
    return w;
}