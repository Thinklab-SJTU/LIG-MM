struct pred {
    int data;
    struct pred *link;
};

/*@ Let listrep(l) = l == 0 && emp ||
      exists t, data_at(field_addr(l, link), t) * listrep(t)
 */
 
/*@ Let lseg(x, y) = x == y && emp ||
      exists z, data_at(field_addr(x, link), z) * lseg(z, y)
 */

struct pred *iter(struct pred *l)
/*@ Require listrep(l)
    Ensure  listrep(__return)
 */
{
    struct pred *p;
    p = l;
    /*@ listrep(p) * lseg(l, p) */
    while (p) {
        p = p->link;
    }
    return l;
}