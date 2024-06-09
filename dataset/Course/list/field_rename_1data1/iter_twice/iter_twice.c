struct pred {
    int data;
    struct pred *link;
};

/*@ Let listrep(l) = l == 0 && emp ||
      exists v t, data_at(field_addr(l, data), v) * data_at(field_addr(l, link), t) * listrep(t)
 */
 
/*@ Let lseg(x, y) = x == y && emp ||
      exists v z, data_at(field_addr(x, data), v) * data_at(field_addr(x, link), z) * lseg(z, y)
 */

struct pred *iter_twice(struct pred *l)
/*@ Require listrep(l)
    Ensure  listrep(__return)
 */
{
    struct pred *p;
    p = l;
    /*@ listrep(p) * lseg(l,p) */
    while (p) {
        p = p->link;
        if (p) {
          p = p -> link;
        }
    }
    return l;
}