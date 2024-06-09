struct list {
    int head;
    struct list *tail;
};

/*@ Let listrep(l) = l == 0 && emp ||
      exists t, data_at(field_addr(l, tail), t) * listrep(t)
 */
 
/*@ Let lseg(x, y) = x == y && emp ||
      exists z, data_at(field_addr(x, tail), z) * lseg(z, y)
 */

struct list *iter_twice(struct list *l)
/*@ Require listrep(l)
    Ensure  listrep(__return)
 */
{
    struct list *p;
    p = l;
    /*@ listrep(p) * lseg(l,p) */
    while (p) {
        p = p->tail;
        if (p) {
          p = p -> tail;
        }
    }
    return l;
}