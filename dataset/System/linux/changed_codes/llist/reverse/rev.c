struct llist_node {
    struct llist_node *next;
};

/*@ Let listrep(l) = l == 0 && emp ||
      exists t, data_at(field_addr(l, next), t) * listrep(t)
 */
 
/*@ Let lseg(x, y) = x == y && emp ||
      exists z, data_at(field_addr(x, next), z) * lseg(z, y)
 */

struct llist_node *reverse(struct llist_node *p)
/*@ Require listrep(p)
    Ensure  listrep(__return)
 */
{
    struct llist_node *w, *t, *v;
    w = 0;
    v = p;
    /*@ listrep(w) * listrep(v) */
    while (v) {
        t = v->next;
        v->next = w;
        w = v;
        v = t;
    }
    return w;
}