struct llist_node {
    struct llist_node *next;
};

/*@ Let listrep(l) = l == 0 && emp ||
      exists t, data_at(field_addr(l, next), t) * listrep(t)
 */
 
/*@ Let lseg(x, y) = x == y && emp ||
      exists z, data_at(field_addr(x, next), z) * lseg(z, y)
 */

struct llist_node *rev_append(struct llist_node *p, struct llist_node *q)
/*@ Require p != q && listrep(p) * listrep(q)
    Ensure  listrep(__return)
 */
{
    struct llist_node *w, *t, *v;
    w = q;
    v = p;
    /*@ lseg(w, q) * listrep(v) * listrep(q) */
    while (v) {
      t = v->next;
      v->next = w;
      w = v;
      v = t;
    }
    return w;
}