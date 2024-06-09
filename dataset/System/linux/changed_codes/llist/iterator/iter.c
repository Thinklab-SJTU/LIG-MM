struct llist_node {
    struct llist_node *next;
};

/*@ Let listrep(l) = l == 0 && emp ||
      exists t, data_at(field_addr(l, next), t) * listrep(t)
 */
 
/*@ Let lseg(x, y) = x == y && emp ||
      exists z, data_at(field_addr(x, next), z) * lseg(z, y)
 */

struct llist_node *iter(struct llist_node *l)
/*@ Require listrep(l)
    Ensure  listrep(__return)
 */
{
    struct llist_node *p;
    p = l;
    /*@ listrep(p) * lseg(l, p) */
    while (p) {
        p = p->next;
    }
    return l;
}