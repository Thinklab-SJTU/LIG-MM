struct llist_node {
    struct llist_node *next;
};

/*@ Let listrep(l) = l == 0 && emp ||
      exists t, data_at(field_addr(l, next), t) * listrep(t)
 */
 
/*@ Let lseg(x, y) = x == y && emp ||
      exists z, data_at(field_addr(x, next), z) * lseg(z, y)
 */

struct llist_node * append(struct llist_node * x, struct llist_node * y)
/*@ Require listrep(x) * listrep(y)
    Ensure  listrep(__return)
 */
{
    struct llist_node *t, *u;
    if (x == 0) {
        return y;
    } else {
        t = x;
        u = t->next;
        /*@ data_at(field_addr(t, next), u) * 
            listrep(y) *
            listrep(u) *
            lseg(x, t)
         */
        while (u) {
            t = u;
            u = t->next;
        }
        t->next = y;
        return x;
    }
}