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
 */;

struct llist_node *append(struct llist_node * x, struct llist_node * y)
/*@ Require listrep(x) * listrep(y)
    Ensure  listrep(__return)
 */;

struct llist_node *multi_rev(struct llist_node *p, struct llist_node *q)
/*@ Require listrep(p) * listrep(q)
    Ensure  listrep(__return)
 */
{
    struct llist_node *w, *t, *v, *x, *y;
    w = 0;
    x = 0;
    v = p;
    y = q;
    /*@ listrep(w) * listrep(v) * listrep(x) * listrep(y) */
    while (1) {
      if (v) {
        t = v->next;
        v->next = w;
        w = v;
        v = t;
      }
      else {
        if (y) {
          t = y->next;
          y->next = x;
          x = y;
          y = t;
        }
        else { 
          t = append(w , x);
          return t;
        }
      }
    }
  // Deadcode : return 0;
}