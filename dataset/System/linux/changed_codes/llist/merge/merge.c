struct llist_node {
    struct llist_node *next;
};

/*@ Let listrep(l) = l == 0 && emp ||
      exists t, data_at(field_addr(l, next), t) * listrep(t)
 */
 
/*@ Let lseg(x, y) = x == y && emp ||
      exists z, data_at(field_addr(x, next), z) * lseg(z, y)
 */

struct llist_node *merge(struct llist_node *x , struct llist_node *y)
/*@ Require listrep(x) * listrep(y)
    Ensure  listrep(__return)
 */
{
    struct llist_node *z, *t;
    if (x == 0) {
      return y; 
    }
    else {
      z = x;
      t = y;
      /*@ y == t && x != 0 && lseg(z , x) * listrep(x) * listrep(y) */
      while (y) {
        t = y -> next;
        y -> next = x -> next;
        x -> next = y;
        if (y -> next == 0) {
          y -> next = t;
          return z;
        }
        else {
          x = y -> next;
          y = t;
        }
      }
    }
    
    return z;
}