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
 */;

struct llist_node *multi_merge(struct llist_node *x , struct llist_node *y, struct llist_node *z)
/*@ Require listrep(x) * listrep(y) * listrep(z)
    Ensure  listrep(__return)
 */
{
    struct llist_node *t,*u;
    if (x == 0) {
      t = merge(y,z);
      return t; 
    }
    else {
      t = x;
      u = t->next;
      /*@ data_at(field_addr(t, next), u) * 
          listrep(y) *
          listrep(z) * 
          listrep(u) *
          lseg(x, t)
      */
      while (u) {
        if (y) {
          t -> next = y;
          t = y;
          y = y -> next;
        }
        else {
          u = merge(u , z);
          t -> next = u;
          return x;   
        }
        if (z) {
          t -> next = z;
          t = z;
          z = z -> next;
        }
        else {
          u = merge(u , y);
          t -> next = u;
          return x;
        }
        t -> next = u;
        t = u;
        u = u -> next;
      }
  }
  t->next = merge(y,z);
  return x;
}