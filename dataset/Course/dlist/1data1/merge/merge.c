struct dlist {
    int head;
    struct dlist *prev;
    struct dlist *next;
};

/*@ Let dlistrep(l, p) = l == 0 && emp ||
      exists v t, data_at(field_addr(l, head), v) * 
                data_at(field_addr(l, next), t) *
                data_at(field_addr(l, prev), p) *
                dlistrep(t, l)
 */

/*@ Let dlseg(x, xp, yp, y) = x == y && xp == yp && emp ||
      exists v z, data_at(field_addr(x, head), v) *
                data_at(field_addr(x, next), z) *
                data_at(field_addr(x, prev), xp) *
                dlseg(z, x, yp, y)
 */

struct dlist *merge(struct dlist * x, struct dlist * y)
/*@ Require dlistrep(x, 0) * dlistrep(y, 0)
    Ensure  dlistrep(__return, 0)
 */
{
    struct dlist *z, *t;
    if (x == 0) {
      return y; 
    }
    else {
      z = x;
      t = y;
      /*@ exists v, v == x->head && y == t && 
          x != 0 && dlseg(z, 0, x->prev, x) * dlistrep(x->next, x) * dlistrep(y , 0) */
      while (y) {
        t = y -> next;
        y -> next = x -> next;
        y -> prev = x;
        x -> next = y;
        if (y -> next == 0) {
          y -> next = t;
          return z;
        }
        else {
          x = y -> next;
          x -> prev = y;
          y = t;
          if (t) {
          	t -> prev = 0;
          }
        }
      }
    }
    
    return z;
}