struct sys_dlist_t {
    struct sys_dlist_t *head;
    struct sys_dlist_t *tail;
};

/*@ Let dlistrep(l, p) = l == 0 && emp ||
      exists t, data_at(field_addr(l, tail), t) *
                data_at(field_addr(l, head), p) *
                dlistrep(t, l)
 */

/*@ Let dlseg(x, xp, yp, y) = x == y && xp == yp && emp ||
      exists z, data_at(field_addr(x, tail), z) *
                data_at(field_addr(x, head), xp) *
                dlseg(z, x, yp, y)
 */

struct sys_dlist_t *merge(struct sys_dlist_t * x, struct sys_dlist_t * y)
/*@ Require dlistrep(x, 0) * dlistrep(y, 0)
    Ensure  dlistrep(__return, 0)
 */
{
    struct sys_dlist_t *z, *t;
    if (x == 0) {
      return y; 
    }
    else {
      z = x;
      t = y;
      /*@ y == t && x != 0 && dlseg(z, 0, x->head, x) * dlistrep(x->tail, x) * dlistrep(y , 0) */
      while (y) {
        t = y -> tail;
        y -> tail = x -> tail;
        y -> head = x;
        x -> tail = y;
        if (y -> tail == 0) {
          y -> tail = t;
          return z;
        }
        else {
          x = y -> tail;
          x -> head = y;
          y = t;
          if (t) {
          	t -> head = 0;
          }
        }
      }
    }
    
    return z;
}