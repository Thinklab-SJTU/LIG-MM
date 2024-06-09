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

struct sys_dlist_t *merge(struct sys_dlist_t *x , struct sys_dlist_t *y)
/*@ With x_head 
    Require dlistrep(x,x_head) * dlistrep(y,0)
    Ensure  dlistrep(__return,x_head)
 */;

struct sys_dlist_t *multi_merge(struct sys_dlist_t *x , struct sys_dlist_t *y, struct sys_dlist_t *z)
/*@ Require dlistrep(x,0) * dlistrep(y,0) * dlistrep(z,0)
    Ensure  dlistrep(__return,0)
 */
{
    struct sys_dlist_t *t,*u;
    if (x == 0) {
      t = merge(y,z);
      return t; 
    }
    else {
      t = x;
      u = t->tail;
      /*@ u == t -> tail &&  
          dlistrep(y,0) *
          dlistrep(z,0) * 
          dlistrep(u,t) *
          dlseg(x, 0, t->head, t)
      */
      while (u) {
        if (y) {
          t -> tail = y;
          y -> head = t;
          t = y;
          u -> head = t;
          y = y -> tail;
          if (y) {
            y -> head = 0;
          }    
        }
        else {
          u = merge(u , z);
          t -> tail = u;
          return x;   
        }
        if (z) {
          t -> tail = z;
          z -> head = t;
          t = z;
          u -> head = t;
          z = z -> tail;
          if (z) {
            z -> head = 0;
          }
        }
        else {
          u = merge(u , y);
          t -> tail = u;
          return x;
        }
        t -> tail = u;
        u -> head = t;
        t = u;
        u = u -> tail;
      }
  }
  u = merge(y,z);
  t -> tail = u;
  if (u) {
    u -> head = t;
  }
  return x;
}