struct sys_dnode_t {
    struct sys_dnode_t *prev;
    struct sys_dnode_t *next;
};

/*@ Let dlistrep(l, p) = l == 0 && emp ||
      exists t, data_at(field_addr(l, next), t) *
                data_at(field_addr(l, prev), p) *
                dlistrep(t, l)
 */

/*@ Let dlseg(x, xp, yp, y) = x == y && xp == yp && emp ||
      exists z, data_at(field_addr(x, next), z) *
                data_at(field_addr(x, prev), xp) *
                dlseg(z, x, yp, y)
 */

struct sys_dnode_t *merge(struct sys_dnode_t *x , struct sys_dnode_t *y)
/*@ With x_prev 
    Require dlistrep(x,x_prev) * dlistrep(y,0)
    Ensure  dlistrep(__return,x_prev)
 */;

struct sys_dnode_t *multi_merge(struct sys_dnode_t *x , struct sys_dnode_t *y, struct sys_dnode_t *z)
/*@ Require dlistrep(x,0) * dlistrep(y,0) * dlistrep(z,0)
    Ensure  dlistrep(__return,0)
 */
{
    struct sys_dnode_t *t,*u;
    if (x == 0) {
      t = merge(y,z);
      return t; 
    }
    else {
      t = x;
      u = t->next;
      /*@ u == t -> next &&  
          dlistrep(y,0) *
          dlistrep(z,0) * 
          dlistrep(u,t) *
          dlseg(x, 0, t->prev, t)
      */
      while (u) {
        if (y) {
          t -> next = y;
          y -> prev = t;
          t = y;
          u -> prev = t;
          y = y -> next;
          if (y) {
            y -> prev = 0;
          }    
        }
        else {
          u = merge(u , z);
          t -> next = u;
          return x;   
        }
        if (z) {
          t -> next = z;
          z -> prev = t;
          t = z;
          u -> prev = t;
          z = z -> next;
          if (z) {
            z -> prev = 0;
          }
        }
        else {
          u = merge(u , y);
          t -> next = u;
          return x;
        }
        t -> next = u;
        u -> prev = t;
        t = u;
        u = u -> next;
      }
  }
  u = merge(y,z);
  t -> next = u;
  if (u) {
    u -> prev = t;
  }
  return x;
}