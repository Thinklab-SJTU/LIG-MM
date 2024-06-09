struct list {
    int head;
    struct list *tail;
};

/*@ Let listrep(l) = l == 0 && emp ||
      exists t, data_at(field_addr(l, tail), t) * listrep(t)
 */
 
/*@ Let lseg(x, y) = x == y && emp ||
      exists z, data_at(field_addr(x, tail), z) * lseg(z, y)
 */

/*@ Let listbox_rep(x) = exists p, *x == p && listrep(p) */ 


/*@ Let listbox_seg(x,y) = x == y && emp || 
       exists p, *x == p && listbox_seg(&(p->tail),y) 
*/

struct list ** malloc_list(void)
  /*@ Require emp
      Ensure exists p, *__return == p && emp
   */
  ;

void free_list(struct list * * p2)
  /*@ With p
      Require *p2 == p && emp
      Ensure emp
   */
  ;

struct list *merge(struct list *x , struct list *y)
/*@ Require listrep(x) * listrep(y)
    Ensure  listrep(__return)
 */;

struct list *multi_merge(struct list *x , struct list *y, struct list *z)
/*@ Require listrep(x) * listrep(y) * listrep(z)
    Ensure  listrep(__return)
 */
{
    struct list **t,**px,*u;
    if (x == 0) {
      u = merge(y,z);
      return u; 
    }
    else {
      px = malloc_list();
      t = px;
      *t = x;
      u = x->tail;
      /*@ px == t && (*t) -> tail == u &&
          lseg(x,*t) *   
          listrep(y) *
          listrep(z) *
          listrep(u)
      */
      while (u) {
        if (y) {
          (*t) -> tail = y;
          *t = y;
          y = y -> tail;
        }
        else {
          u = merge(u , z);
          (*t) -> tail = u;
          free_list(px);
          return x;   
        }
        if (z) {
          (*t) -> tail = z;
          *t = z;
          z = z -> tail;
        }
        else {
          u = merge(u , y);
          (*t) -> tail = u;
          free_list(px);
          return x;
        }
        (*t) -> tail = u;
        *t = u;
        u = u -> tail;
      }
  }
  (*t)->tail = merge(y,z);
  free_list(px);
  return x;
}