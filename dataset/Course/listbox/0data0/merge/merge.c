struct list {
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
 */
{
    struct list *t;
    struct list * * z, * * px;
    if (x == 0) {
      return y; 
    }
    else {
      px = malloc_list();
      z = px;
      * z = x;
      /*@ *z != 0 && listbox_seg(px, z) * listrep(*z) * listrep(y) */
      while (y) {
        t = y -> tail;
        y -> tail = (*z) -> tail;
        (*z) -> tail = y;
        if (y -> tail == 0) {
          y -> tail = t;
          x = *px;
          free_list(px);
          return x;
        }
        else {
          z = &(y -> tail);
          y = t;
        }
      }
    }
    x = *px;
    free_list(px);
    return x;
}