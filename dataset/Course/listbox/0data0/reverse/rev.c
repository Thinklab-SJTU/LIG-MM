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

struct list *reverse(struct list *x)
  /*@ Require listrep(x)
      Ensure listrep(__return)
  */
{
  struct list * * w, * * px, *t,*v;
  px = malloc_list();
  w = px;
  * w = 0;
  v = x;
  /*@ px == w && listrep(v) * listbox_rep(w) */
  while (v) {
    t = v->tail;
    v->tail = *w;
    *w = v;
    v = t;
  }
  v = *w;
  free_list(px);
  return v;
}