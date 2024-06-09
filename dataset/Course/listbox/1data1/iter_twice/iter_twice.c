struct list {
    int head;
    struct list *tail;
};

/*@ Let listrep(l) = l == 0 && emp ||
      exists v t, data_at(field_addr(l, head), v) * data_at(field_addr(l, tail), t) * listrep(t)
 */
 
/*@ Let lseg(x, y) = x == y && emp ||
      exists v z, data_at(field_addr(x, head), v) * data_at(field_addr(x, tail), z) * lseg(z, y)
 */

/*@ Let listbox_rep(x) = exists p, *x == p && listrep(p) */ 


/*@ Let listbox_seg(x,y) = x == y && emp || 
       exists v p, *x == p && data_at(field_addr(p, head), v) * listbox_seg(&(p->tail),y) 
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

struct list *iter(struct list *x)
  /*@ Require listrep(x)
      Ensure listrep(__return)
  */
{
  struct list * * t, * * px;
  px = malloc_list();
  t = px;
  * t = x;
  /*@ listbox_seg(px, t) * listrep(*t)
  */
  while (* t != (void *) 0) {
    t = &((*t) -> tail);
    if (*t != (void *) 0) {
      t = &((*t) -> tail);
    }
  }
  x = * px;
  free_list(px);
  return x;
}