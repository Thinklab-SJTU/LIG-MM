struct pred {
    int data;
    struct pred *link;
};

/*@ Let listrep(l) = l == 0 && emp ||
      exists t, data_at(field_addr(l, link), t) * listrep(t)
 */
 
/*@ Let lseg(x, y) = x == y && emp ||
      exists z, data_at(field_addr(x, link), z) * lseg(z, y)
 */

/*@ Let listbox_rep(x) = exists p, *x == p && listrep(p) */ 


/*@ Let listbox_seg(x,y) = x == y && emp || 
       exists p, *x == p && listbox_seg(&(p->link),y) 
*/

struct pred ** malloc_list(void)
  /*@ Require emp
      Ensure exists p, *__return == p && emp
   */
  ;

void free_list(struct pred * * p2)
  /*@ With p
      Require *p2 == p && emp
      Ensure emp
   */
  ;

struct pred *iter(struct pred *x)
  /*@ Require listrep(x)
      Ensure listrep(__return)
  */
{
  struct pred * * t, * * px;
  px = malloc_list();
  t = px;
  * t = x;
  /*@ listbox_seg(px, t) * listrep(*t)
  */
  while (* t != (void *) 0) {
    t = &((*t) -> link);
    if (*t != (void *) 0) {
      t = &((*t) -> link);
    }
  }
  x = * px;
  free_list(px);
  return x;
}