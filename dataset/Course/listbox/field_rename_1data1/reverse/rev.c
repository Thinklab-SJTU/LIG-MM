struct pred {
    int data;
    struct pred *link;
};

/*@ Let listrep(l) = l == 0 && emp ||
      exists v t, data_at(field_addr(l, data), v) * data_at(field_addr(l, link), t) * listrep(t)
 */
 
/*@ Let lseg(x, y) = x == y && emp ||
      exists v z, data_at(field_addr(x, data), v) * data_at(field_addr(x, link), z) * lseg(z, y)
 */

/*@ Let listbox_rep(x) = exists p, *x == p && listrep(p) */ 


/*@ Let listbox_seg(x,y) = x == y && emp || 
       exists v p, *x == p && data_at(field_addr(p, data), v) * listbox_seg(&(p->link),y) 
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

struct pred *reverse(struct pred *x)
  /*@ Require listrep(x)
      Ensure listrep(__return)
  */
{
  struct pred * * w, * * px, *t,*v;
  px = malloc_list();
  w = px;
  * w = 0;
  v = x;
  /*@ px == w && listrep(v) * listbox_rep(w) */
  while (v) {
    t = v->link;
    v->link = *w;
    *w = v;
    v = t;
  }
  v = *w;
  free_list(px);
  return v;
}