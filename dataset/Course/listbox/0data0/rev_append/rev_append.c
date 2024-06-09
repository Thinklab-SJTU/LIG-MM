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

struct list *rev_append(struct list *p, struct list *q)
/*@ Require p != q && listrep(p) * listrep(q)
    Ensure  listrep(__return)
 */
{
    struct list *v, *t, **w, **px;
    v = p;
    px = malloc_list();
    w = px;
    * w = q;
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