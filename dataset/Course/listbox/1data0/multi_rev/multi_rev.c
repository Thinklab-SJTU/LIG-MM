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

struct list *append(struct list * x, struct list * y)
/*@ Require listrep(x) * listrep(y)
    Ensure  listrep(__return)
 */;

struct list *multi_rev(struct list *p, struct list *q)
/*@ Require listrep(p) * listrep(q)
    Ensure  listrep(__return)
 */
{
    struct list **w, *t, *x, *y,*u;
    struct list *v, * * px;
    px = malloc_list();
    w = px;
    * w = 0;
    v = p;
    x = 0;
    y = q;
    /*@ px == w && listrep(v) * listbox_rep(w) * listrep(x) * listrep(y) */
    while (1) {
      if (v) {
        t = v->tail;
        v->tail = *w;
        *w = v;
        v = t;
      }
      else {
        if (y) {
          t = y->tail;
          y->tail = x;
          x = y;
          y = t;
        }
        else { 
          t = append(*w , x);
          free_list(px);
          return t;
        }
      }
    }
  // Deadcode : return 0;
}