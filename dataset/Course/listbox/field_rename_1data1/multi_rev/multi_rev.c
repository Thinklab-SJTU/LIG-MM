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

struct pred *append(struct pred * x, struct pred * y)
/*@ Require listrep(x) * listrep(y)
    Ensure  listrep(__return)
 */;

struct pred *multi_rev(struct pred *p, struct pred *q)
/*@ Require listrep(p) * listrep(q)
    Ensure  listrep(__return)
 */
{
    struct pred **w, *t, *x, *y,*u;
    struct pred *v, * * px;
    px = malloc_list();
    w = px;
    * w = 0;
    v = p;
    x = 0;
    y = q;
    /*@ px == w && listrep(v) * listbox_rep(w) * listrep(x) * listrep(y) */
    while (1) {
      if (v) {
        t = v->link;
        v->link = *w;
        *w = v;
        v = t;
      }
      else {
        if (y) {
          t = y->link;
          y->link = x;
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