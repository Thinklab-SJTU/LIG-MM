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

struct pred *merge(struct pred *x , struct pred *y)
/*@ Require listrep(x) * listrep(y)
    Ensure  listrep(__return)
 */
{
    struct pred *t;
    struct pred * * z, * * px;
    if (x == 0) {
      return y; 
    }
    else {
      px = malloc_list();
      z = px;
      * z = x;
      /*@ *z != 0 && listbox_seg(px, z) * listrep(*z) * listrep(y) */
      while (y) {
        t = y -> link;
        y -> link = (*z) -> link;
        (*z) -> link = y;
        if (y -> link == 0) {
          y -> link = t;
          x = *px;
          free_list(px);
          return x;
        }
        else {
          z = &(y -> link);
          y = t;
        }
      }
    }
    x = *px;
    free_list(px);
    return x;
}