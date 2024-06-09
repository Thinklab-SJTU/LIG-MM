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

struct pred * append(struct pred * x, struct pred * y)
/*@ Require listrep(x) * listrep(y)
    Ensure  listrep(__return)
 */;

struct pred *multi_append(struct pred *x, struct pred *y, struct pred *z)
/*@ Require listrep(x) * listrep(y) * listrep(z)
    Ensure  listrep(__return)
 */
{
    struct pred **t, **px, *u;
    if (x == 0) {
        u = append(y , z);
        return u;
    } else {
        px = malloc_list();
        t = px;
        * t = x;
        u = x -> link;
        /*@ exists v, (*t) -> data == v &&
            *px == x && (*t)->link == u &&  
            listrep(y) *
            listrep(z) * 
            listrep(u) *
            listbox_seg(px, t)
         */
        while (u) {
            if (y) {
              (*t) -> link = y;
              *t = y;
              y = y -> link;
              (*t) -> link = u;
              *t = u;
              u = u -> link;
            }
            else {
              u = append(u , z);
              (*t) -> link = u;
              free_list(px);
              return x;   
            }
        }
        (*t)->link = append(y,z);
        free_list(px);
        return x;
    }
}