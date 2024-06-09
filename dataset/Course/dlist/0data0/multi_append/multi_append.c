struct dlist {
    struct dlist *prev;
    struct dlist *next;
};

/*@ Let dlistrep(l, p) = l == 0 && emp ||
      exists t, data_at(field_addr(l, next), t) *
                data_at(field_addr(l, prev), p) *
                dlistrep(t, l)
 */

/*@ Let dlseg(x, xp, yp, y) = x == y && xp == yp && emp ||
      exists z, data_at(field_addr(x, next), z) *
                data_at(field_addr(x, prev), xp) *
                dlseg(z, x, yp, y)
 */

struct dlist * append(struct dlist * x, struct dlist * y)
/*@ With x_prev
	Require dlistrep(x, x_prev) * dlistrep(y,0)
  Ensure dlistrep(__return,x_prev)
 */;

struct dlist *multi_append(struct dlist *x, struct dlist *y, struct dlist *z)
/*@ Require dlistrep(x,0) * dlistrep(y,0) * dlistrep(z,0)
    Ensure  dlistrep(__return,0)
 */
{
    struct dlist *t, *u;
    if (x == 0) {
        t = append(y , z);
        return t;
    } else {
        t = x;
        u = t->next;
        /*@ u == t -> next &&  
            dlistrep(y,0) *
            dlistrep(z,0) * 
            dlistrep(u,t) *
            dlseg(x, 0, t->prev, t)
         */
        while (u) {
            if (y) {
              t -> next = y;
              y -> prev = t;
              t = y;
              y = y -> next;
              t -> next = u;
              u -> prev = t;
              if (y) {
                y -> prev = 0;
              }
              t = u;
              u = u -> next;
            }
            else {
              u = append(u , z);
              t -> next = u;
              return x;   
            }
        }
        u = append(y,z);
        t -> next = u;
      	if (u) {
          u -> prev = t;
        }
        return x;
    }
}