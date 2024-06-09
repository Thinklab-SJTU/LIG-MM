struct list_head {
    struct list_head *prev;
    struct list_head *next;
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

struct list_head * append(struct list_head * x, struct list_head * y)
/*@ With x_prev
	Require dlistrep(x, x_prev) * dlistrep(y,0)
  Ensure dlistrep(__return,x_prev)
 */;

struct list_head *multi_append(struct list_head *x, struct list_head *y, struct list_head *z)
/*@ Require dlistrep(x,0) * dlistrep(y,0) * dlistrep(z,0)
    Ensure  dlistrep(__return,0)
 */
{
    struct list_head *t, *u;
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