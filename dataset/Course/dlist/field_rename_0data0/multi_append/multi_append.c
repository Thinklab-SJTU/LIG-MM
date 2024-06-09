struct pred {
    struct pred *link1;
    struct pred *link2;
};

/*@ Let dlistrep(l, p) = l == 0 && emp ||
      exists t, data_at(field_addr(l, link2), t) *
                data_at(field_addr(l, link1), p) *
                dlistrep(t, l)
 */

/*@ Let dlseg(x, xp, yp, y) = x == y && xp == yp && emp ||
      exists z, data_at(field_addr(x, link2), z) *
                data_at(field_addr(x, link1), xp) *
                dlseg(z, x, yp, y)
 */

struct pred * append(struct pred * x, struct pred * y)
/*@ With x_prev
	Require dlistrep(x, x_prev) * dlistrep(y,0)
  Ensure dlistrep(__return,x_prev)
 */;

struct pred *multi_append(struct pred *x, struct pred *y, struct pred *z)
/*@ Require dlistrep(x,0) * dlistrep(y,0) * dlistrep(z,0)
    Ensure  dlistrep(__return,0)
 */
{
    struct pred *t, *u;
    if (x == 0) {
        t = append(y , z);
        return t;
    } else {
        t = x;
        u = t->link2;
        /*@ u == t -> link2 &&  
            dlistrep(y,0) *
            dlistrep(z,0) * 
            dlistrep(u,t) *
            dlseg(x, 0, t->link1, t)
         */
        while (u) {
            if (y) {
              t -> link2 = y;
              y -> link1 = t;
              t = y;
              y = y -> link2;
              t -> link2 = u;
              u -> link1 = t;
              if (y) {
                y -> link1 = 0;
              }
              t = u;
              u = u -> link2;
            }
            else {
              u = append(u , z);
              t -> link2 = u;
              return x;   
            }
        }
        u = append(y,z);
        t -> link2 = u;
      	if (u) {
          u -> link1 = t;
        }
        return x;
    }
}