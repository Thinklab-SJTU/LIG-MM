struct pred {
    int data;
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

struct pred *merge(struct pred * x, struct pred * y)
/*@ Require dlistrep(x, 0) * dlistrep(y, 0)
    Ensure  dlistrep(__return, 0)
 */
{
    struct pred *z, *t;
    if (x == 0) {
      return y; 
    }
    else {
      z = x;
      t = y;
      /*@ y == t && x != 0 && dlseg(z, 0, x->link1, x) * dlistrep(x->link2, x) * dlistrep(y , 0) */
      while (y) {
        t = y -> link2;
        y -> link2 = x -> link2;
        y -> link1 = x;
        x -> link2 = y;
        if (y -> link2 == 0) {
          y -> link2 = t;
          return z;
        }
        else {
          x = y -> link2;
          x -> link1 = y;
          y = t;
          if (t) {
          	t -> link1 = 0;
          }
        }
      }
    }
    
    return z;
}