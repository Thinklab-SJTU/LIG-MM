struct pred {
    struct pred *link;
};

/*@ Let listrep(l) = l == 0 && emp ||
      exists t, data_at(field_addr(l, link), t) * listrep(t)
 */
 
/*@ Let lseg(x, y) = x == y && emp ||
      exists z, data_at(field_addr(x, link), z) * lseg(z, y)
 */

struct pred *merge(struct pred *x , struct pred *y)
/*@ Require listrep(x) * listrep(y)
    Ensure  listrep(__return)
 */
{
    struct pred *z, *t;
    if (x == 0) {
      return y; 
    }
    else {
      z = x;
      y = t;
      /*@ y == t && x != 0 && lseg(z , x) * listrep(x) * listrep(y) */
      while (y) {
        t = y -> link;
        y -> link = x -> link;
        x -> link = y;
        if (y -> link == 0) {
          y -> link = t;
          return z;
        }
        else {
          x = y -> link;
          y = t;
        }
      }
    }
    
    return z;
}