struct pred {
    struct pred *link;
};

/*@ Let listrep(l) = l == 0 && emp ||
      exists t, data_at(field_addr(l, link), t) * listrep(t)
 */
 
/*@ Let lseg(x, y) = x == y && emp ||
      exists z, data_at(field_addr(x, link), z) * lseg(z, y)
 */

struct pred *reverse(struct pred *p)
/*@ Require listrep(p)
    Ensure  listrep(__return)
 */;

struct pred *append(struct pred * x, struct pred * y)
/*@ Require listrep(x) * listrep(y)
    Ensure  listrep(__return)
 */;

struct pred *multi_rev(struct pred *p, struct pred *q)
/*@ Require listrep(p) * listrep(q)
    Ensure  listrep(__return)
 */
{
    struct pred *w, *t, *v, *x, *y;
    w = 0;
    x = 0;
    v = p;
    y = q;
    /*@ listrep(w) * listrep(v) * listrep(x) * listrep(y) */
    while (1) {
      if (v) {
        t = v->link;
        v->link = w;
        w = v;
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
          t = append(w , x);
          return t;
        }
      }
    }
  // Deadcode : return 0;
}