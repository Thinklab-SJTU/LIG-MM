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

struct pred *reverse(struct pred *p)
/*@ Require dlistrep(p, 0)
    Ensure  dlistrep(__return, 0)
*/;


struct pred *rev_append(struct pred *p, struct pred *q)
/*@ Require dlistrep(p,0) * dlistrep(q,0)
    Ensure  dlistrep(__return,0)
 */
{
    struct pred *w, *t, *v;
    w = q;
    v = p;
    if (w) {
      /*@ w != 0 && dlistrep(v, 0) * dlistrep(w, 0) */
      while (v) {
        t = v -> link2;
        v-> link2 = w;
        w-> link1 = v; 
        w = v;
        v = t;
        if (v) {
          v -> link1 = 0;
        }
      }
    }
    else {
      w = reverse(v);
    }
    return w;
}