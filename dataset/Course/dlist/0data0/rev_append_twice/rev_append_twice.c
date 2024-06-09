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

struct dlist *reverse(struct dlist *p)
/*@ Require dlistrep(p, 0)
    Ensure  dlistrep(__return, 0)
*/;


struct dlist *rev_append_twice(struct dlist *p, struct dlist *q)
/*@ Require dlistrep(p,0) * dlistrep(q,0)
    Ensure  dlistrep(__return,0)
 */
{
    struct dlist *w, *t, *v;
    w = q;
    v = p;
    if (w) {
      /*@ w != 0 && dlistrep(v, 0) * dlistrep(w, 0) */
      while (v) {
        t = v -> next;
        v-> next = w;
        w-> prev = v; 
        w = v;
        v = t;
        if (v) {
          v -> prev = 0;
          t = v -> next;
          v-> next = w;
          w-> prev = v; 
          w = v;
          v = t;
          if (v) {
            v -> prev = 0;
          }
        }
      }
    }
    else {
      w = reverse(v);
    }
    return w;
}