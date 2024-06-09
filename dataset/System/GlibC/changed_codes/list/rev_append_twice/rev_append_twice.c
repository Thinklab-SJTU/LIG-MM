struct list_t {
    struct list_t *prev;
    struct list_t *next;
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

struct list_t *reverse(struct list_t *p)
/*@ Require dlistrep(p, 0)
    Ensure  dlistrep(__return, 0)
*/;


struct list_t *rev_append_twice(struct list_t *p, struct list_t *q)
/*@ Require dlistrep(p,0) * dlistrep(q,0)
    Ensure  dlistrep(__return,0)
 */
{
    struct list_t *w, *t, *v;
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