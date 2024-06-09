struct sys_dlist_t {
    struct sys_dlist_t *head;
    struct sys_dlist_t *tail;
};

/*@ Let dlistrep(l, p) = l == 0 && emp ||
      exists t, data_at(field_addr(l, tail), t) *
                data_at(field_addr(l, head), p) *
                dlistrep(t, l)
 */

/*@ Let dlseg(x, xp, yp, y) = x == y && xp == yp && emp ||
      exists z, data_at(field_addr(x, tail), z) *
                data_at(field_addr(x, head), xp) *
                dlseg(z, x, yp, y)
 */

struct sys_dlist_t *reverse(struct sys_dlist_t *p)
/*@ Require dlistrep(p, 0)
    Ensure  dlistrep(__return, 0)
*/;


struct sys_dlist_t *rev_append(struct sys_dlist_t *p, struct sys_dlist_t *q)
/*@ Require dlistrep(p,0) * dlistrep(q,0)
    Ensure  dlistrep(__return,0)
 */
{
    struct sys_dlist_t *w, *t, *v;
    w = q;
    v = p;
    if (w) {
      /*@ w != 0 && dlistrep(v, 0) * dlistrep(w, 0) */
      while (v) {
        t = v -> tail;
        v-> tail = w;
        w-> head = v; 
        w = v;
        v = t;
        if (v) {
          v -> head = 0;
        }
      }
    }
    else {
      w = reverse(v);
    }
    return w;
}