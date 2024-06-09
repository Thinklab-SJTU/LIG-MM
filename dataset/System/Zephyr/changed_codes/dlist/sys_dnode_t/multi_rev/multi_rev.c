struct sys_dnode_t {
    struct sys_dnode_t *prev;
    struct sys_dnode_t *next;
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

struct sys_dnode_t * append(struct sys_dnode_t * x, struct sys_dnode_t * y)
/*@ With x_prev
	Require dlistrep(x, x_prev) * dlistrep(y,0)
  Ensure dlistrep(__return,x_prev)
 */;

struct sys_dnode_t *multi_rev(struct sys_dnode_t *p, struct sys_dnode_t *q)
/*@ Require dlistrep(p,0) * dlistrep(q,0)
    Ensure  dlistrep(__return,0)
 */
{
    struct sys_dnode_t *w, *t, *v, *x, *y;
    w = 0;
    x = 0;
    v = p;
    y = q;
    /*@ dlistrep(w, v) * dlistrep(v, w) * dlistrep(x, y) * dlistrep(y, x) */
    while (1) {
      if (v) {
        t = v->next;
        v->next = w;
        v->prev = t;
        w = v;
        v = t;
      }
      else {
        if (y) {
          t = y->next;
          y->next = x;
          y->prev = t;
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