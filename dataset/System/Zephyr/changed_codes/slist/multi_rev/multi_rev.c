struct sys_slist_t {
    struct sys_slist_t *next;
};

/*@ Let listrep(l) = l == 0 && emp ||
      exists t, data_at(field_addr(l, next), t) * listrep(t)
 */
 
/*@ Let lseg(x, y) = x == y && emp ||
      exists z, data_at(field_addr(x, next), z) * lseg(z, y)
 */

struct sys_slist_t *reverse(struct sys_slist_t *p)
/*@ Require listrep(p)
    Ensure  listrep(__return)
 */;

struct sys_slist_t *append(struct sys_slist_t * x, struct sys_slist_t * y)
/*@ Require listrep(x) * listrep(y)
    Ensure  listrep(__return)
 */;

struct sys_slist_t *multi_rev(struct sys_slist_t *p, struct sys_slist_t *q)
/*@ Require listrep(p) * listrep(q)
    Ensure  listrep(__return)
 */
{
    struct sys_slist_t *w, *t, *v, *x, *y;
    w = 0;
    x = 0;
    v = p;
    y = q;
    /*@ listrep(w) * listrep(v) * listrep(x) * listrep(y) */
    while (1) {
      if (v) {
        t = v->next;
        v->next = w;
        w = v;
        v = t;
      }
      else {
        if (y) {
          t = y->next;
          y->next = x;
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