struct dlist {
    int head;
    struct dlist *prev;
    struct dlist *next;
};

/*@ Let dlistrep(l, p) = l == 0 && emp ||
      exists v t, data_at(field_addr(l, head), v) * 
                data_at(field_addr(l, next), t) *
                data_at(field_addr(l, prev), p) *
                dlistrep(t, l)
 */

/*@ Let dlseg(x, xp, yp, y) = x == y && xp == yp && emp ||
      exists v z, data_at(field_addr(x, head), v) *
                data_at(field_addr(x, next), z) *
                data_at(field_addr(x, prev), xp) *
                dlseg(z, x, yp, y)
 */

struct dlist *iter(struct dlist *l)
/*@ With lprev
    Require dlistrep(l, lprev)
    Ensure  dlistrep(__return, lprev)
 */
{
    struct dlist *p;
    p = l;
    /*@ exists p_prev,
          dlseg(l, lprev, p_prev, p) *
          dlistrep(p, p_prev)
     */
    while (p) {
        p = p->next;
    }
    return l;
}