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

struct sys_dlist_t *iter(struct sys_dlist_t *l)
/*@ With head
    Require dlistrep(l, head)
    Ensure  dlistrep(__return, head)
 */
{
    struct sys_dlist_t *p;
    p = l;
    /*@ exists p_head,
          dlseg(l, head, p_head, p) *
          dlistrep(p, p_head)
     */
    while (p) {
        p = p->tail;
    }
    return l;
}