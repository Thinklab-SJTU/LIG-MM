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

struct pred *iter_twice(struct pred *l)
/*@ With link1
    Require dlistrep(l, link1)
    Ensure  dlistrep(__return, link1)
 */
{
    struct pred *p;
    p = l;
    /*@ exists p_prev,
        dlseg(l,link1,p_prev,p) * dlistrep(p, p_prev)
     */
    while (p) {
        p = p->link2;
        if (p) {
          p = p -> link2;
        }
      	else {
          return l;
        }
    }
    return l;
}