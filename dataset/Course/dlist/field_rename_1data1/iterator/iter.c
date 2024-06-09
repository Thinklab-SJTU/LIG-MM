struct pred {
    int data;
    struct pred *link1;
    struct pred *link2;
};

/*@ Let dlistrep(l, p) = l == 0 && emp ||
      exists v t, data_at(field_addr(l, data), v) * 
                data_at(field_addr(l, link2), t) *
                data_at(field_addr(l, link1), p) *
                dlistrep(t, l)
 */

/*@ Let dlseg(x, xp, yp, y) = x == y && xp == yp && emp ||
      exists v z, data_at(field_addr(x, data), v) *
                data_at(field_addr(x, link2), z) *
                data_at(field_addr(x, link1), xp) *
                dlseg(z, x, yp, y)
 */

struct pred *iter(struct pred *l)
/*@ With lprev
    Require dlistrep(l, lprev)
    Ensure  dlistrep(__return, lprev)
 */
{
    struct pred *p;
    p = l;
    /*@ exists p_prev,
          dlseg(l, lprev, p_prev, p) *
          dlistrep(p, p_prev)
     */
    while (p) {
        p = p->link2;
    }
    return l;
}