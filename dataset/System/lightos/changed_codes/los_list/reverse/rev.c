struct LOS_DL_LIST {
    struct LOS_DL_LIST *pstPrev;
    struct LOS_DL_LIST *pstNext;
};

/*@ Let dlistrep(l, p) = l == 0 && emp ||
      exists t, data_at(field_addr(l, pstNext), t) *
                data_at(field_addr(l, pstPrev), p) *
                dlistrep(t, l)
 */

/*@ Let dlseg(x, xp, yp, y) = x == y && xp == yp && emp ||
      exists z, data_at(field_addr(x, pstNext), z) *
                data_at(field_addr(x, pstPrev), xp) *
                dlseg(z, x, yp, y)
 */

struct LOS_DL_LIST *reverse(struct LOS_DL_LIST *p)
/*@ Require dlistrep(p, 0)
    Ensure  dlistrep(__return, 0)
 */
{
    struct LOS_DL_LIST *w, *t, *v;
    w = (void *)0;
    v = p;
    /*@ dlistrep(w, v) *
        dlistrep(v, w)
     */
    while (v) {
        t = v->pstNext;
        v->pstNext = w;
        v->pstPrev = t;
        w = v;
        v = t;
    }
    return w;
}