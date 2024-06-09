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

struct LOS_DL_LIST * append(struct LOS_DL_LIST * x, struct LOS_DL_LIST * y)
/*@ Require dlistrep(x, 0) * dlistrep(y, 0)
    Ensure  dlistrep(__return, 0)
 */
{
    struct LOS_DL_LIST *t, *u;
    if (x == 0) {
        return y;
    } else {
        t = x;
        u = t->pstNext;
        /*@ u == t->pstNext &&
            dlistrep(y, 0) *
            dlistrep(u, t) *
            dlseg(x, 0, t->pstPrev, t)
         */
        while (u) {
            t = u;
            u = t->pstNext;
        }
        t->pstNext = y;
        if (y) {
            y->pstPrev = t;
        }
        return x;
    }
}