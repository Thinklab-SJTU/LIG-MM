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

struct LOS_DL_LIST *iter_twice(struct LOS_DL_LIST *l)
/*@ With pstPrev
    Require dlistrep(l, pstPrev)
    Ensure  dlistrep(__return, pstPrev)
 */
{
    struct LOS_DL_LIST *p;
    p = l;
    /*@ exists p_prev,
        dlseg(l,pstPrev,p_prev,p) * dlistrep(p, p_prev)
     */
    while (p) {
        p = p->pstNext;
        if (p) {
          p = p -> pstNext;
        }
      	else {
          return l;
        }
    }
    return l;
}