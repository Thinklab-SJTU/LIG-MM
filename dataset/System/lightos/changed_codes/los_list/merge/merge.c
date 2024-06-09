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

struct LOS_DL_LIST *merge(struct LOS_DL_LIST * x, struct LOS_DL_LIST * y)
/*@ Require dlistrep(x, 0) * dlistrep(y, 0)
    Ensure  dlistrep(__return, 0)
 */
{
    struct LOS_DL_LIST *z, *t;
    if (x == 0) {
      return y; 
    }
    else {
      z = x;
      t = y;
      /*@ y == t && x != 0 && dlseg(z, 0, x->pstPrev, x) * dlistrep(x->pstNext, x) * dlistrep(y , 0) */
      while (y) {
        t = y -> pstNext;
        y -> pstNext = x -> pstNext;
        y -> pstPrev = x;
        x -> pstNext = y;
        if (y -> pstNext == 0) {
          y -> pstNext = t;
          return z;
        }
        else {
          x = y -> pstNext;
          x -> pstPrev = y;
          y = t;
          if (t) {
          	t -> pstPrev = 0;
          }
        }
      }
    }
    
    return z;
}