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
*/;


struct LOS_DL_LIST *rev_append_twice(struct LOS_DL_LIST *p, struct LOS_DL_LIST *q)
/*@ Require dlistrep(p,0) * dlistrep(q,0)
    Ensure  dlistrep(__return,0)
 */
{
    struct LOS_DL_LIST *w, *t, *v;
    w = q;
    v = p;
    if (w) {
      /*@ w != 0 && dlistrep(v, 0) * dlistrep(w, 0) */
      while (v) {
        t = v -> pstNext;
        v-> pstNext = w;
        w-> pstPrev = v; 
        w = v;
        v = t;
        if (v) {
          v -> pstPrev = 0;
          t = v -> pstNext;
          v-> pstNext = w;
          w-> pstPrev = v; 
          w = v;
          v = t;
          if (v) {
            v -> pstPrev = 0;
          }
        }
      }
    }
    else {
      w = reverse(v);
    }
    return w;
}