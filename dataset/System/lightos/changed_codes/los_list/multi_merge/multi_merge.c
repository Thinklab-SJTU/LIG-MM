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

struct LOS_DL_LIST *merge(struct LOS_DL_LIST *x , struct LOS_DL_LIST *y)
/*@ With x_prev 
    Require dlistrep(x,x_prev) * dlistrep(y,0)
    Ensure  dlistrep(__return,x_prev)
 */;

struct LOS_DL_LIST *multi_merge(struct LOS_DL_LIST *x , struct LOS_DL_LIST *y, struct LOS_DL_LIST *z)
/*@ Require dlistrep(x,0) * dlistrep(y,0) * dlistrep(z,0)
    Ensure  dlistrep(__return,0)
 */
{
    struct LOS_DL_LIST *t,*u;
    if (x == 0) {
      t = merge(y,z);
      return t; 
    }
    else {
      t = x;
      u = t->pstNext;
      /*@ u == t -> pstNext &&  
          dlistrep(y,0) *
          dlistrep(z,0) * 
          dlistrep(u,t) *
          dlseg(x, 0, t->pstPrev, t)
      */
      while (u) {
        if (y) {
          t -> pstNext = y;
          y -> pstPrev = t;
          t = y;
          u -> pstPrev = t;
          y = y -> pstNext;
          if (y) {
            y -> pstPrev = 0;
          }    
        }
        else {
          u = merge(u , z);
          t -> pstNext = u;
          return x;   
        }
        if (z) {
          t -> pstNext = z;
          z -> pstPrev = t;
          t = z;
          u -> pstPrev = t;
          z = z -> pstNext;
          if (z) {
            z -> pstPrev = 0;
          }
        }
        else {
          u = merge(u , y);
          t -> pstNext = u;
          return x;
        }
        t -> pstNext = u;
        u -> pstPrev = t;
        t = u;
        u = u -> pstNext;
      }
  }
  u = merge(y,z);
  t -> pstNext = u;
  if (u) {
    u -> pstPrev = t;
  }
  return x;
}