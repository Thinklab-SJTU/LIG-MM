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

struct LOS_DL_LIST *iter_back(struct LOS_DL_LIST *l, struct LOS_DL_LIST *head)
/*@ With l_prev
	  Require dlseg(head, 0, l_prev, l) * dlistrep(l, l_prev)
    Ensure  dlistrep(__return, 0)
 */
{
    struct LOS_DL_LIST *p;
    if (l == 0) {
      return head;
    }
  	else {
    	p = l;
      /*@ dlseg(head, 0, p->pstPrev, p) * dlistrep(p->pstNext , p)*/
    	while (p != head) {
      	  p = p -> pstPrev; 
      }
    }
    return p;
}