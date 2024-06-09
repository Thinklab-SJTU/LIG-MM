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

struct LOS_DL_LIST *iter_back_2(struct LOS_DL_LIST **head, struct LOS_DL_LIST **tail)
/*@ With head_node tail_node 
	Require *head == head_node && *tail == tail_node && head_node != 0 && tail_node != 0 && dlseg(head_node,0,tail_node,0)
    Ensure *head == head_node && *tail == tail_node && dlseg(__return, 0, tail_node, 0)
 */
{
    struct LOS_DL_LIST *p;
    p = *tail;
    if (*head == *tail) {
      return p;
    }
    else {
    /*@ *head == head_node && *tail == tail_node &&
        dlseg(head_node , 0 , p->pstPrev , p) * 
        dlseg(p->pstNext , p , tail_node , 0)
    */
    while (p != *head) {
      p = p -> pstPrev;
    }
    return p;
  }
}