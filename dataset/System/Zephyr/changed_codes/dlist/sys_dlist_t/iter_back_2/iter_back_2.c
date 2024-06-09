struct sys_dlist_t {
    struct sys_dlist_t *head;
    struct sys_dlist_t *tail;
};

/*@ Let dlistrep(l, p) = l == 0 && emp ||
      exists t, data_at(field_addr(l, tail), t) *
                data_at(field_addr(l, head), p) *
                dlistrep(t, l)
 */

/*@ Let dlseg(x, xp, yp, y) = x == y && xp == yp && emp ||
      exists z, data_at(field_addr(x, tail), z) *
                data_at(field_addr(x, head), xp) *
                dlseg(z, x, yp, y)
 */

struct sys_dlist_t *iter_back_2(struct sys_dlist_t **front, struct sys_dlist_t **end)
/*@ With front_node end_node 
	Require *front == front_node && *end == end_node && front_node != 0 && end_node != 0 && dlseg(front_node,0,end_node,0)
    Ensure *front == front_node && *end == end_node && dlseg(__return, 0, end_node, 0)
 */
{
    struct sys_dlist_t *p;
    p = *end;
    if (*front == *end) {
      return p;
    }
    else {
    /*@ *front == front_node && *end == end_node &&
        dlseg(front_node , 0 , p->head , p) * 
        dlseg(p->tail , p , end_node , 0)
    */
    while (p != *front) {
      p = p -> head;
    }
    return p;
  }
}