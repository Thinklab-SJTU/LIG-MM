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

struct sys_dlist_t *iter_back(struct sys_dlist_t *l, struct sys_dlist_t *front)
/*@ With l_head
	  Require dlseg(front, 0, l_head, l) * dlistrep(l, l_head)
    Ensure  dlistrep(__return, 0)
 */
{
    struct sys_dlist_t *p;
    if (l == 0) {
      return front;
    }
  	else {
    	p = l;
      /*@ dlseg(front, 0, p->head, p) * dlistrep(p->tail , p)*/
    	while (p != front) {
      	  p = p -> head; 
      }
    }
    return p;
}