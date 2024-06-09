struct list_head {
    struct list_head *prev;
    struct list_head *next;
};

/*@ Let dlistrep(l, p) = l == 0 && emp ||
      exists t, data_at(field_addr(l, next), t) *
                data_at(field_addr(l, prev), p) *
                dlistrep(t, l)
 */

/*@ Let dlseg(x, xp, yp, y) = x == y && xp == yp && emp ||
      exists z, data_at(field_addr(x, next), z) *
                data_at(field_addr(x, prev), xp) *
                dlseg(z, x, yp, y)
 */

struct list_head *iter_back(struct list_head *l, struct list_head *head)
/*@ With l_prev
	  Require dlseg(head, 0, l_prev, l) * dlistrep(l, l_prev)
    Ensure  dlistrep(__return, 0)
 */
{
    struct list_head *p;
    if (l == 0) {
      return head;
    }
  	else {
    	p = l;
      /*@ dlseg(head, 0, p->prev, p) * dlistrep(p->next , p)*/
    	while (p != head) {
      	  p = p -> prev; 
      }
    }
    return p;
}