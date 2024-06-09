struct dlist {
    struct dlist *prev;
    struct dlist *next;
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

struct dlist *iter_back_2(struct dlist **head, struct dlist **tail)
/*@ With head_node tail_node 
	Require *head == head_node && *tail == tail_node && head_node != 0 && tail_node != 0 && dlseg(head_node,0,tail_node,0)
    Ensure *head == head_node && *tail == tail_node && dlseg(__return, 0, tail_node, 0)
 */
{
    struct dlist *p;
    p = *tail;
    if (*head == *tail) {
      return p;
    }
    else {
    /*@ *head == head_node && *tail == tail_node &&
        dlseg(head_node , 0 , p->prev , p) * 
        dlseg(p->next , p , tail_node , 0)
    */
    while (p != *head) {
      p = p -> prev;
    }
    return p;
  }
}