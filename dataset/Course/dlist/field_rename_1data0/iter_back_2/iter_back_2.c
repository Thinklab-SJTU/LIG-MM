struct pred {
    int data;
    struct pred *link1;
    struct pred *link2;
};

/*@ Let dlistrep(l, p) = l == 0 && emp ||
      exists t, data_at(field_addr(l, link2), t) *
                data_at(field_addr(l, link1), p) *
                dlistrep(t, l)
 */

/*@ Let dlseg(x, xp, yp, y) = x == y && xp == yp && emp ||
      exists z, data_at(field_addr(x, link2), z) *
                data_at(field_addr(x, link1), xp) *
                dlseg(z, x, yp, y)
 */

struct pred *iter_back_2(struct pred **head, struct pred **tail)
/*@ With head_node tail_node 
	Require *head == head_node && *tail == tail_node && head_node != 0 && tail_node != 0 && dlseg(head_node,0,tail_node,0)
    Ensure *head == head_node && *tail == tail_node && dlseg(__return, 0, tail_node, 0)
 */
{
    struct pred *p;
    p = *tail;
    if (*head == *tail) {
      return p;
    }
    else {
    /*@ *head == head_node && *tail == tail_node &&
        dlseg(head_node , 0 , p->link1 , p) * 
        dlseg(p->link2 , p , tail_node , 0)
    */
    while (p != *head) {
      p = p -> link1;
    }
    return p;
  }
}