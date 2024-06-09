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

struct pred *iter_back(struct pred *l, struct pred *head)
/*@ With l_prev
	  Require dlseg(head, 0, l_prev, l) * dlistrep(l, l_prev)
    Ensure  dlistrep(__return, 0)
 */
{
    struct pred *p;
    if (l == 0) {
      return head;
    }
  	else {
    	p = l;
      /*@ dlseg(head, 0, p->link1, p) * dlistrep(p->link2 , p)*/
    	while (p != head) {
      	  p = p -> link1; 
      }
    }
    return p;
}