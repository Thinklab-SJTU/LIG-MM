struct SLL {
  struct SLL *tail;
  int head;
};

/*@ Let listrep(l) = l == 0 && emp ||
      exists v t, data_at(field_addr(l, head), v) * data_at(field_addr(l, tail), t) * listrep(t)
 */
 
/*@ Let lseg(x, y) = x == y && emp ||
      exists v z, data_at(field_addr(x, head), v) * data_at(field_addr(x, tail), z) * lseg(z, y)
 */

struct SLL * append_equal(struct SLL *l, int data) 
/*@ With data0
    Require data == data0 && listrep(l)
    Ensure  listrep(__return)
 */
{
  struct SLL *p;
  p = l;
  /*@ data == data0 && lseg(l,p) * listrep(p)
  */
  while (p) {
    if (p-> head != data) {
      return l;
    }
    p = p->tail;
  }
  return l;
}
