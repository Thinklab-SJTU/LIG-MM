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

struct SLL * update_all_reverse(struct SLL *p, int data) 
/*@ With data0
    Require data == data0 && listrep(l)
    Ensure  listrep(__return)
 */
{
  struct SLL *w, *t, *v;
  w = (void *)0;
  v = p;
  /*@ listrep(w) *
      listrep(v)
  */
  while (v) {
    t = v->tail;
    v->tail = w;
    if (v-> head != data) {
      v -> head = data;
    }
    w = v;
    v = t;
  }
  return w;
}
