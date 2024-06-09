struct DLL {
  struct DLL *next;
  struct DLL *prev;
  int data;
};


/*@ Let dlistrep(l, p) = l == 0 && emp ||
      exists v t, data_at(field_addr(l, data), v) * 
                data_at(field_addr(l, next), t) *
                data_at(field_addr(l, prev), p) *
                dlistrep(t, l)
 */

/*@ Let dlseg(x, xp, yp, y) = x == y && xp == yp && emp ||
      exists v z, data_at(field_addr(x, data), v) *
                data_at(field_addr(x, next), z) *
                data_at(field_addr(x, prev), xp) *
                dlseg(z, x, yp, y)
 */

struct DLL * append_unequal(struct DLL *l, int data) 
/*@ With data0
    Require data == data0 && dlistrep(l, 0)
    Ensure  dlistrep(__return, 0)
 */
{
  struct DLL *p;
  p = l;
  /*@ exists p_prev, data == data0 &&
        dlseg(l,0,p_prev,p) * dlistrep(p, p_prev)
  */
  while (p) {
    if (p->data == data) {
      return l;
    }
    p = p->next;
  }
  return l;
}
