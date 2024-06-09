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

struct DLL * update_all_reverse(struct DLL *p, int data) 
/*@ With data0
    Require data == data0 && dlistrep(l, 0)
    Ensure  dlistrep(__return, 0)
 */
{
  struct DLL *w, *t, *v;
  w = (void *)0;
  v = p;
  /*@ dlistrep(w, v) *
      dlistrep(v, w)
  */
  while (v) {
    t = v->next;
    v->next = w;
    v->prev = t;
    if (v->data != data) {
      v -> data = data;
    }
    w = v;
    v = t;
  }
  return w;
}
