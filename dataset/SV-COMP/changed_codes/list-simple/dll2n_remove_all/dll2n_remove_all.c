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

struct DLL* malloc_DLL(int v)
/*@ With v0 
    Require v == v0 && emp
    Ensure data_at(field_addr(__return, data), v0) * 
           data_at(field_addr(__return, next), 0) *
           data_at(field_addr(__return, prev), 0) 
*/;

void free_DLL(struct DLL *l)
/*@ With v n p
    Require data_at(field_addr(l, data), v) * 
            data_at(field_addr(l, next), n) *
            data_at(field_addr(l, prev), p)
    Ensure emp
*/;


void remove_all(struct DLL *l) 
/*@ Require dlistrep(l, 0)
    Ensure  emp
 */
{
  struct DLL *p;
  p = l;
  /*@ l == p && dlistrep(l, 0) */
  while (l) {
    p = l->next;
    free_DLL(l);
    if (p) {
      p->prev = 0;
    }
    l = p;
  }
}
