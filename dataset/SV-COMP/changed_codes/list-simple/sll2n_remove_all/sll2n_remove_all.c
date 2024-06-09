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

struct SLL* malloc_SLL(int data)
/*@ With data0 
    Require data == data0 && emp
    Ensure data_at(field_addr(__return, head), data0) * 
           data_at(field_addr(__return, tail), 0)
*/;

void free_SLL(struct SLL *l)
/*@ With v n
    Require data_at(field_addr(l, head), v) * 
            data_at(field_addr(l, tail), n)
    Ensure emp
*/;


void remove_all(struct SLL *l) 
/*@ Require listrep(l)
    Ensure  emp
 */
{
  struct SLL *p;
  p = l;
  /*@ l == p && listrep(l) */
  while (l) {
    p = l->tail;
    free_SLL(l);
    l = p;
  }
}
