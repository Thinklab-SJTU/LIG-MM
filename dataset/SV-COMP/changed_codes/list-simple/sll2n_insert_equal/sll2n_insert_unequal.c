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

struct SLL * insert_unequal(struct SLL *l, int data) 
/*@ With data0
    Require data == data0 && listrep(l)
    Ensure  listrep(__return)
 */
{
  struct SLL *p;
  struct SLL *new_node;
  new_node = 0;
  p = l;
  /*@ exists p_prev, data == data0 && new_node == 0 &&
        lseg(l,p) * listrep(p)
  */
  while (p) {
    if (p-> head != data) {
      new_node = malloc_SLL(data);
      new_node->tail = p->tail;
      p->tail = new_node;
      return l;
    }
    p = p->tail;
  }
  return l;
}
