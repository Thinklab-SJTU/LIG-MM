struct SNnode {
    int head;
    struct SNnode *tail;
};

/*@ Let listrep(l) = l == 0 && emp ||
      exists v t, data_at(field_addr(l, head), v) * data_at(field_addr(l, tail), t) * listrep(t)
 */
 
/*@ Let lseg(x, y) = x == y && emp ||
      exists v z, data_at(field_addr(x, head), v) * data_at(field_addr(x, tail), z) * lseg(z, y)
 */

struct SNnode* malloc_SNnode(int data)
/*@ With data0 
    Require data == data0 && emp
    Ensure data_at(field_addr(__return, head), data0) * 
           data_at(field_addr(__return, tail), 0)
*/;

struct SNnode * insert(struct SNnode * x, int data)
/*@ With data0
    Require data == data0 && listrep(x)
    Ensure  listrep(__return)
 */
{
    struct SNnode *p, *new_node;
    new_node = 0;
    p = x;
    /*@ data == data0 && new_node == 0 && lseg(x,p) * listrep(p) */
    while (p) {
      if (p->head < data) {
        new_node = malloc_SNnode(data);
        new_node -> tail = p -> tail;
        p -> tail = new_node;
        return x;
      }
      p = p -> tail;
    }
    return x;
}