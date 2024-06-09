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

struct SNnode * sll_copy(struct SNnode * x)
/*@ Require listrep(x)
    Ensure  listrep(__return) * listrep(x)
 */
{
    struct SNnode *y, *p, *t;
    y = malloc_SNnode(0);
    t = y;
    p = x;
    /*@ t -> tail == 0 && t -> head == 0 && lseg(x,p) * listrep(p) * lseg(y, t) */
    while (p) {
      t -> head = p -> head;
      t -> tail = malloc_SNnode(0);
      p = p -> tail;
      t = t -> tail;
    }
    return y;
}