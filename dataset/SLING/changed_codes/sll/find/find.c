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

int find(struct SNnode * x, int data)
/*@ With data0
    Require data0 == data && listrep(x)
    Ensure  __return == 1 && listrep(x) ||
            __return == -1 && listrep(x)
 */
{
    struct SNnode * p;
    p = x;
    /*@ data == data0 && lseg(x,p) * listrep(p) */
    while (p) {
      if (p->head == data) {
        return 1;
      }
      p = p->tail;
    }
    return -1;
}