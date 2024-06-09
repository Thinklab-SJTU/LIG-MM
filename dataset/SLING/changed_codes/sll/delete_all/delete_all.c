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

void free_SNnode(struct SNnode *l)
/*@ With v n
    Require data_at(field_addr(l, head), v) * 
            data_at(field_addr(l, tail), n)
    Ensure emp
*/;

struct SNnode * delete_all(struct SNnode * l)
/*@ Require listrep(l)
    Ensure  emp
 */
{
    struct SNnode *p;
    p = l;
    /*@ l == p && listrep(l) */
    while (l) {
      p = l->tail;
      free_SNnode(l);
      l = p;
    } 
}