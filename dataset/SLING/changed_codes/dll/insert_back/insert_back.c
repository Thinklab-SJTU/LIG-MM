struct DLNode {
    int head;
    struct DLNode *prev;
    struct DLNode *next;
};

/*@ Let dlistrep(l, p) = l == 0 && emp ||
      exists v t, data_at(field_addr(l, head), v) * 
                data_at(field_addr(l, next), t) *
                data_at(field_addr(l, prev), p) *
                dlistrep(t, l)
 */

/*@ Let dlseg(x, xp, yp, y) = x == y && xp == yp && emp ||
      exists v z, data_at(field_addr(x, head), v) *
                data_at(field_addr(x, next), z) *
                data_at(field_addr(x, prev), xp) *
                dlseg(z, x, yp, y)
 */

struct DLNode* malloc_DLNode(int data)
/*@ With data0 
    Require data == data0 && emp
    Ensure data_at(field_addr(__return, head), data0) * 
           data_at(field_addr(__return, next), 0) *
           data_at(field_addr(__return, prev), 0) 
*/;

struct DLNode * insert_back(struct DLNode * x, int data)
/*@ With data0
    Require data == data0 && dlistrep(x, 0)
    Ensure  dlistrep(__return, 0)
 */
{
    struct DLNode *p;
    p = x;
    /*@ exists p_prev, data == data0 && 
        dlseg(x,0,p_prev,p) * dlistrep(p, p_prev)
    */
    while (p) {
      if (p->next == 0) {
        p->next = malloc_DLNode(data);
        p->next->prev = p;
        p = p -> next;
      }
      p = p->next;
    }
    return x;
}