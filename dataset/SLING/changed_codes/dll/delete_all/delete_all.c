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

void free_DLNode(struct DLNode *l)
/*@ With v n p
    Require data_at(field_addr(l, head), v) * 
            data_at(field_addr(l, next), n) *
            data_at(field_addr(l, prev), p)
    Ensure emp
*/;

void deleta_all(struct DLNode * l)
/*@ Require dlistrep(l, 0)
    Ensure  emp
 */
{
    struct DLNode *p;
    p = l;
    /*@ l == p && dlistrep(l, 0) */
    while (l) {
      p = l->next;
      free_DLNode(l);
      if (p) {
        p->prev = 0;
      }
      l = p;
    }
}