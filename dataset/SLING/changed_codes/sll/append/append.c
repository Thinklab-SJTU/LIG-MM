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

struct SNnode * append(struct SNnode * x, struct SNnode * y)
/*@ Require listrep(x) * listrep(y)
    Ensure  listrep(__return)
 */
{
    struct SNnode *t, *u;
    if (x == 0) {
        return y;
    } else {
        t = x;
        u = t->tail;
        /*@ exists v,
            data_at(field_addr(t, head), v) *
            data_at(field_addr(t, tail), u) * 
            listrep(y) *
            listrep(u) *
            lseg(x, t)
         */
        while (u) {
            t = u;
            u = t->tail;
        }
        t->tail = y;
        return x;
    }
}