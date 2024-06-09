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

struct SNnode *reverse(struct SNnode *p)
/*@ Require listrep(p)
    Ensure  listrep(__return)
 */
{
    struct SNnode *w, *t, *v;
    w = 0;
    v = p;
    /*@ listrep(w) * listrep(v) */
    while (v) {
        t = v->tail;
        v->tail = w;
        w = v;
        v = t;
    }
    return w;
}