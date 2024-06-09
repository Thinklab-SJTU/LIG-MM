struct list {
    int head;
    struct list *tail;
};

/*@ Let listrep(l) = l == 0 && emp ||
      exists v t, data_at(field_addr(l, head), v) * data_at(field_addr(l, tail), t) * listrep(t)
 */
 
/*@ Let lseg(x, y) = x == y && emp ||
      exists v z, data_at(field_addr(x, head), v) * data_at(field_addr(x, tail), z) * lseg(z, y)
 */

struct list *rev_append(struct list *p, struct list *q)
/*@ Require p != q && listrep(p) * listrep(q)
    Ensure  listrep(__return)
 */
{
    struct list *w, *t, *v;
    w = q;
    v = p;
    /*@ lseg(w, q) * listrep(v) * listrep(q) */
    while (v) {
      t = v->tail;
      v->tail = w;
      w = v;
      v = t;
    }
    return w;
}