struct list {
    struct list *tail;
};

/*@ Let listrep(l) = l == 0 && emp ||
      exists t, data_at(field_addr(l, tail), t) * listrep(t)
 */
 
/*@ Let lseg(x, y) = x == y && emp ||
      exists z, data_at(field_addr(x, tail), z) * lseg(z, y)
 */

struct list * append(struct list * x, struct list * y)
/*@ Require listrep(x) * listrep(y)
    Ensure  listrep(__return)
 */;

struct list *multi_append(struct list *x, struct list *y, struct list *z)
/*@ Require listrep(x) * listrep(y) * listrep(z)
    Ensure  listrep(__return)
 */
{
    struct list *t, *u;
    if (x == 0) {
        t = append(y , z);
        return t;
    } else {
        t = x;
        u = t->tail;
        /*@ data_at(field_addr(t, tail), u) * 
            listrep(y) *
            listrep(z) * 
            listrep(u) *
            lseg(x, t)
         */
        while (u) {
            if (y) {
              t -> tail = y;
              t = y;
              y = y -> tail;
              t -> tail = u;
              t = u;
              u = u -> tail;
            }
            else {
              u = append(u , z);
              t -> tail = u;
              return x;   
            }
        }
        t->tail = append(y,z);
        return x;
    }
}