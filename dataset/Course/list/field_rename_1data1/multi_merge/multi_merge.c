struct pred {
    int data;
    struct pred *link;
};

/*@ Let listrep(l) = l == 0 && emp ||
      exists v t, data_at(field_addr(l, data), v) * data_at(field_addr(l, link), t) * listrep(t)
 */
 
/*@ Let lseg(x, y) = x == y && emp ||
      exists v z, data_at(field_addr(x, data), v) * data_at(field_addr(x, link), z) * lseg(z, y)
 */

struct pred *merge(struct pred *x , struct pred *y)
/*@ Require listrep(x) * listrep(y)
    Ensure  listrep(__return)
 */;

struct pred *multi_merge(struct pred *x , struct pred *y, struct pred *z)
/*@ Require listrep(x) * listrep(y) * listrep(z)
    Ensure  listrep(__return)
 */
{
    struct pred *t,*u;
    if (x == 0) {
      t = merge(y,z);
      return t; 
    }
    else {
      t = x;
      u = t->link;
      /*@ exists v,
          data_at(field_addr(t, data), v) * 
          data_at(field_addr(t, link), u) * 
          listrep(y) *
          listrep(z) * 
          listrep(u) *
          lseg(x, t)
      */
      while (u) {
        if (y) {
          t -> link = y;
          t = y;
          y = y -> link;
        }
        else {
          u = merge(u , z);
          t -> link = u;
          return x;   
        }
        if (z) {
          t -> link = z;
          t = z;
          z = z -> link;
        }
        else {
          u = merge(u , y);
          t -> link = u;
          return x;
        }
        t -> link = u;
        t = u;
        u = u -> link;
      }
  }
  t->link = merge(y,z);
  return x;
}