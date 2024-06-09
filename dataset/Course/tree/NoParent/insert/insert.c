struct NFtree {
    int data;
    struct NFtree * left;
    struct NFtree * right;
};

/*@
  Let NFtree_rep(p) = p == 0 && emp ||
  	exists p_data, p -> data == p_data && 
                   NFtree_rep(p -> left) * NFtree_rep(p -> right)
 */

/*@
  Let NFptree_rep(p, p_root) = p == p_root && emp ||
  	exists p_par ppar_data, 
              p_par -> left == p && p_par -> data == ppar_data && 
              NFtree_rep(p_par -> right) * NFptree_rep(p_par, p_root) ||
    exists p_par ppar_data,
              p_par -> right == p && p_par -> data == ppar_data && 
              NFtree_rep(p_par -> left) * NFptree_rep(p_par, p_root)  
*/

struct NFtree * malloc_NFtree(void)
/*@ Require emp
    Ensure __return -> left == 0 && 
           __return -> right == 0 && 
           __return -> data == 0 && emp
 */;

struct NFtree * insert(struct NFtree* x, int v)
/*@ With v0
    Require v == v0 && NFtree_rep(x)
    Ensure NFtree_rep(__return)
 */
{
    struct NFtree * y, * t;
    if (x == 0) {
        x = malloc_tree();
        x->data = v;
        return x;
    }
    else {
        y = x;
        /*@ (exists u,
            v == v0 && !(y == 0) &&   
            y -> data == u && 
            NFptree_rep(y, x) *
            NFtree_rep(y -> left) *
            NFtree_rep(y -> right))
        || (v == v0 && t -> data > v0 &&
            t -> left == y && 
            NFptree_rep(t, x) *
            NFtree_rep(y) *
            NFtree_rep(t -> right))
        || (v == v0 && t -> data < v0 &&
            t -> right == y && 
            NFptree_rep(t,x) *
            NFtree_rep(y) *
            NFtree_rep(t -> left))
        */
        while (y) {
            t = y;
            if (y->data < v) {
                y = y->right;
            }
            else {
              if (y->data > v) {
                y = y->left;
              }
              else {
                return x;
              }
            }
        }
        y = malloc_tree();
        y->data = v;
        if (t->data < v) {
            t->right = y;
        }
        else {
            t->left = y;
        }
        return x;
    }
}