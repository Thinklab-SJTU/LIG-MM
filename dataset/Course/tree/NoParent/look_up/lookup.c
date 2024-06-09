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

int lookup(struct NFtree* x, int v)
/*@ With v0
    Require v == v0 && NFtree_rep(x)
    Ensure __return == 0 && NFtree_rep(x) || __return == 1 && NFtree_rep(x)
 */
{
    struct NFtree *y;
    if (x == 0) {
        return 0;
    }
    else {
        y = x;
        /*@ (exists u, v == v0 && u == y -> data && 
            NFptree_rep(y, x) *
            NFtree_rep(y -> left) *
            NFtree_rep(y -> right))
        || (exists y_par, v == v0 && y_par -> data > v0 &&
            y_par -> left == y &&  
            NFptree_rep(y_par, x) *
            NFtree_rep(y) *
            NFtree_rep(y_par -> right))
        || (exists y_par, v == v0 && y_par -> data < v0 &&
            y_par -> right == y &&  
            NFptree_rep(y_par, x) *
            NFtree_rep(y) *
            NFtree_rep(y_par -> left))
        */
        while (y) {
            if (y->data == v) {
                return 1;
            }
            else {
              if (y->data < v) {
                y = y->right;
              }
              else {
                y = y->left;
              }
            }
        }
        return 0;
    }
}