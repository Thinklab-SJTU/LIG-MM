struct tree {
    int data;
    struct tree * left;
    struct tree * right;
    struct tree * parent;
};

/*@
  Let tree_rep(p, p_par) = p == 0 && emp ||
  	exists p_data, p -> parent == p_par && p -> data == p_data && 
                   tree_rep(p -> left, p) * tree_rep(p -> right, p)
 */

/*@
  Let ptree_rep(p, p_par, p_root, p_top) = p == p_root && p_par == p_top && emp ||
  	exists ppar_data, 
              p_par -> left == p && p_par -> data == ppar_data && 
              tree_rep(p_par -> right, p_par) * ptree_rep(p_par, p_par -> parent, p_root, p_top) ||
    exists ppar_data,
              p_par -> right == p && p_par -> data == ppar_data && 
              tree_rep(p_par -> left, p_par) * ptree_rep(p_par, p_par -> parent, p_root, p_top)  
*/

int lookup(struct tree* x, int v)
/*@ With x_par v0
    Require v == v0 && tree_rep(x, x_par)
    Ensure __return == 0 && tree_rep(x, x_par) || __return == 1 && tree_rep(x, x_par)
 */
{
    struct tree *y;
    if (x == 0) {
        return 0;
    }
    else {
        y = x;
        /*@ (exists u, v == v0 && u == y -> data && 
            ptree_rep(y, y->parent, x, x_par) *
            tree_rep(y -> left, y) *
            tree_rep(y -> right, y))
        || (exists y_par, v == v0 && y_par -> data > v0 &&
            y_par -> left == y &&  
            ptree_rep(y_par, y_par -> parent, x, x_par) *
            tree_rep(y, y_par) *
            tree_rep(y_par -> right, y_par))
        || (exists y_par, v == v0 && y_par -> data < v0 &&
            y_par -> right == y &&  
            ptree_rep(y_par, y_par -> parent, x, x_par) *
            tree_rep(y, y_par) *
            tree_rep(y_par -> left, y_par))
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