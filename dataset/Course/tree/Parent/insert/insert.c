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

struct tree * malloc_tree(void)
/*@ Require emp
    Ensure __return -> left == 0 && 
           __return -> right == 0 && 
           __return -> parent == 0 && 
           __return -> data == 0 && emp
 */;

struct tree * insert(struct tree* x, int v)
/*@ With v0
    Require v == v0 && tree_rep(x, 0)
    Ensure tree_rep(__return, 0)
 */
{
    struct tree * y, * t;
    if (x == 0) {
        x = malloc_tree();
        x->data = v;
        return x;
    }
    else {
        y = x;
        t = y->parent;
        /*@ (exists u,
            v == v0 && !(y == 0) &&  
            y -> parent == t && 
            y -> data == u && 
            ptree_rep(y, t, x, 0) *
            tree_rep(y -> left , y) *
            tree_rep(y -> right, y))
        || (v == v0 && t -> data > v0 &&
            t -> left == y && 
            ptree_rep(t, t -> parent, x, 0) *
            tree_rep(y, t) *
            tree_rep(t -> right, t))
        || (v == v0 && t -> data < v0 &&
            t -> right == y && 
            ptree_rep(t, t -> parent, x, 0) *
            tree_rep(y, t) *
            tree_rep(t -> left, t))
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
        y->parent = t;
        if (t->data < v) {
            t->right = y;
        }
        else {
            t->left = y;
        }
        return x;
    }
}