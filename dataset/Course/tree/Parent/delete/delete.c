struct tree {
    int data;
    struct tree * left;
    struct tree * right;
    struct tree * parent;
    // malloc_info: 以后可以加上，使其通用化
};

/*@
  Let tree_rep(p, p_par) = p == 0 && emp ||
  	exists p_lch p_rch p_data, data_at(field_addr(p, left), p_lch) * 
                        data_at(field_addr(p, right), p_rch) * 
                        data_at(field_addr(p, parent), p_par) *
                        data_at(field_addr(p, data), p_data) * 
                        tree_rep(p_lch, p) *
                        tree_rep(p_rch, p)
 */

/*@
  Let ptree_rep(p, p_par, p_root, p_top) = p == p_root && p_par == p_top && emp ||
  	exists ppar_rch ppar_par ppar_data, 
                        data_at(field_addr(p_par, left), p) * 
                        data_at(field_addr(p_par, right), ppar_rch) * 
                        data_at(field_addr(p_par, parent), ppar_par) * 
                        data_at(field_addr(p_par, data), ppar_data) *
                        tree_rep(ppar_rch, p_par) *
                        ptree_rep(p_par, ppar_par, p_root, p_top) ||
    exists ppar_lch ppar_par ppar_data, 
                        data_at(field_addr(p_par, left), ppar_lch) * 
                        data_at(field_addr(p_par, right), p) * 
                        data_at(field_addr(p_par, parent), ppar_par) * 
                        data_at(field_addr(p_par, data), ppar_data) *
                        tree_rep(ppar_lch, p_par) *
                        ptree_rep(p_par, ppar_par, p_root, p_top) 
*/

// free_tree: 针对 tree 的 free 操作

void free_tree (struct tree *p)
/*@ With d p_lch p_rch p_par
    Require data_at(field_addr(p, data), d) *
            data_at(field_addr(p, left), p_lch) *
            data_at(field_addr(p, right), p_rch) *
            data_at(field_addr(p, parent), p_par)
    Ensure  emp
 */;

struct tree * delete(struct tree* x, int v)
/*@ With x_par
    Require tree_rep(x, x_par)
    Ensure tree_rep(__return, x_par)
 */
{
    struct tree *y, *t, *u, *w;
    if (x == 0) {
        return x;
    }
    else {
        y = x;
        u = x -> parent;
        /*@ exists v0, v0 == y -> data &&
            u == y -> parent &&  
            ptree_rep(y, y->parent, x, x_par) *
            tree_rep(y -> left, y) *
            tree_rep(y -> right, y)
        || u->data > v && y == u -> left &&
           ptree_rep(u, u -> parent, x, x_par) *
           tree_rep(u->right, u) *
           tree_rep(y, u)
        || u->data < v && y == u -> right && 
            ptree_rep(u, u -> parent, x, x_par) *
            tree_rep(u->left, u) *
            tree_rep(y, u)
        */
        while (y) { 
            if (y->data < v) {
              u = y;
              y = y->right;
            }
            else {
              if (y->data > v) {
                u = y;
                y = y->left;
              }
              else {
                u = y -> parent;
                if (y->right == 0) {
                  t = y->left;
                }
                else {
                  t = y -> right;
                  if (y -> left != 0) {
                    w = y;
                    /*@ 
                      exists v0, t -> data == v0 && w == y && w == t -> parent && 
                      y -> data == v && y -> left != 0 && y -> right == t &&
                      u -> right == y && u -> data < v && y -> parent == u && 
                      ptree_rep(u, u -> parent, x, x_par) * 
                      tree_rep(u -> left, u) * tree_rep(y -> left,y) *  
                      tree_rep(t -> left,t) *
                      tree_rep(t -> right,t)
                    || 
                      exists v0, t -> data == v0 && w == y && w == t -> parent && 
                      y -> data == v && y -> left != 0 && y -> right == t &&
                      u -> left == y && u -> data > v && y -> parent == u && 
                      ptree_rep(u, u -> parent, x, x_par) * 
                      tree_rep(u -> right, u) * tree_rep(y -> left,y) *  
                      tree_rep(t -> left,t) *
                      tree_rep(t -> right,t)
                    ||
                      exists v0 v1, t -> data == v0 && w != y && w == t -> parent &&
                      t == w -> left && w -> data == v1 &&  
                      y -> data == v && y -> left != 0 && y -> right != 0 &&
                      u -> right == y && u -> data < v && y -> parent == u && 
                      ptree_rep(u, u -> parent, x, x_par) * 
                      tree_rep(u -> left, u) * tree_rep(y -> left,y) * 
                      ptree_rep(w, w -> parent,y -> right,y) * tree_rep(w -> right,y) * 
                      tree_rep(t -> left,t) * 
                      tree_rep(t -> right,t)
                    ||
                      exists v0 v1, t -> data == v0 && w != y && w == t -> parent &&
                      t == w -> left && w -> data == v1 &&  
                      y -> data == v && y -> left != 0 && y -> right != 0 &&
                      u -> left == y && u -> data > v && y -> parent == u &&
                      ptree_rep(u, u -> parent, x, x_par) * 
                      tree_rep(u -> right,u) * tree_rep(y -> left,y) * 
                      ptree_rep(w, w -> parent,y -> right,y) * tree_rep(w -> right,y) *
                      tree_rep(t -> left,t) *
                      tree_rep(t -> right,t)
                    */
                    while (t->left) {
                      w = t;
                      t = t->left;
                    }
                    y -> data = t -> data;
                    if (t == w -> left) {
                      w -> left = t -> right;
                    }
                    if (t == w -> right) {
                      w -> right = t -> right;
                    }
                    if (t -> right) {
                      t -> right -> parent = w;
                    }
                    free_tree(t);
                    return x;
                  }
              }
              free_tree(y);
              if (t) {
                t -> parent = u;
              }
              if (u->left == y) {
                  u->left = t;
              }
              if (u -> right == y) {
                u->right = t;
              }
              return x;
          }
        }       
    }
    return x;
  }
}