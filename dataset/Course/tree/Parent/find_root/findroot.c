struct tree {
    int data;
    struct tree * left;
    struct tree * right;
    struct tree * parent;
};

/*@
  Let tree_rep(p, p_par) = p == 0 && emp ||
  	exists p_lch p_rch p_data, 
                        data_at(field_addr(p, left), p_lch) * 
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


struct tree *Find_root(struct tree * x)
/*@ With __1 root
    Require x != 0 && tree_rep(x, __1) * ptree_rep(x, __1, root, 0)
    Ensure tree_rep(__return , 0)
 */
{
    /*@ exists xson, x != 0 && tree_rep(xson , x) * ptree_rep(xson, x, root, 0) */
    while (x -> parent) 
      x = x -> parent;
    return x;
}