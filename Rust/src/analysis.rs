use std::collections::HashSet;
use egg::*;
use crate::lean_expr::*;
use crate::util::*;

#[derive(Debug, Default)]
pub struct LeanAnalysisData {
    pub nat_val:      Option<u64>,
    pub dir_val:      Option<bool>,
    pub loose_bvars:  HashSet<u64>, // A bvar is in this set only iff it is referenced by *some* e-node in the e-class.
    pub is_primitive: bool          // A class is primitive if it represents a `Nat`, `Str` or universe level e-node.
}

#[derive(Default)]
pub struct LeanAnalysis;
impl Analysis<LeanExpr> for LeanAnalysis {
    type Data = LeanAnalysisData;

    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {       
        // `merge_max` prefers `Some` value over `None`. Note that if `to` and `from` both have nat values,
        // then they should have the *same* value as otherwise merging their e-classes indicates an invalid 
        // rewrite. The same applies for the `dir_val`s.
        egg::merge_max(&mut to.nat_val, from.nat_val) | 
        egg::merge_max(&mut to.dir_val, from.dir_val) | 
        union_sets(&mut to.loose_bvars, from.loose_bvars) |
        egg::merge_max(&mut to.is_primitive, from.is_primitive)
    }

    fn make(egraph: &EGraph<LeanExpr, Self>, enode: &LeanExpr) -> Self::Data {      
        match enode {
            LeanExpr::Nat(n) => 
                Self::Data { 
                    nat_val: Some(*n), 
                    is_primitive: true,
                    ..Default::default() 
                },
            
            LeanExpr::Str(shift_up) if shift_up == "+" => 
                Self::Data { 
                    dir_val: Some(true), 
                    is_primitive: true,
                    ..Default::default() 
                },
            
            LeanExpr::Str(shift_down) if shift_down == "-" => 
                Self::Data { 
                    dir_val: Some(false), 
                    is_primitive: true,
                    ..Default::default() 
                },

            LeanExpr::Str(_) | LeanExpr::Fun(_) | LeanExpr::UVar(_) | LeanExpr::Param(_) | 
            LeanExpr::Succ(_) | LeanExpr::Max(_) | LeanExpr::IMax(_) => 
                Self::Data { 
                    is_primitive: true,
                    ..Default::default() 
                },
            
            LeanExpr::BVar(idx) => 
                Self::Data { 
                    loose_bvars: match egraph[*idx].data.nat_val { 
                        Some(n) => vec![n].into_iter().collect(),
                        None    => HashSet::new()
                    }, 
                    ..Default::default() 
                },
            
            LeanExpr::App([fun, arg]) => 
                Self::Data { 
                    loose_bvars: union_clone(&egraph[*fun].data.loose_bvars, &egraph[*arg].data.loose_bvars),
                    ..Default::default() 
                },
            
            LeanExpr::Lam([ty, body]) | LeanExpr::Forall([ty, body]) =>
                Self::Data { 
                    loose_bvars: union_clone(
                        &egraph[*ty].data.loose_bvars, 
                        &shift_down(&egraph[*body].data.loose_bvars)
                    ), 
                    ..Default::default() 
                },

            LeanExpr::Subst([idx, to, e]) => {
                let mut loose_bvars = egraph[*e].data.loose_bvars.clone();
                loose_bvars.remove(&egraph[*idx].data.nat_val.unwrap());
                loose_bvars.extend(&egraph[*to].data.loose_bvars);
                Self::Data { loose_bvars, ..Default::default() }
            },
            
            LeanExpr::Shift([dir, off, cut, e]) => {
                // Determine if we have a self-loop for the shift-node. If so, 
                // the shift-node must be in an e-class where some node contains 
                // no loose bvars. Thus, all other loose bvars which appear under 
                // the given e-class must be redundant. Our current handling of 
                // this situation is then to not add any shift-nodes to `e` in 
                // `shift.rs`, so we also opt to not change the set of loose bvars 
                // here. This might not be the correct approach.
                if let Some(enode_class) = egraph.lookup(enode.clone()) {
                    if egraph.find(enode_class) == egraph.find(*e) { 
                        return Self::Data { loose_bvars: egraph[*e].data.loose_bvars.clone(), ..Default::default() }
                    }
                }

                let &dir_is_up = &egraph[*dir].data.dir_val.unwrap();
                let &off = &egraph[*off].data.nat_val.unwrap();
                let &cut = &egraph[*cut].data.nat_val.unwrap();
                let mut loose_bvars: HashSet<u64> = Default::default();
                for &b in egraph[*e].data.loose_bvars.iter() {
                    if b < cut {
                        loose_bvars.insert(b);
                    } else if dir_is_up {
                        loose_bvars.insert(b + off);
                    } else if off <= b {
                        // If `off > b`, this shift was "not intended", so we just don't do it. 
                        loose_bvars.insert(b - off);
                    }
                }
                Self::Data { loose_bvars, ..Default::default() }
            },

            LeanExpr::Shaped([_, e]) | LeanExpr::Proof(e)  =>
                Self::Data { loose_bvars: egraph[*e].data.loose_bvars.clone(), ..Default::default() },

            _ => Default::default()
        }
    }
}

pub type LeanEGraph = EGraph<LeanExpr, LeanAnalysis>;
pub type LeanRewrite = Rewrite<LeanExpr, LeanAnalysis>;