import Egg.Core.Premise.Facts
import Egg.Core.Premise.Rewrites
import Lean
open Lean Meta

namespace Egg

inductive Premise where
  | rw   (rw : Rewrite)
  | fact (f : Fact)

namespace Premise

-- Note: It isn't sufficient to take the `args` as a rewrite's holes, as implicit arguments will
--       already be instantiated as mvars during type inference. For example, the type of
--       `theorem t : ∀ {x}, x + 0 = 0 + x := Nat.add_comm _ _` will be directly inferred as
--       `?x + 0 = 0 + ?x`. On the other hand, we might be collecting too many mvars right now as a
--       rewrite could possibly contain mvars which weren't quantified (e.g. if it comes from the
--       local context). Also, we need to "catch loose args", that is, those which are preconditions
--       for the rewrite, but don't appear in the body (as in conditional rewrites).
--
-- Note: We must instantiate mvars of the rewrite's type. For an example that breaks otherwise, see
--       leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Different.20elab.20results
def «from»
    (proof : Expr) (type : Expr) (src : Source) (normalize : Option Config.Normalization)
    (amb : MVars.Ambient) : MetaM Premise := do
  let mut (args, _, type) ← forallMetaTelescope (← instantiateMVars type)
  type ← if let some cfg := normalize then Egg.normalize type cfg else pure type
  let proof := mkAppN proof args
  let some cgr ← Congr.from? type | return .fact { src, type, proof }
  let mLhs := (← MVars.collect cgr.lhs).remove amb
  let mRhs := (← MVars.collect cgr.rhs).remove amb
  let conds ← collectConds args mLhs mRhs
  let mvars := { lhs := mLhs, rhs := mRhs }
  return .rw { cgr with proof, src, conds, mvars }
where
  collectConds (args : Array Expr) (mLhs mRhs : MVars) : MetaM (Array Rewrite.Condition) := do
    let mut conds := #[]
    for arg in args do
      if mLhs.expr.contains arg.mvarId! || mRhs.expr.contains arg.mvarId! then continue
      let ty ← instantiateMVars (← arg.mvarId!.getType) -- TODO: Does this need to be normalized?
      conds := conds.push { expr := arg, type := ty, mvars := (← MVars.collect ty).remove amb }
    return conds
