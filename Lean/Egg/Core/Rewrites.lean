import Egg.Core.Directions
import Egg.Core.MVars.Subst
import Egg.Core.MVars.Ambient
import Egg.Core.Normalize
import Egg.Core.Congr
import Egg.Core.Source
import Egg.Lean
open Lean Meta

namespace Egg.Rewrite

structure _root_.Egg.Rewrite extends Congr where
  private mk ::
  proof    : Expr
  src      : Source
  lhsMVars : MVars
  rhsMVars : MVars
  deriving Inhabited

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
def from?
    (proof : Expr) (type : Expr) (src : Source) (normalize : Option Config.Normalization)
    (amb : MVars.Ambient) : MetaM (Option Rewrite) := do
  let mut (args, _, type) ← forallMetaTelescope (← instantiateMVars type)
  type ← if let some cfg := normalize then Egg.normalize type cfg else pure type
  let proof := mkAppN proof args
  let some cgr ← Congr.from? type | return none
  let lhsMVars := (← MVars.collect cgr.lhs).remove amb
  let rhsMVars := (← MVars.collect cgr.rhs).remove amb
  catchLooseArgs args lhsMVars rhsMVars
  return some { cgr with proof, src, lhsMVars, rhsMVars }
where
  catchLooseArgs (args : Array Expr) (lhsMVars rhsMVars : MVars) : MetaM Unit := do
    for arg in args do
      if lhsMVars.expr.contains arg.mvarId! then continue
      if rhsMVars.expr.contains arg.mvarId! then continue
      throwError m!"Rewrite {src.description} contains loose argument."

def validDirs (rw : Rewrite) : Directions :=
  let exprDirs := Directions.satisfyingSuperset rw.lhsMVars.expr rw.rhsMVars.expr
  let lvlDirs  := Directions.satisfyingSuperset rw.lhsMVars.lvl rw.rhsMVars.lvl
  exprDirs.meet lvlDirs

-- Returns the same rewrite but with its type and proof potentially flipped to match the given
-- direction.
def forDir (rw : Rewrite) : Direction → MetaM Rewrite
  | .forward  => return rw
  | .backward => return { rw with lhs := rw.rhs, rhs := rw.lhs, proof := ← rw.rel.mkSymm rw.proof }

def eqProof (rw : Rewrite) : MetaM Expr := do
  match rw.rel with
  | .eq  => return rw.proof
  | .iff => mkPropExt rw.proof

def freshWithSubst (rw : Rewrite) (src : Source := rw.src) : MetaM (Rewrite × MVars.Subst) := do
  let (lhsMVars, subst) ← rw.lhsMVars.fresh
  let (rhsMVars, subst) ← rw.rhsMVars.fresh (init := subst)
  let rw' := { rw with
    lhs   := subst.apply rw.lhs
    rhs   := subst.apply rw.rhs
    proof := subst.apply rw.proof
    src, lhsMVars, rhsMVars
  }
  return (rw', subst)

-- Returns the same rewrite but with all (expression and level) mvars replaced by fresh mvars. This
-- is used during proof reconstruction, as rewrites may be used multiple times but instantiated
-- differently. If we don't use fresh mvars, the mvars will already be assigned and new assignment
-- (via `isDefEq`) will fail.
def fresh (rw : Rewrite) (src : Source := rw.src) : MetaM Rewrite :=
  Prod.fst <$> rw.freshWithSubst src

def instantiateMVars (rw : Rewrite) : MetaM Rewrite :=
  return { rw with
    lhs      := ← Lean.instantiateMVars rw.lhs
    rhs      := ← Lean.instantiateMVars rw.rhs
    proof    := ← Lean.instantiateMVars rw.proof
    lhsMVars := ← rw.lhsMVars.removeAssigned
    rhsMVars := ← rw.rhsMVars.removeAssigned
  }

end Rewrite

abbrev Rewrites := Array Rewrite

-- TODO: This is unnecessarilly inefficient during proof reconstruction, so at some point we may
--       want to redefine `Rewrites` using a better suited data structure.
def Rewrites.find? (rws : Rewrites) (src : Source) : Option Rewrite :=
  Array.find? rws (·.src == src)
