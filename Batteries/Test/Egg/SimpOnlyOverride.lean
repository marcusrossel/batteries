import Lean
import Egg
open Lean Meta Elab Parser Tactic

private def unsupported := #[
  "egg requires rewrites to be equalities, equivalences or (non-propositional) definitions",
  "egg does not support using auxiliary declarations"
]

elab "egg_succeeded" : tactic => logWarning "egg succeeded"

elab_rules : tactic
  | `(simp| simp only $[[$lemmas:simpLemma,*]]?) => do
    let simpStx ← if let some lems := lemmas then `(tactic| simp only [$lems,*]) else `(tactic| simp only)
    let mut premises ← simpOnlyBuiltins.toArray.mapM fun b => `(egg_premise|$(mkIdent b):ident)
    if let some lems := lemmas then
      for lem in lems.getElems do
        -- syntax simpLemma := (simpPre <|> simpPost)? patternIgnore("← " <|> "<- ")? term
        let lemTerm : Term := ⟨lem.raw[2]⟩
        premises := premises.push <| ← `(egg_premise|$lemTerm:term)
    focus do
      let s ← saveState
      let goal ← getMainGoal
      evalSimp simpStx
      unless (← getGoals).isEmpty do return
      let some _ ← Egg.Congr.from? (← Egg.normalize (← goal.getType) .noReduce) | return
      s.restore
      try
        evalTactic (← `(tactic|egg [$premises,*]))
        logWarning "egg succeeded"
      catch err =>
        s.restore
        if !unsupported.contains (← err.toMessageData.toString) then
          logWarning m!"egg failed: {err.toMessageData}"
        evalSimp simpStx
