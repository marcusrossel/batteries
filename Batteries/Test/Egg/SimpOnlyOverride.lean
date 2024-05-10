import Lean
import EggTactic
open Lean Meta Elab Parser Tactic

elab_rules : tactic
  | `(simp| simp only $[[$lemmas:simpLemma,*]]?) => do
    let simpStx ← if let some lems := lemmas then `(tactic| simp only [$lems,*]) else `(tactic| simp only)
    let mut premises := simpOnlyBuiltins.toArray.map Lean.mkIdent
    if let some lems := lemmas then
      for lem in lems.getElems do
        -- syntax simpLemma := (simpPre <|> simpPost)? patternIgnore("← " <|> "<- ")? term
        premises := premises.push ⟨lem.raw[2]⟩
    focus do
      let s ← saveState
      let goal ← getMainGoal
      evalSimp simpStx
      unless (← getGoals).isEmpty do return
      unless (← goal.getType).eq?.isSome do return
      s.restore
      try
        evalTactic (← `(tactic|egg [$premises,*]))
        logWarning "egg succeeded"
      catch err =>
        s.restore
        logWarning m!"egg failed: {err.toMessageData}"
        evalSimp simpStx
