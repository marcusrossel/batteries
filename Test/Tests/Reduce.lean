import Egg

-- Tests for manually inspecting what terms look like with the `reduce` option.
set_option trace.egg true

example (a : Nat) (h : ∀ x : Nat, x + 1 = 1 + x) : a + 1 = 1 + a := by
  egg (config := { reduce := true }) [h]

-- This example shows that reduction can already reduce the proof goal to a degree that egg given
-- rewrite rules aren't required any more.
example (x : Nat) (h : ∀ x : Nat, x + 0 = x) : x = x + 0 := by
  egg (config := { reduce := true }) [h]

-- This example shows that reduction can already reduce the proof goal to be trivial.
example (x : Nat) (h : ∀ x : Nat, x.add .zero = x) : x = x.add (Nat.zero.add .zero) := by
  egg [h]
