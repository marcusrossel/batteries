import Egg

/-- error: Rewrite #0 contains loose argument. -/
#guard_msgs in
example (h : ∀ n : Nat, n > 2 → n = 5) : x = 5 := by
  egg [h]
