/-
Arithmetic theorems to prove.
-/
import TestProject.Basic
import Mathlib.Tactic

/-- Zero is even -/
theorem zero_even : even 0 := by
  sorry

/-- The sum of two even numbers is even -/
theorem even_add_even (a b : Nat) (ha : even a) (hb : even b) : even (a + b) := by
  sorry

/-- Double of any number is even -/
theorem double_even (n : Nat) : even (double n) := by
  sorry

/-- Simple arithmetic fact -/
theorem add_comm_example (x y : Nat) : x + y = y + x := by
  sorry
