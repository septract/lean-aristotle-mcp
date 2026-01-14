/-
Basic definitions for our test project.
-/

/-- A natural number is even if it's divisible by 2 -/
def even (n : Nat) : Prop := ∃ k, n = 2 * k

/-- A natural number is odd if it's not even -/
def odd (n : Nat) : Prop := ∃ k, n = 2 * k + 1

/-- Double a number -/
def double (n : Nat) : Nat := 2 * n

/-- Square a number -/
def square (n : Nat) : Nat := n * n
