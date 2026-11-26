/-
  Collatz worksheet, Part E.
  Replace `sorry` with a proof. Use `descent_16m3` in ../Collatz.lean as a model:
  one `have` per step, each proved with `step_odd` or `step_even` and `omega`.
  Check it with:  lean Exercise.lean
-/

def collatz (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

theorem step_even {n : Nat} (h : n % 2 = 0) : collatz n = n / 2 := by
  simp [collatz, h]

theorem step_odd {n : Nat} (h : n % 2 = 1) : collatz n = 3 * n + 1 := by
  simp [collatz, h]

/-- Worksheet D1: 32m + 11 drops below itself after 8 steps. -/
theorem descent_32m11 (m : Nat) :
    collatz (collatz (collatz (collatz (collatz (collatz (collatz (collatz (32 * m + 11))))))))
      < 32 * m + 11 := by
  sorry

#print axioms descent_32m11
