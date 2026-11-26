/-
  Collatz: the three small results from our conversation, machine-checked.
  Plain Lean 4, no Mathlib needed.

  1. n = 4m + 1 (m ≥ 1) drops below itself in 3 steps.
  2. n = 16m + 3 drops below itself in 6 steps.
  3. Numbers ending in j ones in binary (n = 2^j·b − 1) never drop
     during the first j "odd" steps, so the mod-2^k method can never
     finish the proof on its own.
-/

/-- One Collatz step. -/
def collatz (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

theorem step_even {n : Nat} (h : n % 2 = 0) : collatz n = n / 2 := by
  simp [collatz, h]

theorem step_odd {n : Nat} (h : n % 2 = 1) : collatz n = 3 * n + 1 := by
  simp [collatz, h]

/-! ## Result 1: n ≡ 1 (mod 4) drops below itself -/

theorem descent_4m1 (m : Nat) (hm : 1 ≤ m) :
    collatz (collatz (collatz (4 * m + 1))) < 4 * m + 1 := by
  have h1 : collatz (4 * m + 1) = 12 * m + 4 := by
    rw [step_odd (n := 4 * m + 1) (by omega)]; omega
  have h2 : collatz (12 * m + 4) = 6 * m + 2 := by
    rw [step_even (n := 12 * m + 4) (by omega)]; omega
  have h3 : collatz (6 * m + 2) = 3 * m + 1 := by
    rw [step_even (n := 6 * m + 2) (by omega)]; omega
  rw [h1, h2, h3]; omega

/-! ## Result 2: n ≡ 3 (mod 16) drops below itself (every m, including m = 0) -/

theorem descent_16m3 (m : Nat) :
    collatz (collatz (collatz (collatz (collatz (collatz (16 * m + 3)))))) < 16 * m + 3 := by
  have h1 : collatz (16 * m + 3) = 48 * m + 10 := by
    rw [step_odd (n := 16 * m + 3) (by omega)]; omega
  have h2 : collatz (48 * m + 10) = 24 * m + 5 := by
    rw [step_even (n := 48 * m + 10) (by omega)]; omega
  have h3 : collatz (24 * m + 5) = 72 * m + 16 := by
    rw [step_odd (n := 24 * m + 5) (by omega)]; omega
  have h4 : collatz (72 * m + 16) = 36 * m + 8 := by
    rw [step_even (n := 72 * m + 16) (by omega)]; omega
  have h5 : collatz (36 * m + 8) = 18 * m + 4 := by
    rw [step_even (n := 36 * m + 8) (by omega)]; omega
  have h6 : collatz (18 * m + 4) = 9 * m + 2 := by
    rw [step_even (n := 18 * m + 4) (by omega)]; omega
  rw [h1, h2, h3, h4, h5, h6]; omega

/-! ## Result 3: the all-ones classes never drop

We use the shortcut map T, where an odd step and the halving that always
follows it count as one step: T n = (3n + 1) / 2 for odd n. -/

def T (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-- T really is "odd step, then halve" in terms of the original map. -/
theorem T_odd {n : Nat} (h : n % 2 = 1) : T n = collatz (collatz n) := by
  unfold T
  rw [step_odd h, step_even (n := 3 * n + 1) (by omega)]
  simp [h]

/-- Apply T j times. -/
def iterT : Nat → Nat → Nat
  | 0, n => n
  | j + 1, n => iterT j (T n)

/-- One shortcut step on 2^(j+1)·b − 1 gives 2^j·(3b) − 1: one fewer trailing 1, but 3× bigger. -/
theorem T_ones (j b : Nat) (hb : 0 < b) :
    T (2 ^ (j + 1) * b - 1) = 2 ^ j * (3 * b) - 1 := by
  have hx : 0 < 2 ^ j * b := Nat.mul_pos (Nat.two_pow_pos j) hb
  have e1 : 2 ^ (j + 1) * b = 2 * (2 ^ j * b) := by
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ j) 2, Nat.mul_assoc]
  have e2 : 2 ^ j * (3 * b) = 3 * (2 ^ j * b) := Nat.mul_left_comm _ _ _
  rw [e1, e2]
  generalize 2 ^ j * b = x at *
  unfold T
  split <;> omega

/-- Closed form: j shortcut steps turn 2^j·b − 1 into 3^j·b − 1. -/
theorem iterT_ones (j : Nat) : ∀ b, 0 < b → iterT j (2 ^ j * b - 1) = 3 ^ j * b - 1 := by
  induction j with
  | zero => intro b _; simp [iterT]
  | succ j ih =>
    intro b hb
    show iterT j (T (2 ^ (j + 1) * b - 1)) = 3 ^ (j + 1) * b - 1
    rw [T_ones j b hb, ih (3 * b) (by omega), Nat.pow_succ, Nat.mul_assoc]

/-- After j steps, 2^j·b − 1 is at least as big as where it started. -/
theorem ones_grow (j b : Nat) (hb : 0 < b) :
    2 ^ j * b - 1 ≤ iterT j (2 ^ j * b - 1) := by
  rw [iterT_ones j b hb]
  have hp : 2 ^ j ≤ 3 ^ j := Nat.pow_le_pow_left (by decide) j
  have hm : 2 ^ j * b ≤ 3 ^ j * b := Nat.mul_le_mul_right b hp
  omega

/-- Main result 3: if n ends in at least j ones in binary (n = 2^j·b − 1),
    then n never drops below itself during the first j shortcut steps. -/
theorem ones_never_drop (j b i : Nat) (hb : 0 < b) (hi : i ≤ j) :
    2 ^ j * b - 1 ≤ iterT i (2 ^ j * b - 1) := by
  have e : 2 ^ j * b = 2 ^ i * (2 ^ (j - i) * b) := by
    rw [← Nat.mul_assoc, ← Nat.pow_add, Nat.add_sub_of_le hi]
  rw [e]
  exact ones_grow i _ (Nat.mul_pos (Nat.two_pow_pos _) hb)

/-! ## Sanity checks and audit -/

#eval (List.range 111).foldl (fun n _ => collatz n) 27   -- 27 reaches 1 after 111 steps
#eval iterT 5 (2 ^ 5 * 1 - 1)                            -- 31 → 3^5 − 1 = 242

-- Should list only standard axioms (propext, Quot.sound, …) and never `sorryAx`.
#print axioms descent_4m1
#print axioms descent_16m3
#print axioms ones_never_drop
