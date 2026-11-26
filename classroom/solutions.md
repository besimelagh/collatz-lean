# Collatz worksheet: solutions

## Part A

**A1.** 6 → 3 → 10 → 5 → 16 → 8 → 4 → 2 → 1. That is **8 steps**.

**A2.** 7 → 22 → 11 → 34 → 17 → 52 → 26 → 13 → 40 → 20 → 10 → 5 → 16 → 8 → 4 → 2 → 1.
That is **16 steps**, and the largest value is **52**.

**A3.** Neighbouring starting values can behave completely differently, so there is no simple formula
for the number of steps. This is one reason the problem is hard.

## Part B

**B1.** If n is even, the first step gives n/2, which is less than n.

**B2.** Suppose some number never reaches 1, and let N be the smallest such number. N > 1, so by
assumption N drops: its sequence reaches some k < N. Because k is smaller than N, k reaches 1. But the
sequence from N passes through k, so N reaches 1 too. That contradicts the choice of N, so every
number reaches 1.

**B3.**

| Step | Value | Odd or even? |
|---|---|---|
| 0 | 4m + 1 | odd (4m is even) |
| 1 | 12m + 4 | even |
| 2 | 6m + 2 | even |
| 3 | 3m + 1 | |

3m + 1 < 4m + 1 whenever m ≥ 1.

**B4.** Even numbers are 1/2 of all integers and numbers of the form 4m + 1 are another 1/4, so
**3/4** of all numbers drop (apart from n = 1 itself, which is already at the end).

## Part C

**C1.**

| Step | Value | Odd or even? |
|---|---|---|
| 0 | 16m + 3 | odd |
| 1 | 48m + 10 | even |
| 2 | 24m + 5 | odd |
| 3 | 72m + 16 | even |
| 4 | 36m + 8 | even |
| 5 | 18m + 4 | even |
| 6 | 9m + 2 | |

9m + 2 < 16m + 3 for every m ≥ 0, because 7m + 1 > 0.

**C2.** 16m + 7 → 48m + 22 → 24m + 11 → 72m + 34 → 36m + 17 → 108m + 52 → 54m + 26 → **27m + 13**.
Whether 27m + 13 is odd or even depends on m, so we can't continue without splitting into cases.
27m + 13 is *bigger* than 16m + 7, so nothing is proved yet.

**C3.** 3²/2⁴ = 9/16. The coefficient of m went from 16 to 9, so for large m the value has shrunk to
about 9/16 of the start. A product below 1 means the sequence ends up smaller than where it began.

## Part D

**D1.** 32m + 11 → 96m + 34 → 48m + 17 → 144m + 52 → 72m + 26 → 36m + 13 → 108m + 40 → 54m + 20 →
**27m + 10**. The steps are odd, even, odd, even, even, odd, even, even, the same for every m.
27m + 10 < 32m + 11 for every m ≥ 0.

**D2.** 32m + 23 → 96m + 70 → 48m + 35 → 144m + 106 → 72m + 53 → 216m + 160 → 108m + 80 → 54m + 40 →
**27m + 20**, and 27m + 20 < 32m + 23 for every m ≥ 0.

So mod 32 the survivors are 7, 15, 27 and 31: 4 of the 32 classes, or 12.5%.

**D3.** 7 = 111₂, 15 = 1111₂, 31 = 11111₂. They are all of the form 2ᵏ − 1: every binary digit is 1.

**D4.** 31 → 47 → 71 → 107 → 161 → 242. The values 31, 47, 71, 107 and 161 are all odd, and
242 = 243 − 1 = 3⁵ − 1.

**D5.** n = 2ᵏ·b − 1 is odd because k ≥ 1. So
T(n) = (3n + 1)/2 = (3·2ᵏ·b − 2)/2 = 3·2ᵏ⁻¹·b − 1 = 2ᵏ⁻¹·(3b) − 1.

The result has the same shape with k − 1 in place of k, so the argument repeats. After k shortcut
steps, n = 2ᵏ·b − 1 has become 3ᵏ·b − 1, and every intermediate value was bigger than the one before.

Now take the class n ≡ 2ᵏ − 1 (mod 2ᵏ), that is, n = 2ᵏ·b − 1. The last k binary digits only decide
the first k steps, and in this class those steps all grow the number. So when you check remainders
mod 2ᵏ, this class is never shown to drop, for every k.

**D6.** Checking remainders mod 2ᵏ only uses the last k binary digits of n, so it can only predict
finitely many steps. At every level there are classes (such as the all-ones class) whose first k
steps grow the number, so they are never resolved. The fraction of unresolved numbers shrinks to 0,
but "almost all numbers drop" is weaker than "every number drops", and a single exception would break
the conjecture. A full proof needs an idea that controls infinitely many digits at once.

## Part E

```lean
theorem descent_32m11 (m : Nat) :
    collatz (collatz (collatz (collatz (collatz (collatz (collatz (collatz (32 * m + 11))))))))
      < 32 * m + 11 := by
  have h1 : collatz (32 * m + 11) = 96 * m + 34 := by
    rw [step_odd (n := 32 * m + 11) (by omega)]; omega
  have h2 : collatz (96 * m + 34) = 48 * m + 17 := by
    rw [step_even (n := 96 * m + 34) (by omega)]; omega
  have h3 : collatz (48 * m + 17) = 144 * m + 52 := by
    rw [step_odd (n := 48 * m + 17) (by omega)]; omega
  have h4 : collatz (144 * m + 52) = 72 * m + 26 := by
    rw [step_even (n := 144 * m + 52) (by omega)]; omega
  have h5 : collatz (72 * m + 26) = 36 * m + 13 := by
    rw [step_even (n := 72 * m + 26) (by omega)]; omega
  have h6 : collatz (36 * m + 13) = 108 * m + 40 := by
    rw [step_odd (n := 36 * m + 13) (by omega)]; omega
  have h7 : collatz (108 * m + 40) = 54 * m + 20 := by
    rw [step_even (n := 108 * m + 40) (by omega)]; omega
  have h8 : collatz (54 * m + 20) = 27 * m + 10 := by
    rw [step_even (n := 54 * m + 20) (by omega)]; omega
  rw [h1, h2, h3, h4, h5, h6, h7, h8]; omega
```

`#print axioms descent_32m11` should then report only `propext` and `Quot.sound`.
