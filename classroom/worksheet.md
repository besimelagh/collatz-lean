# Collatz worksheet

**Level:** final years of secondary school or first-year university.
**You need:** pencil, paper, and the idea of a remainder (n mod 4, n mod 16, …).
**Time:** about 90 minutes for Parts A–D. Part E needs a computer with Lean.

**The rule.** Start with a positive integer n. If n is even, replace it with n/2. If n is odd, replace
it with 3n + 1. Repeat.

**The Collatz conjecture** says that from every starting value you eventually reach 1. Nobody has
proved it. In this worksheet you will prove some true statements about it and find out why the easy
approach runs out.

---

## Part A: Getting a feel for it

**A1.** Write out the full sequence starting from 6. How many steps does it take to reach 1?

**A2.** Do the same for 7. What is the largest number the sequence reaches?

**A3.** Starting from 27 takes 111 steps and reaches 9,232 along the way. Starting from 26 takes
10 steps and from 28 takes 18. What does this suggest about trying to predict the number of steps
from the starting value?

---

## Part B: Dropping below the start

Say that n **drops** if its sequence eventually reaches a number smaller than n.

**B1.** Explain why every even n drops.

**B2.** Suppose every n > 1 drops. Explain why the Collatz conjecture must then be true.
*Hint: think about the smallest number that never reaches 1.*

**B3.** Let n = 4m + 1 with m ≥ 1. Fill in the table, deciding at each step whether the expression is
odd or even *for every m*.

| Step | Value | Odd or even? |
|---|---|---|
| 0 | 4m + 1 | |
| 1 | | |
| 2 | | |
| 3 | | |

Show that the value after step 3 is less than 4m + 1.

**B4.** What fraction of all positive integers have you now shown to drop?

---

## Part C: Going further mod 16

**C1.** Every number that is 3 more than a multiple of 4 is one of 16m + 3, 16m + 7, 16m + 11 or
16m + 15. Repeat the table method for n = 16m + 3 and show that it drops after 6 steps.

**C2.** Try the same for 16m + 7. Keep going until the next odd/even decision depends on m. What
expression do you reach, and is it bigger or smaller than 16m + 7?

**C3.** At each "odd" step the value is multiplied by about 3, and at each "even" step it is divided
by 2. In C1 you multiplied by 3 twice and divided by 2 four times. Compute 3²/2⁴. Why does a value
below 1 mean the number drops?

---

## Part D: Where the method stops

**D1.** The numbers that survived mod 16 are 7, 11 and 15. Mod 32, each splits in two:
7 and 23, 11 and 27, 15 and 31. Show that **32m + 11** drops. *(It takes 8 steps.)*

**D2.** Show that **32m + 23** also drops.

**D3.** Write 7, 15 and 31 in binary. What do they have in common?

**D4.** Let n = 31. Use the shortcut rule T(n) = (3n + 1)/2 for odd n. Apply it 5 times and check
that every value is odd until the last one. Show that you end at 242 = 3⁵ − 1.

**D5.** *(Challenge.)* Show that if n = 2ᵏ·b − 1 with b ≥ 1 and k ≥ 1, then T(n) = 2ᵏ⁻¹·(3b) − 1.
Use this to explain why, at every level mod 2ᵏ, at least one class of numbers is never shown to drop
by this method.

**D6.** In your own words: why can checking remainders never prove the full conjecture, even though
the fraction of unresolved numbers goes to 0?

---

## Part E: Let a computer check it (optional)

Open [`Exercise.lean`](Exercise.lean). It states the result of D1 in Lean with `sorry` in place of the
proof. Replace `sorry` with a proof, using [`../Collatz.lean`](../Collatz.lean) (`descent_16m3`) as a
model. Run `lean Exercise.lean` from this folder. You are done when Lean reports no errors and the
`#print axioms` line does not mention `sorryAx`.
