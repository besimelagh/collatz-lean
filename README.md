# collatz-lean

Small, machine-checked facts about the Collatz conjecture, written in plain Lean 4 (no Mathlib).

> **This is not a proof of the Collatz conjecture.** The results here are classical (they go back at
> least to Terras, 1976) and are the usual first steps people take on the problem. The point of this
> repository is to show what those steps look like when a computer checks every one of them, and to
> show exactly where they stop working.

## The conjecture

Start with any positive integer n. If n is even, halve it. If n is odd, replace it with 3n + 1.
Repeat. The conjecture says you always reach 1.

## What is proved

All in [`Collatz.lean`](Collatz.lean):

| Theorem | Statement |
|---|---|
| `descent_4m1` | n = 4m + 1 with m ≥ 1 drops below itself after 3 steps |
| `descent_16m3` | n = 16m + 3 drops below itself after 6 steps, for every m ≥ 0 |
| `T_odd` | The shortcut map T(n) = (3n + 1)/2 equals two ordinary steps for odd n |
| `iterT_ones` | j shortcut steps send 2^j·b − 1 to exactly 3^j·b − 1 |
| `ones_never_drop` | A number ending in j ones in binary never drops below itself during its first j shortcut steps |

### Why these matter

If every n > 1 eventually drops below its own starting value, the conjecture follows: a smallest
counterexample would drop to a smaller number, which reaches 1 by assumption.

- `descent_4m1` plus the trivial even case rule out 75% of all numbers as smallest counterexamples.
- `descent_16m3` rules out more. Checking remainders mod 2^k this way, the fraction of numbers left
  unresolved goes to 0 as k grows (Terras), so "almost all" numbers drop.
- `ones_never_drop` shows why this method can never finish the job: for every k, the class of
  numbers ending in k binary ones survives the mod 2^k check. Any full proof needs a different idea.

## Checking it yourself

Install Lean with [elan](https://github.com/leanprover/elan), then run:

```sh
lake build
```

The build prints the output of the `#eval` sanity checks and the `#print axioms` lines. Each theorem
should depend only on `propext` and `Quot.sound`. If `sorryAx` ever appears, a proof is incomplete.

GitHub Actions runs the same build on every push.

## Classroom material

The [`classroom/`](classroom) folder has a worksheet that walks through the same arguments by hand,
from computing sequences to the mod 32 case, plus a Lean exercise with one `sorry` to fill in.

- [`classroom/worksheet.md`](classroom/worksheet.md): exercises for students
- [`classroom/solutions.md`](classroom/solutions.md): full solutions
- [`classroom/Exercise.lean`](classroom/Exercise.lean): Lean exercise (not part of the build)

## Further reading

- R. Terras, "A stopping time problem on the positive integers", *Acta Arithmetica* 30 (1976).
- J. C. Lagarias, "The 3x + 1 problem and its generalizations", *American Mathematical Monthly* 92 (1985).
- T. Tao, "Almost all orbits of the Collatz map attain almost bounded values", *Forum of Mathematics, Pi* (2022).

## License

MIT. See [LICENSE](LICENSE).
