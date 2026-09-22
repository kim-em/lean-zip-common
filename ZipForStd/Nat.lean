module

@[expose] public section

/-!
# Missing Nat lemmas for standard library

Lemmas about bitwise operations on natural numbers that are useful for
reasoning about bit-level algorithms (CRC, DEFLATE, etc.) but missing
from Lean 4's standard library. Candidates for upstreaming.

## Upstream status (Lean 4.33)

Nothing here any more: `Nat.or_two_pow_eq_add_of_lt` (`a < 2^n → a ||| 2^n =
a + 2^n`) is now in core, with the same signature, so the local copy is gone
and call sites resolve to core's. The file is kept as the home for the next
such lemma.
-/
