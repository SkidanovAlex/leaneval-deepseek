import ChallengeDeps
import Submission.Commons.Combinatorics.Additive.AP.affine_image_ap_of_ap
import Submission.Commons.NumberTheory.PrimesInAP.infinite_affine_prime_set

open scoped BigOperators

/-!
# Submission helpers for the Green–Tao theorem (`green_tao`)

The challenge theorem (`LeanEval.NumberTheory.green_tao`) asserts

    ContainsArbitraryAPs {p : ℕ | Nat.Prime p}

i.e. the set of primes contains arithmetic progressions of every length.

## Status

A complete proof requires the full Green–Tao transference machinery
(Szemerédi's theorem for arbitrary `k` in a relative/pseudorandom form, the
W-trick, and its analytic estimates).  Those deep ingredients are not yet in
the shared commons, so the final theorem cannot be assembled here yet.  This
file records the *provable elementary back-end* of that argument, built on the
shared commons:

* `Commons.Combinatorics.Additive.AP.affine_image_ap_of_ap` — the affine
  "W-trick transfer": if `{n | c * n + d ∈ A}` (`c ≥ 1`) contains APs of every
  length then so does `A`.
* `Commons.NumberTheory.PrimesInAP.infinite_affine_prime_set` — Dirichlet's
  theorem rescaled: for `gcd r W = 1` the W-tricked set
  `{n | Nat.Prime (W * n + r)}` is infinite.

`green_tao_of_tricked` below is the last line of the proof: an AP
`a + b * j` inside the W-tricked set lifts through `n ↦ W * n + r` to the
prime AP `(W*a + r) + (W*b) * j`.

## Remaining (deep) steps — roadmap

1. **W-trick density estimate.** For the modulus `W` chosen by the argument
   and a residue `r` coprime to `W` (typically `r = 1`), prove a *positive
   lower-density* statement for `{n ≤ N | W * n + r prime}`, with constants
   uniform enough in `N` (Selberg-sieve upper bounds are needed as well; the
   commons already contains `SelbergSieve`, `SieveWindows`, and many
   `NumberTheory/Nat` window/coprimality lemmas to build on).
2. **Szemerédi's theorem, arbitrary `k`.** Mathlib only has Roth's theorem
   (`k = 3`); the commons has `finite_szemeredi_three_ap` and the reduction
   `infinite_ap_of_finite_upper_density`.  The full finite Szemerédi theorem
   (all `k`) is not yet formalized anywhere in this stack.
3. **Relative/transference theorem (the core of Green–Tao §§3–10).** A
   Szemerédi-type statement for functions `f ≤ ν` dominated by a
   pseudorandom measure `ν` on `[1, N]` (Gowers uniformity norms, dense-model /
   transference).  Once the W-tricked von Mangoldt-type function is shown
   `δ`-dense under a pseudorandom `ν`, this produces the `k`-APs inside
   `{n | W*n + r prime}` required by `green_tao_of_tricked`.
-/

namespace Submission

namespace Helpers

/-- Green–Tao for the primes, *assuming* arbitrarily long APs inside a
W-tricked set `{n | Nat.Prime (W * n + r)}` (with `W ≥ 1`).  This is the
elementary last step of the proof (the "back-end"), assembled from the shared
commons lemma `affine_image_ap_of_ap`. -/
theorem green_tao_of_tricked (W r : ℕ) (hW : 1 ≤ W)
    (h : LeanEval.NumberTheory.ContainsArbitraryAPs {n : ℕ | Nat.Prime (W * n + r)}) :
    LeanEval.NumberTheory.ContainsArbitraryAPs {p : ℕ | Nat.Prime p} := by
  unfold LeanEval.NumberTheory.ContainsArbitraryAPs at h ⊢
  exact Commons.Combinatorics.Additive.AP.affine_image_ap_of_ap
    (A := {p : ℕ | Nat.Prime p}) (c := W) (d := r) hW h

/-- (W-trick set-up) `{n | Nat.Prime (W * n + r)}` is infinite for
`gcd r W = 1`, `W ≥ 1` (Dirichlet's theorem, rescaled).  Re-exported from the
shared commons so the challenge-side helpers expose it with the same name. -/
theorem infinite_affine_prime_set (W r : ℕ) (hW : 1 ≤ W) (hcop : r.Coprime W) :
    Set.Infinite {n : ℕ | Nat.Prime (W * n + r)} :=
  Commons.NumberTheory.PrimesInAP.infinite_affine_prime_set hW hcop

end Helpers

end Submission
