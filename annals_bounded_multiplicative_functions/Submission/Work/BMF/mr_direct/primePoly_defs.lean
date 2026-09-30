import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Vocabulary for the prime Dirichlet polynomial large-values estimate

This file contains the definitions used by
`Work.BMF.mr_direct.primePoly_large_values` (the formalisation of Lemma `le:Rupest`, "large
values of a Dirichlet polynomial supported on primes", in K. Matomäki, M. Radziwiłł,
T. Tao, J. Teräväinen, T. Ziegler, *Higher uniformity of bounded multiplicative functions
in short intervals on average*; see `tmp_lit/mr_annals/ShorterIntervals55.tex`, §"Mean and
large value theorems for Dirichlet polynomials").

* `primeSet P` : the primes in the dyadic interval `[⌈P⌉₊, ⌊2P⌋₊]`;
* `primeDirPoly c P t` : `Σ_{p ∈ primeSet P} c p · p^{-(1+it)}`;
* `powCoeff c P k n` : the coefficient of `n^{-it}` in the `k`-th power of `primeDirPoly`,
  obtained by expanding the `k`-fold product over `k`-tuples of primes and collecting the
  terms whose product of primes equals `n`.
-/

set_option autoImplicit false

namespace Work.BMF.mr_direct.primePoly

open Finset
open scoped BigOperators

/-- The set of primes in the dyadic interval `[⌈P⌉₊, ⌊2P⌋₊]`. -/
noncomputable def primeSet (P : ℝ) : Finset ℕ := (Finset.Icc ⌈P⌉₊ ⌊2 * P⌋₊).filter Nat.Prime

/-- The prime-supported Dirichlet polynomial `Σ_{p ∈ primeSet P} c p · p^{-(1+it)}`. -/
noncomputable def primeDirPoly (c : ℕ → ℂ) (P t : ℝ) : ℂ :=
  ∑ p ∈ primeSet P, c p * (p : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))

/-- `powCoeff c P k n` is the coefficient of `n^{-it}` in `(Σ_{p ∈ primeSet P} c p p^{-1-it})^k`:
the sum, over all `k`-tuples `f` of primes in `primeSet P` with `∏ j, f j = n`, of
`∏ j, c (f j) / (f j)`. -/
noncomputable def powCoeff (c : ℕ → ℂ) (P : ℝ) (k : ℕ) (n : ℕ) : ℂ :=
  ∑ f ∈ (Fintype.piFinset (fun _ : Fin k => primeSet P)).filter (fun f => ∏ j, f j = n),
    ∏ j, (c (f j) * ((f j : ℂ))⁻¹)


end Work.BMF.mr_direct.primePoly
