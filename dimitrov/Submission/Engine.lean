import Mathlib
import Submission.Induction
import Submission.Conjugates
import Submission.Powers
import Submission.PowRev
import Submission.SquarePoly
import Submission.RootOfUnity
import Submission.SquareReflect
import Submission.EngineAlg
import Submission.AnalyticEngine

/-!
# THE ANALYTIC ENGINE (the single remaining gap)

`Submission.Induction.dimitrov_of_engine` reduces the challenge theorem to the
following statement, which is exactly the analytic content of Dimitrov's proof
of the Schinzel–Zassenhaus conjecture (Dimitrov, arXiv:1912.12545, in the
phase-refined form; cf. McKee–Smyth, *Around the Unit Circle*, Ch. 4).

The theorem is proved here by reduction to the single isolated analytic
statement `Submission.AnalyticEngine.hankel_eventually_zero` (the only
remaining `sorry` in the tree): assuming `house α < 2^(1/(4·|argSet α|))`
the analytic engine must produce the "Hankel input" (an integer sequence
`a`, the coefficients of the formal square root of the reversed power
product, whose Hankel determinants vanish eventually).  The algebraic tail
`Submission.EngineAlg.no_hankelInput` then turns that input into the
contradiction with `¬ IsOfFinOrder α` via the verified chain
Kronecker + RationalSqrt + SquareReflect + SquarePoly + RootOfUnity.

## What the engine must prove

For a number field `K` and `α : K`, with `P := minpoly ℤ α` monic irreducible of
degree `d` whose complex roots are the conjugate set `S`, assume
`P₂ := pow2 P` is *irreducible*.  Then the house bound
`2^(1/(4·|argSet α|)) ≤ house α` holds (i.e. `Bound α`), where `|argSet α|` is
the number of distinct phases of the conjugates.

## Proof plan of the engine (all the ingredients except capacity theory are in
place; see the docstrings of Submission.PowRev / SquarePoly / RootOfUnity /
SquareReflect / Induction for the verified algebra)

Assume for contradiction `house α < 2^(1/(4 d'))` with `d' := |argSet α|`,
`S := conjugateValues α`, `H := house α`.

1. **Integer series.**  Let `R₂ := (pow2 P).reflect d`, `R₄ := (pow4 P).reflect d`,
   `G := R₂ * R₄`.  `Submission.PowRev.powRev_sqrt_integral` gives a sequence
   `a : ℕ → ℤ` with `a 0 = 1` and `(∑_{i+j=k} a_i a_j) = G.coeff k`, i.e. the
   formal series `F(w) := Σ a_k w^k` satisfies `F(w)² = G(w)` in `ℤ[[w]]` and
   `F(0) = 1`.  As an analytic function, `F` converges in `|w| < 1/H⁴` and
   equals the principal branch of `sqrt (R₂(w) R₄(w))` near `w = 0`.

2. **Analytic continuation off the hedgehog.**  The function `f(X) := F(1/X) =
   Σ a_k X^{-k}` (an element of `ℤ[[1/X]]`, convergent for `|X| > H⁴`) extends
   from infinity to a holomorphic function on the complement of the compact
   set `K := ⋃_{z∈S} ([0,z²] ∪ [0,z⁴])` in the Riemann sphere (the branch
   points of the square root are exactly the points `z², z⁴`, and the
   complement is simply connected, so the branch of the square root with value
   `1` at infinity exists there).  All spikes of `K` have length `≤ H⁴`.

3. **Spike count and Dubinin's inequality.**  The hedgehog `K` has at most
   `2 d'` distinct spikes: the rays of `z²` and of `z⁴` for `z ∈ S`; distinct
   arguments of `{z²} ∪ {z⁴}` are counted by
   `|argSet(α²) ∪ argSet(α⁴)| ≤ 2 d'` (Submission.Phases).  By Dubinin's
   theorem, a hedgehog with `s` spikes of lengths at most `L` has transfinite
   diameter `τ(K) ≤ 4^(-1/s) · L`; with `s ≤ 2d'` and `L = H⁴`:
   `τ(K) ≤ 4^(-1/s) H⁴ ≤ 4^(-1/(2d')) H⁴ < 4^(-1/(2d')) · 2^(1/d') = 1`
   (the strict inequality uses `H < 2^(1/(4d'))`, i.e. `H⁴ < 2^(1/d')`).

4. **Pólya–Bertrandias rationality.**  (Bertrandias's theorem; the classical
   rationality criterion of Pólya and Carlson in the sharp quantitative form
   with transfinite diameter < 1.)  An integer-coefficient series
   `f(1/X) ∈ ℤ[[1/X]]` that is holomorphic on the connected complement of a
   compact set `K` with `τ(K) < 1` is rational.  Hence `f` is rational.

5. **Algebraic conclusion.**  A rational `f = F(1/·)` means `F` is rational;
   since `F² = G` is a polynomial, `F` is a polynomial, so `G` is a perfect
   square in `ℤ[X]`; by `Submission.SquareReflect.pow_product_square_of_reflect_square`,
   `P₂ P₄` is a perfect square; by `Submission.SquarePoly.pow4_eq_pow2_of_square`
   (using irreducibility of `P₂`), `P₄ = P₂`; by
   `Submission.RootOfUnity.pow4_eq_pow2_imp_rootOfUnity`, `α` is a root of
   unity, contradicting the hypothesis.  So `house α ≥ 2^(1/(4 d'))`.  ∎

The gap is entirely in steps 2–4: analytic continuation onto the complement of
a finite union of radial segments; the theory of transfinite diameter /
Chebyshev constants including Dubinin's bound for hedgehogs; and the
Pólya–Bertrandias rationality theorem.  None of this is currently in Mathlib.
-/

noncomputable section

namespace Submission.Engine

open Submission.Induction
open Submission.Conjugates
open Submission.Powers

variable {K : Type*} [Field K] [NumberField K]

/-- The analytic engine: under irreducibility of `pow2 (minpoly ℤ α)`, the
house bound holds.  (Statement only; proof needs capacity theory.) -/
theorem house_bound_of_pow2_irreducible (α : K) (hα : IsIntegral ℤ α)
    (hα0 : α ≠ 0) (hROU : ¬ IsOfFinOrder α)
    (h2irr : Irreducible (pow2 (minpoly ℤ α))) : Bound α := by
  by_contra hnot
  have hH : NumberField.house α <
      (2 : ℝ) ^ (1 / (4 * ((Submission.Conjugates.argSet α).card : ℝ))) := by
    exact Submission.EngineAlg.house_lt_of_not_bound α hnot
  have hIn : Submission.EngineAlg.HankelInput α hα :=
    Submission.AnalyticEngine.hankel_eventually_zero α hα hα0 hH h2irr
  exact Submission.EngineAlg.no_hankelInput α hα hα0 hROU h2irr hIn

end Submission.Engine

end
