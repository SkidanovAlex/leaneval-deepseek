/-
Copyright: work module for the Elgindi finite-time singularity project.

# Shared vocabulary for the seven-slot honesty transfer from a *vanishing* family

`HkMem_of_pure_and_vanishing` reduces `HkMem α k f` (for `f` smooth on the open quadrant) to

* the level-`0` honesty of the *pure radial* slots `D_z^j f`, `j ≤ k` (with the singular
  weight `σ = sin(2θ)^{-η}`), and
* the integrability of the *vanishing-weight* slots
  `vig α f r j = (D_z^j ∂_θ^r f · w)² · sin(2θ)^{2r-γ}` for `1 ≤ r`, `r + j ≤ k`.

The input family of the target lemma `HkMem_seven_slots_of_vanishing_family` provides

* `hσ`: `HkMem α 0 (D_z^l ∂_θ^m Ψ)` for `l ≤ 9`, `m ≤ 2`, and
* `hV`: integrability of `hVint α Ψ t l = (D_z^l ∂_θ^t Ψ · w)² · sin(2θ)^{2t-4-γ}` for
  `3 ≤ t ≤ 9`, `l ≤ 9`,

i.e. the singular weight only up to angular order `2`, and (weaker) *vanishing* weights from
angular order `3` on.  Everything the assembly needs is stated against the single grid
majorant `vanGrid` below, which is the sum of all these known-integrable integrands.

This module contains definitions only (no proofs), so that the parallel pieces of the
argument can be stated against them.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.ClassC.HkMem_of_pure_and_vanishing

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

set_option autoImplicit false

/-- The integrand of the `hV` hypothesis of `HkMem_seven_slots_of_vanishing_family`, as a
curried function: `(D_z^l ∂_θ^t Ψ · w)² · sin(2θ)^{2t - 4 - γ}`. -/
def hVint (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (t l : ℕ) : ℝ → ℝ → ℝ :=
  fun z θ => (Work.Spaces.DzIter l (Work.Spaces.pthIter t Ψ) z θ * Work.Spaces.w z) ^ 2
    * (Real.sin (2 * θ)) ^ (2 * (t : ℝ) - 4 - Work.Spaces.gam α)

/-- The *grid majorant* of the assembly: the sum of all the integrands whose integrability is
supplied by the hypotheses `hσ` (the singular-weight family, `l ≤ 9`, `m ≤ 2`) and `hV` (the
vanishing-weight family, `3 ≤ t ≤ 9`, `l ≤ 9`). -/
def vanGrid (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ =>
    (∑ l ∈ Finset.range 10, ∑ m ∈ Finset.range 3,
        Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter l (Work.Spaces.pthIter m Ψ)) z θ)
      + ∑ t ∈ Finset.Icc 3 9, ∑ l ∈ Finset.range 10, hVint α Ψ t l z θ

/-- The sum of the constants `vanC` of `HkMem_of_pure_and_vanishing` over all the mixed slots
of level `k`; the constant of the pointwise reduction `HkIntegrand_le_pure_vanishing`. -/
def vanSum (α : ℝ) (hα : 0 < α) (hγ : Work.Spaces.gam α ≤ 3 / 2)
    (f : ℝ → ℝ → ℝ) (hsm : Work.FTS.EllipticEst.SmoothOpen f) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), ∑ i ∈ Finset.Icc 1 (k - j),
    (if h : 1 ≤ i then vanC α hα hγ f hsm i j h else 0)

/-- The grid majorant is nonnegative on the angular interval. -/
theorem vanGrid_nonneg (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (z : ℝ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ vanGrid α Ψ z θ := by
  rw [vanGrid]
  refine add_nonneg (Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun m _ => ?_)
    (Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun l _ => ?_)
  · exact Work.Spaces.HkIntegrand_nonneg α 0 _ z θ
  · rw [hVint]
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ' hθ) _)

/-- `vanSum` is nonnegative. -/
theorem vanSum_nonneg (α : ℝ) (hα : 0 < α) (hγ : Work.Spaces.gam α ≤ 3 / 2)
    (f : ℝ → ℝ → ℝ) (hsm : Work.FTS.EllipticEst.SmoothOpen f) (k : ℕ) :
    0 ≤ vanSum α hα hγ f hsm k := by
  rw [vanSum]
  refine Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => ?_
  split_ifs with h
  · exact le_of_lt (vanC_pos α hα hγ f hsm i j h)
  · exact le_refl 0

end Work.FTS.ClassC
