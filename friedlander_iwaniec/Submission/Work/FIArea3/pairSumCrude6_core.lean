import Mathlib
import Submission.Work.FIArea3.PairDefs6
import Submission.Work.FIArea3.BoxDefs
import Submission.Work.FIArea3.pairSumCrude6_smallU

set_option autoImplicit false

namespace Work.FIArea3

open Finset Work.FIPlan
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-!
# `Submission.Work.FIArea3.pairSumCrude6_core`

The τ-weighted **off-diagonal** pair sum of `pairSumCrude6`, in the crude regime
`1/10 ≤ θ√N ≤ N^{3/8}`.

The proof is a case split at `θ√N = N^{1/4}`, into the two regime-restricted forms of the
statement that are delegated as

* `Work.FIArea3.pairSumCrude6_smallU` (`θ√N ≤ N^{1/4}`): the polar box has `≪ u²` points, so the
  crude pointwise bound plus the large factor `(τ⁻¹+θ)/θ = 1 + 1/(θτ)` of the right-hand side
  closes the estimate;
* `Work.FIArea3.pairSumCrude6_largeU` (`N^{1/4} ≤ θ√N ≤ N^{3/8}`): here `u = θ√N ≥ N^{1/4}` and the
  paper's own route (Lemma 2.2 splitting at small divisors + the per-`z₁` joint lattice count
  `JointCount.card_filter_le_le_arith`, which needs no primitivity) applies.

Since `N^{1/4} ≤ N^{3/8}` for `N ≥ 1`, the two regimes cover the hypotheses of the target.
-/

/-- **The assembly**: the target follows from its two regime-restricted forms.

The two statements differ from the target only by the additional hypotheses `u ≤ N^{1/4}` and
`N^{1/4} ≤ u` respectively; `u ∈ [1/10, N^{3/8}]` and `N^{1/4} ≤ N^{3/8}` (as `N ≥ 1`) make the
split exhaustive.  The right-hand sides are identical, so the larger of the two constants works
once we note that `(τ⁻¹+θ)θ³N²(log N)^{2²⁰−1} ≥ 0`. -/
lemma pairSumCrude6_core_of
    (hS : ∃ C : ℝ, 0 < C ∧
      ∀ (Pa : Work.FITop.Params) (φ : ℝ) (β : GaussianInt → ℂ),
        Work.FITop3.IsBoxCoeff Pa φ β →
        (1 / 10 : ℝ) ≤ Pa.θ * Real.sqrt Pa.N →
        Pa.θ * Real.sqrt Pa.N ≤ Pa.N ^ ((3 : ℝ) / 8) →
        Pa.θ * Real.sqrt Pa.N ≤ Pa.N ^ ((1 : ℝ) / 4) →
        (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
            (if β z1 ≠ 0 ∧ β z2 ≠ 0 ∧ z1 ≠ z2 then
              (((Work.FIPlan.gnorm z1).divisors.card : ℕ) : ℝ)
                * ((((Work.FIPlan.gnorm z2).divisors.card : ℕ) : ℝ)
                    * (1 + (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ)))
            else 0))
          ≤ C * (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (3 : ℕ) * Pa.N ^ (2 : ℕ)
              * (Real.log Pa.N) ^ (((2 : ℕ) ^ (20 : ℕ)) - 1))
    (hL : ∃ C : ℝ, 0 < C ∧
      ∀ (Pa : Work.FITop.Params) (φ : ℝ) (β : GaussianInt → ℂ),
        Work.FITop3.IsBoxCoeff Pa φ β →
        (1 / 10 : ℝ) ≤ Pa.θ * Real.sqrt Pa.N →
        Pa.θ * Real.sqrt Pa.N ≤ Pa.N ^ ((3 : ℝ) / 8) →
        Pa.N ^ ((1 : ℝ) / 4) ≤ Pa.θ * Real.sqrt Pa.N →
        (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
            (if β z1 ≠ 0 ∧ β z2 ≠ 0 ∧ z1 ≠ z2 then
              (((Work.FIPlan.gnorm z1).divisors.card : ℕ) : ℝ)
                * ((((Work.FIPlan.gnorm z2).divisors.card : ℕ) : ℝ)
                    * (1 + (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ)))
            else 0))
          ≤ C * (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (3 : ℕ) * Pa.N ^ (2 : ℕ)
              * (Real.log Pa.N) ^ (((2 : ℕ) ^ (20 : ℕ)) - 1)) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Pa : Work.FITop.Params) (φ : ℝ) (β : GaussianInt → ℂ),
      Work.FITop3.IsBoxCoeff Pa φ β →
      (1 / 10 : ℝ) ≤ Pa.θ * Real.sqrt Pa.N →
      Pa.θ * Real.sqrt Pa.N ≤ Pa.N ^ ((3 : ℝ) / 8) →
      (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          (if β z1 ≠ 0 ∧ β z2 ≠ 0 ∧ z1 ≠ z2 then
            (((Work.FIPlan.gnorm z1).divisors.card : ℕ) : ℝ)
              * ((((Work.FIPlan.gnorm z2).divisors.card : ℕ) : ℝ)
                  * (1 + (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ)))
          else 0))
        ≤ C * (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (3 : ℕ) * Pa.N ^ (2 : ℕ)
            * (Real.log Pa.N) ^ (((2 : ℕ) ^ (20 : ℕ)) - 1) := by
  obtain ⟨C₁, hC₁pos, hclose⟩ := hS
  obtain ⟨C₂, hC₂pos, hfar⟩ := hL
  refine ⟨max C₁ C₂, lt_of_lt_of_le hC₁pos (le_max_left _ _), ?_⟩
  intro Pa φ β hβ hu1 hu2
  -- nonnegativity of the right-hand side
  have hx1 : (1 : ℝ) ≤ (Pa.x : ℝ) := by
    have h : (1 : ℕ) ≤ Pa.x := by have := Pa.hx; omega
    exact_mod_cast h
  have hτnn : 0 ≤ Pa.τ :=
    le_trans (Real.rpow_nonneg (Real.log_nonneg hx1) _) Pa.hτ1
  have hX : 0 ≤ (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (3 : ℕ) * Pa.N ^ (2 : ℕ)
      * (Real.log Pa.N) ^ (((2 : ℕ) ^ (20 : ℕ)) - 1) := by
    have h1 : 0 ≤ Pa.τ⁻¹ := inv_nonneg.mpr hτnn
    have h2 : 0 ≤ Pa.θ := Pa.hθ0.le
    have h3 : 0 ≤ Pa.N := by linarith [Pa.hN1]
    have h4 : 0 ≤ Real.log Pa.N := Real.log_nonneg Pa.hN1
    positivity
  have key : ∀ C : ℝ, C ≤ max C₁ C₂ →
      C * (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (3 : ℕ) * Pa.N ^ (2 : ℕ)
          * (Real.log Pa.N) ^ (((2 : ℕ) ^ (20 : ℕ)) - 1)
        ≤ max C₁ C₂ * (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (3 : ℕ) * Pa.N ^ (2 : ℕ)
          * (Real.log Pa.N) ^ (((2 : ℕ) ^ (20 : ℕ)) - 1) := by
    intro C hC
    calc C * (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (3 : ℕ) * Pa.N ^ (2 : ℕ)
            * (Real.log Pa.N) ^ (((2 : ℕ) ^ (20 : ℕ)) - 1)
        = C * ((Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (3 : ℕ) * Pa.N ^ (2 : ℕ)
            * (Real.log Pa.N) ^ (((2 : ℕ) ^ (20 : ℕ)) - 1)) := by ring
      _ ≤ max C₁ C₂ * ((Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (3 : ℕ) * Pa.N ^ (2 : ℕ)
            * (Real.log Pa.N) ^ (((2 : ℕ) ^ (20 : ℕ)) - 1)) :=
          mul_le_mul_of_nonneg_right hC hX
      _ = max C₁ C₂ * (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (3 : ℕ) * Pa.N ^ (2 : ℕ)
            * (Real.log Pa.N) ^ (((2 : ℕ) ^ (20 : ℕ)) - 1) := by ring
  by_cases h : Pa.θ * Real.sqrt Pa.N ≤ Pa.N ^ ((1 : ℝ) / 4)
  · exact le_trans (hclose Pa φ β hβ hu1 hu2 h) (key C₁ (le_max_left _ _))
  · exact le_trans (hfar Pa φ β hβ hu1 hu2 (not_le.mp h).le) (key C₂ (le_max_right _ _))

/-- The analytic content of `pairSumCrude6`: the τ-weighted OFF-DIAGONAL pair sum over the polar
box in the crude regime `1/10 ≤ θ√N ≤ N^{3/8}`.  (The diagonal `z1 = z2` is excluded, matching the
`ind z z = 0` hypothesis of the requested lemma, from which it therefore follows using
`‖β z‖ ≤ τ(|z|²)` and `ind ≤ 1`.) -/
lemma pairSumCrude6_core :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Pa : Work.FITop.Params) (φ : ℝ) (β : GaussianInt → ℂ),
      Work.FITop3.IsBoxCoeff Pa φ β →
      (1 / 10 : ℝ) ≤ Pa.θ * Real.sqrt Pa.N →
      Pa.θ * Real.sqrt Pa.N ≤ Pa.N ^ ((3 : ℝ) / 8) →
      (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          (if β z1 ≠ 0 ∧ β z2 ≠ 0 ∧ z1 ≠ z2 then
            (((Work.FIPlan.gnorm z1).divisors.card : ℕ) : ℝ)
              * ((((Work.FIPlan.gnorm z2).divisors.card : ℕ) : ℝ)
                  * (1 + (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ)))
          else 0))
        ≤ C * (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (3 : ℕ) * Pa.N ^ (2 : ℕ)
            * (Real.log Pa.N) ^ (((2 : ℕ) ^ (20 : ℕ)) - 1) := by
  exact pairSumCrude6_core_of pairSumCrude6_smallU (by sorry)


end

end Work.FIArea3
