/-
# `fkLowAux` — the level-`m` slice sum behind `fkLowSlice`

This file provides the pointwise algebra behind the target

  `Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkLowSlice`

namely the observation that the level-`m` `ℋ`-integrand factorises *exactly* as

  `HkIntegrand α m f z θ = (w z)² · lowSum α m f z θ`

on the open angular interval, where `lowSum` is `HkIntegrand` with the radial weight `(w z)²`
pulled out and the mixed slots written with the angular weight `sin(2θ)^{-γ}` left in place.
Consequently the angular slice of `HkIntegrand` is `(w z)²` times the slice of `lowSum`, and the
slice bound reduces to two independent one-dimensional integral bounds (see
`NOTES_fkLowSlice.md` and the companion files `lowZSliceLe.lean`, `lowMixedSliceLe.lean`,
`lowGamSlotIntegrable.lean`).

The two slot identities used here are

* `(D_z^i f · w/sin(2θ)^{η/2})² = (w z)² · (D_z^i f)² · sin(2θ)^{-η}`  (`Work.FTS.H2.div_rpow_sq`);
* `(D_z^jD_θ^if · Wt α)² = (w z)² · (D_z^jD_θ^if)² · sin(2θ)^{-γ(α)}`  (`Wt = w·sin(2θ)^{-γ/2}`
  and `(sin(2θ)^{-γ/2})² = sin(2θ)^{-γ}` for `sin(2θ) > 0`).

-/
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.H2.SupMixedNB

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-! ## The weight-free level-`m` slice sum -/

/-- The level-`m` `ℋ`-integrand with the radial weight `(w z)²` removed: the radial slots keep
their `η`-weight, the mixed slots their `γ`-weight.  On the open angular interval
`HkIntegrand α m f z θ = (w z)² * lowSum α m f z θ` (`HkIntegrand_eq_w_sq_mul_lowSum`). -/
noncomputable def lowSum (α : ℝ) (m : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (∑ i ∈ Finset.range (m + 1),
      (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.mixed i 0 f z θ) ^ 2)
    + ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
        if 1 ≤ i ∧ i + j ≤ m then
          (Work.Spaces.mixed j i f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        else 0

/-! ## The two slot identities -/

/-- A single radial slot: `(D_z^i f · w/sin(2θ)^{η/2})² = (w z)²·(D_z^i f)²·sin(2θ)^{-η}`. -/
theorem zslot_eq_low {f : ℝ → ℝ → ℝ} {z θ : ℝ} (hs : 0 < Real.sin (2 * θ)) (i : ℕ) :
    (Work.Spaces.DzIter i f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          * (Work.Spaces.mixed i 0 f z θ) ^ 2) := by
  rw [Work.Spaces.mixed_zero_right, mul_pow,
    Work.FTS.H2.div_rpow_sq (Work.Spaces.w z) (Real.sin (2 * θ)) Work.Spaces.eta hs.le
      (ne_of_gt Work.Spaces.eta_pos)]
  ring

/-- A single mixed slot: `(D_z^jD_θ^if · Wt α)² = (w z)²·(D_z^jD_θ^if)²·sin(2θ)^{-γ(α)}`. -/
theorem mslot_eq_low {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hs : 0 < Real.sin (2 * θ)) (i j : ℕ) :
    (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * ((Work.Spaces.mixed j i f z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
  have hgam : Work.Spaces.gam α ≠ 0 := by
    rw [Work.Spaces.gam]
    intro h
    linarith
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow, mul_pow,
    Work.Spaces.bt_rpow_sq (Work.Spaces.gam α) (Real.sin (2 * θ)) hs.le hgam]
  ring

/-! ## The factorisation of `HkIntegrand` -/

/-- **The level-`m` slice factorisation** on the open angular interval:
`HkIntegrand α m f z θ = (w z)² · lowSum α m f z θ`. -/
theorem HkIntegrand_eq_w_sq_mul_lowSum {α : ℝ} (hα : 0 < α) (m : ℕ) (f : ℝ → ℝ → ℝ)
    {z θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.HkIntegrand α m f z θ = (Work.Spaces.w z) ^ 2 * lowSum α m f z θ := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  simp only [Work.Spaces.HkIntegrand, lowSum]
  rw [mul_add]
  simp only [Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => zslot_eq_low hs i
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases hc : 1 ≤ i ∧ i + j ≤ m
    · rw [if_pos hc, if_pos hc]
      exact mslot_eq_low hα hs i j
    · rw [if_neg hc, if_neg hc]
      ring

/-- Almost every point of `Iθ` is an interior point of the interval. -/
theorem ae_mem_Ioo_Iθ_low :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (π / 2) := by
  rw [Work.Spaces.Iθ]
  rw [← MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc]
  exact MeasureTheory.self_mem_ae_restrict measurableSet_Ioo

/-- The factorisation, almost everywhere on `Iθ`. -/
theorem ae_HkIntegrand_eq_w_sq_mul_lowSum {α : ℝ} (hα : 0 < α) (m : ℕ) (f : ℝ → ℝ → ℝ)
    (z : ℝ) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.HkIntegrand α m f z θ = (Work.Spaces.w z) ^ 2 * lowSum α m f z θ :=
  ae_mem_Ioo_Iθ_low.mono fun _ hθ => HkIntegrand_eq_w_sq_mul_lowSum hα m f hθ

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
