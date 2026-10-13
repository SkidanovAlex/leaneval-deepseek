/-
# `Work.LWP.BiotSavart.farField_decay_fderiv_const` — far-field decay of `D (biotSavart ω)`
with the explicit constant `2^20`

For a vorticity `ω` bounded by `M` and supported in the closed ball of radius `R` about the
origin, the derivative of the Newtonian-potential Biot–Savart field decays like `‖x‖⁻³`, with
the *explicit* constant `2^20`:

  `‖fderiv ℝ (biotSavart ω) x‖ ≤ 2^20 · M · R³ / ‖x‖³`   whenever `2R ≤ ‖x‖`.

This is the constant-explicit form of `Work.LWP.BiotSavart.farField_decay_fderiv` (which only
asserts the existence of *some* positive constant); it is the shape the LWP/BKM assembly
consumes.

The proof has the same two branches as `farField_decay_fderiv`.

* If `ω` is ae strongly measurable, then on `ball x (‖x‖/4)` the map `z ↦ biotSavart ω z` is
  Lipschitz with constant exactly `2^20 · M R³/‖x‖³` (see `biotSavart_lipschitzOn_far`), so that
  `‖fderiv ℝ (biotSavart ω) x‖` is bounded by that constant, and vanishes at non-differentiability
  points.
* If `ω` is *not* ae strongly measurable, two independent cross-product directions determine `ω`
  (`crossMeasDichotomy`), so `biotSavart ω` vanishes off a single point and its whole Fréchet
  derivative is `0` (`fderiv_eq_zero_of_eq_zero_off_single`); the bound holds trivially because the
  right-hand side is nonnegative.
-/
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.LWP.Defs
import Submission.Work.LWP.BiotSavart.farField_decay_fderiv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity MeasureTheory Set Filter Topology
open scoped Matrix Topology

set_option autoImplicit false

namespace Work.LWP.BiotSavart

/-- **Far-field decay of the derivative of the Biot–Savart field, with the explicit constant
`2^20`.**  For a vorticity bounded by `M` and supported in the closed ball of radius `R`,
`‖fderiv ℝ (biotSavart ω) x‖ ≤ 2^20 · M · R³ / ‖x‖³` for every `x` with `2R ≤ ‖x‖`. -/
theorem farField_decay_fderiv_const {ω : R3 → R3} {R M : ℝ} (hR : 0 < R) (hM : 0 ≤ M)
    (hω : ∀ y, ‖ω y‖ ≤ M) (hsupp : ∀ y, ω y ≠ 0 → y ∈ Metric.closedBall 0 R) :
    ∀ x : R3, 2 * R ≤ ‖x‖ →
      ‖fderiv ℝ (biotSavart ω) x‖ ≤ 2 ^ 20 * M * R ^ 3 / ‖x‖ ^ 3 := by
  intro x hx
  by_cases hmeas : AEStronglyMeasurable ω volume
  · -- the measurable case: `biotSavart ω` is Lipschitz in the far field with constant `2^20 M R³/‖x‖³`
    by_cases hd : DifferentiableAt ℝ (biotSavart ω) x
    · have hx0 : 0 < ‖x‖ := by linarith
      have hlip := biotSavart_lipschitzOn_far (le_of_lt hR) hM hω hsupp hmeas hx
      have hb := hd.hasFDerivAt.le_of_lipschitzOn
        (Metric.ball_mem_nhds x (by positivity)) hlip
      rw [Real.coe_toNNReal _ (by positivity)] at hb
      exact hb
    · rw [fderiv_zero_of_not_differentiableAt hd, norm_zero]
      positivity
  · -- the non-measurable case: two independent cross-product directions determine `ω`, so there
    -- is at most one point at which the integrand is ae strongly measurable; hence `biotSavart ω`
    -- vanishes off a single point and its derivative vanishes everywhere
    have hkey : ∀ z z' : R3, AEStronglyMeasurable (bsK ω z) volume →
        AEStronglyMeasurable (bsK ω z') volume → z = z' := by
      intro z z' hz hz'
      by_contra hne
      exact hmeas (crossMeasDichotomy hne
        (aestronglyMeasurable_cross_of_bsK hz) (aestronglyMeasurable_cross_of_bsK hz'))
    have hsingle : ∃ p : R3, ∀ z, z ≠ p → biotSavart ω z = 0 := by
      by_cases hM' : ∃ p : R3, AEStronglyMeasurable (bsK ω p) volume
      · obtain ⟨p, hp⟩ := hM'
        refine ⟨p, fun z hz => ?_⟩
        have hz' : ¬ AEStronglyMeasurable (bsK ω z) volume := fun h => hz (hkey z p h hp)
        rw [biotSavart_apply, integral_non_aestronglyMeasurable hz', smul_zero]
      · exact ⟨x, fun z _ => by
          rw [biotSavart_apply, integral_non_aestronglyMeasurable (fun h => hM' ⟨z, h⟩),
            smul_zero]⟩
    rw [fderiv_eq_zero_of_eq_zero_off_single hsingle.choose_spec x, norm_zero]
    positivity

end Work.LWP.BiotSavart
