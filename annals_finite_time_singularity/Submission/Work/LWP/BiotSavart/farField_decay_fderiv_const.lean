import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.LWP.BiotSavart.nearField_bound
import Submission.Work.Spaces.mixed_sq_integrableOn
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.LWP.BiotSavart.exists_decay_of_compactSupport =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.LWP.BiotSavart

theorem exists_decay_of_compactSupport {ω : R3 → R3} {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hω : ∀ y, ‖ω y‖ ≤ M) (hsupp : ∀ y, ω y ≠ 0 → y ∈ Metric.closedBall 0 R) :
    ∃ C : ℝ, ∀ x : R3, ‖biotSavart ω x‖ ≤ C / (1 + ‖x‖) := by
  refine ⟨3 * M * R * (1 + 2 * R), ?_⟩
  intro x
  -- the proposed constant is nonnegative
  have hC : (0 : ℝ) ≤ 3 * M * R * (1 + 2 * R) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM) hR) (by linarith)
  have hn0 : (0 : ℝ) < 1 + ‖x‖ := by positivity
  rcases lt_or_ge (2 * R) ‖x‖ with hx | hx
  · -- **far field**: `2R ≤ ‖x‖`
    have hx' : 2 * R ≤ ‖x‖ := le_of_lt hx
    have hb := farField_decay_const hR hM hω hsupp x hx'
    -- the elementary inequality `(4/3) R² (1+n) ≤ 3 (1+2R) n²` for `n ≥ 2R ≥ 0`
    have hbr : (4 / 3) * R ^ 2 * (1 + ‖x‖) ≤ 3 * (1 + 2 * R) * ‖x‖ ^ 2 := by
      set s := ‖x‖ - 2 * R with hsdef
      have hs : 0 ≤ s := by linarith
      have hn : ‖x‖ = 2 * R + s := by linarith
      rw [hn]
      nlinarith [hs, hR, mul_nonneg hR hs, mul_nonneg (mul_nonneg hR hR) hs,
        mul_nonneg hR (sq_nonneg s), sq_nonneg s]
    have hMR : 0 ≤ M * R := mul_nonneg hM hR
    -- multiply by `M R ≥ 0`
    have harith : (4 / 3) * M * R ^ 3 * (1 + ‖x‖)
        ≤ 3 * M * R * (1 + 2 * R) * ‖x‖ ^ 2 := by
      calc (4 / 3) * M * R ^ 3 * (1 + ‖x‖)
          = (M * R) * ((4 / 3) * R ^ 2 * (1 + ‖x‖)) := by ring
        _ ≤ (M * R) * (3 * (1 + 2 * R) * ‖x‖ ^ 2) := mul_le_mul_of_nonneg_left hbr hMR
        _ = 3 * M * R * (1 + 2 * R) * ‖x‖ ^ 2 := by ring
    have key : (4 / 3) * M * R ^ 3 / ‖x‖ ^ 2
        ≤ 3 * M * R * (1 + 2 * R) / (1 + ‖x‖) := by
      rcases eq_or_lt_of_le (norm_nonneg x) with h0 | hnpos
      · -- `‖x‖ = 0` forces `R = 0` (and Lean's `a/0 = 0`); the bound is trivial
        rw [← h0]; simpa using hC
      · refine (le_div_iff₀ hn0).mpr ?_
        rw [div_mul_eq_mul_div, div_le_iff₀ (pow_pos hnpos 2)]
        exact harith
    exact hb.trans key
  · -- **near field**: `‖x‖ ≤ 2R`
    have hb := norm_biotSavart_near hR hM hω hsupp hx
    have key : 3 * M * R ≤ 3 * M * R * (1 + 2 * R) / (1 + ‖x‖) := by
      rw [le_div_iff₀ hn0]
      nlinarith [mul_le_mul_of_nonneg_left hx (show (0 : ℝ) ≤ 3 * M * R by positivity)]
    exact hb.trans key

end Work.LWP.BiotSavart
end
-- ===== merged: Submission.Work.LWP.BiotSavart.farField_decay_fderiv_const =====
section

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
end
