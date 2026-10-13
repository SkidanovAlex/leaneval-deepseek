import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_EllLimOK.PkgJets.CosWeightDefs
import Submission.Work.Spaces.sin_two_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.PkgJets

open scoped Real Topology
open MeasureTheory Set Filter

/-!
## Integrability of the comparison functions `cwG`, `cwPhiD` near `θ = 0`

The two functions

`cwG θ = sin(2θ)^{-η}/cos(θ)^4`,
`cwPhiD θ = 50 · sin(2θ)^{-η} · (2(1-η)cos(2θ) + 8 sin²θ)/cos(θ)^4`

(with `η = 99/100`) are continuous on a neighbourhood of every point of `(0, π/2)`, and at `θ = 0`
they behave like `(2θ)^{-η}` (times the bounded factor `cos(0)^{-4} = 1`, resp.
`50·(2(1-η) + 0)`).  Since `η < 1`, the endpoint `0` is an integrable singularity, so both are
integrable on `(0, θ]` for every `θ ∈ (0, π/2)`.  The second statement follows from the first
because the extra factor `2(1-η)cos(2θ) + 8 sin²θ` is bounded by `2(1-η) + 8 ≤ 10`, so
`|cwPhiD| ≤ 500 · cwG`.
-/

/-- `η < 1` is what makes `sin(2θ)^{-η}` integrable at `θ = 0`. -/
lemma cw_eta_Ioc : (-1 : ℝ) < -(Work.Spaces.eta) ∧ (-(Work.Spaces.eta)) ≤ 0 :=
  ⟨by norm_num [Work.Spaces.eta], by norm_num [Work.Spaces.eta]⟩

/-- `θ ↦ sin(2θ)^{-η}` is integrable on `(0, θ]` for every `θ ≤ π/2`. -/
lemma cw_sin_rpow_integrableOn_Ioc {θ : ℝ} (hθ : θ ≤ π / 2) :
    MeasureTheory.IntegrableOn (fun t : ℝ => (Real.sin (2 * t)) ^ (-(Work.Spaces.eta)))
      (Set.Ioc 0 θ) MeasureTheory.volume := by
  obtain ⟨h1, h2⟩ := cw_eta_Ioc
  obtain ⟨hint, -⟩ := Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) h1 h2
  refine hint.mono_set ?_
  intro t ht
  exact ⟨ht.1.le, le_trans ht.2 hθ⟩

/-- `cwG` is integrable on `(0, θ]` for every `θ ∈ (0, π/2)`. -/
lemma cwG_integrableOn {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    MeasureTheory.IntegrableOn cwG (Set.Ioc 0 θ) MeasureTheory.volume := by
  have hθ2 : θ < π / 2 := hθ.2
  have hθ_pi : θ ≤ π := by linarith [Real.pi_pos]
  have hcos_θ : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
  have hdom : Integrable
      (fun t : ℝ => (Real.sin (2 * t)) ^ (-(Work.Spaces.eta)) / (Real.cos θ) ^ (4 : ℕ))
      (volume.restrict (Set.Ioc 0 θ)) :=
    (cw_sin_rpow_integrableOn_Ioc (θ := θ) (le_of_lt hθ2)).div_const _
  refine hdom.mono' ?_ ?_
  · refine Measurable.aestronglyMeasurable ?_
    show Measurable
      (fun t : ℝ => (Real.sin (2 * t)) ^ (-(Work.Spaces.eta)) / (Real.cos t) ^ (4 : ℕ))
    exact ((Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const _).div
      (Real.measurable_cos.pow_const (4 : ℕ))
  · refine ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht => ?_)
    have ht0 : 0 ≤ t := ht.1.le
    have htle : t ≤ θ := ht.2
    have hcos_le : Real.cos θ ≤ Real.cos t :=
      Real.cos_le_cos_of_nonneg_of_le_pi ht0 hθ_pi htle
    have hpow_le : Real.cos θ ^ (4 : ℕ) ≤ Real.cos t ^ (4 : ℕ) :=
      pow_le_pow_left₀ (le_of_lt hcos_θ) hcos_le 4
    have hsin_nn : 0 ≤ (Real.sin (2 * t)) ^ (-(Work.Spaces.eta)) :=
      Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩) _
    have hcwG_nn : 0 ≤ cwG t := by
      rw [cwG]
      exact div_nonneg hsin_nn (by positivity)
    rw [Real.norm_of_nonneg hcwG_nn, cwG]
    exact div_le_div_of_nonneg_left hsin_nn (by positivity) hpow_le

/-- The extra factor of `cwPhiD` is bounded by `10` in absolute value. -/
lemma cw_phi_factor_bound (t : ℝ) :
    |2 * (1 - Work.Spaces.eta) * Real.cos (2 * t) + 8 * (Real.sin t) ^ (2 : ℕ)| ≤ 10 := by
  have h1 : |2 * (1 - Work.Spaces.eta) * Real.cos (2 * t)| ≤ 2 * (1 - Work.Spaces.eta) := by
    rw [abs_mul,
      abs_of_nonneg (by norm_num [Work.Spaces.eta] : (0 : ℝ) ≤ 2 * (1 - Work.Spaces.eta))]
    exact mul_le_of_le_one_right (by norm_num [Work.Spaces.eta]) (Real.abs_cos_le_one _)
  have h2 : |8 * (Real.sin t) ^ (2 : ℕ)| ≤ 8 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 8),
      abs_of_nonneg (sq_nonneg (Real.sin t))]
    exact mul_le_of_le_one_right (by norm_num) (Real.sin_sq_le_one t)
  calc |2 * (1 - Work.Spaces.eta) * Real.cos (2 * t) + 8 * (Real.sin t) ^ (2 : ℕ)|
      ≤ |2 * (1 - Work.Spaces.eta) * Real.cos (2 * t)| + |8 * (Real.sin t) ^ (2 : ℕ)| :=
        abs_add_le _ _
    _ ≤ 2 * (1 - Work.Spaces.eta) + 8 := add_le_add h1 h2
    _ ≤ 10 := by norm_num [Work.Spaces.eta]

/-- `cwPhiD = 50 · (2(1-η)cos(2θ) + 8sin²θ) · cwG` (the factor `sin(2θ)^{-η}/cos(θ)^4` split off). -/
lemma cwPhiD_eq_factor_mul_cwG (t : ℝ) :
    cwPhiD t =
      (50 * (2 * (1 - Work.Spaces.eta) * Real.cos (2 * t) + 8 * (Real.sin t) ^ (2 : ℕ)))
        * cwG t := by
  rw [cwPhiD, cwG]
  ring

/-- `|cwPhiD t| ≤ 500 · cwG t` for `t ∈ [0, π/2]`. -/
lemma cwPhiD_abs_le {t : ℝ} (ht : t ∈ Set.Icc 0 (π / 2)) : ‖cwPhiD t‖ ≤ 500 * cwG t := by
  have ht0 : 0 ≤ t := ht.1
  have ht2 : t ≤ π / 2 := ht.2
  have hB := cw_phi_factor_bound t
  have hsin_nn : 0 ≤ (Real.sin (2 * t)) ^ (-(Work.Spaces.eta)) :=
    Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩) _
  have hcwG_nn : 0 ≤ cwG t := by
    rw [cwG]
    exact div_nonneg hsin_nn (by positivity)
  rw [cwPhiD_eq_factor_mul_cwG, Real.norm_eq_abs, abs_mul, abs_of_nonneg hcwG_nn]
  refine mul_le_mul_of_nonneg_right ?_ hcwG_nn
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 50)]
  have := mul_le_mul_of_nonneg_left hB (by norm_num : (0 : ℝ) ≤ 50)
  linarith

/-- `cwPhiD` is integrable on `(0, θ]` for every `θ ∈ (0, π/2)`. -/
lemma cwPhiD_integrableOn {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    MeasureTheory.IntegrableOn cwPhiD (Set.Ioc 0 θ) MeasureTheory.volume := by
  have hG := cwG_integrableOn hθ
  refine (hG.const_mul (500 : ℝ)).mono' ?_ ?_
  · refine Measurable.aestronglyMeasurable ?_
    have h1 : Measurable (fun t : ℝ => (Real.sin (2 * t)) ^ (-(Work.Spaces.eta))) :=
      (Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const _
    have h2 : Measurable (fun t : ℝ => Real.cos (2 * t)) :=
      Real.measurable_cos.comp (measurable_const.mul measurable_id)
    have h3 : Measurable (fun t : ℝ => (Real.sin t) ^ (2 : ℕ)) :=
      Real.measurable_sin.pow_const (2 : ℕ)
    have h4 : Measurable (fun t : ℝ => (Real.cos t) ^ (4 : ℕ)) :=
      Real.measurable_cos.pow_const (4 : ℕ)
    have h5 : Measurable (fun t : ℝ => 50 * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta)) *
        (2 * (1 - Work.Spaces.eta) * Real.cos (2 * t) + 8 * (Real.sin t) ^ (2 : ℕ))
        / (Real.cos t) ^ (4 : ℕ)) :=
      ((measurable_const.mul h1).mul
        ((measurable_const.mul h2).add (measurable_const.mul h3))).div h4
    change Measurable (fun t : ℝ => 50 * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta)) *
        (2 * (1 - Work.Spaces.eta) * Real.cos (2 * t) + 8 * (Real.sin t) ^ (2 : ℕ))
        / (Real.cos t) ^ (4 : ℕ))
    exact h5
  · refine ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht =>
      cwPhiD_abs_le ⟨ht.1.le, le_trans ht.2 (le_of_lt hθ.2)⟩)

theorem cw_integrable : ∀ θ : ℝ, θ ∈ Set.Ioo 0 (π / 2) →
    MeasureTheory.IntegrableOn cwG (Set.Ioc 0 θ) MeasureTheory.volume ∧
    MeasureTheory.IntegrableOn cwPhiD (Set.Ioc 0 θ) MeasureTheory.volume := by
  intro θ hθ
  exact ⟨cwG_integrableOn hθ, cwPhiD_integrableOn hθ⟩

end Work.FTS_EllLimOK.PkgJets
