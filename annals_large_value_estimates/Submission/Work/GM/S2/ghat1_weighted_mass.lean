import Mathlib
import Submission.Work.GM.S2.pair_sum_defs
import Submission.Work.GM.S2.log_window1

/-!
# The weighted mass of `ĝ₁` (Guth–Maynard §6)

The weight surviving the reflection is

`gwt ξ = ‖ĝ₁(ξ)‖ (1 + |2πξ|)^{1/2}`.

Since `ĝ₁` decays like `(1+|ξ|)^{-2}`, the weight decays like `(1+|ξ|)^{-3/2}`, hence is
integrable with a finite mass.  This is the `hgwt`/`hmass` input of the reflexion
(`Work.GM.S2.pos_half_reflection`).
-/

open MeasureTheory
open scoped BigOperators Topology

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.GM.S2

lemma gwt_nonneg (ξ : ℝ) : 0 ≤ gwt ξ :=
  mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (by positivity) _)

/-- `gwt` is continuous (as `ĝ₁` is a Fourier transform of an `L¹` function). -/
lemma gwt_continuous : Continuous gwt := by
  have h1 : Continuous (fun ξ : ℝ => 1 + |2 * Real.pi * ξ|) := by fun_prop
  unfold gwt
  exact ghat1_continuous.norm.mul
    (h1.rpow_const (p := (1 / 2 : ℝ)) (fun _ => Or.inr (by norm_num)))

/-- Quantitative decay of the weight: `‖ĝ₁(ξ)‖ ≤ C (1+|ξ|)^{-2}` gives
`gwt ξ ≤ C (1+2π)^{1/2} (1+|ξ|)^{-3/2}`. -/
lemma gwt_decay (C : ℝ) (hCpos : 0 < C)
    (hC : ∀ ξ : ℝ, ‖ghat1 ξ‖ ≤ C / (1 + |ξ|) ^ 2) (ξ : ℝ) :
    gwt ξ ≤ C * (1 + 2 * Real.pi) ^ (1 / 2 : ℝ) * (1 + |ξ|) ^ (-(3 / 2 : ℝ)) := by
  have hξ : 0 < 1 + |ξ| := by positivity
  have hC2 : ‖ghat1 ξ‖ ≤ C * (1 + |ξ|) ^ (-(2 : ℝ)) := by
    have h := hC ξ
    rw [div_eq_mul_inv, ← Real.rpow_two, ← Real.rpow_neg hξ.le] at h
    exact h
  have h2 : (1 + |2 * Real.pi * ξ|) ^ (1 / 2 : ℝ) ≤
      (1 + 2 * Real.pi) ^ (1 / 2 : ℝ) * (1 + |ξ|) ^ (1 / 2 : ℝ) := by
    have harg : 1 + |2 * Real.pi * ξ| ≤ (1 + 2 * Real.pi) * (1 + |ξ|) := by
      have h2pi : |2 * Real.pi * ξ| = 2 * Real.pi * |ξ| := by
        rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos]
        ring
      rw [h2pi]
      nlinarith [abs_nonneg ξ, Real.pi_pos]
    calc (1 + |2 * Real.pi * ξ|) ^ (1 / 2 : ℝ)
        ≤ ((1 + 2 * Real.pi) * (1 + |ξ|)) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (by positivity) harg (by norm_num)
      _ = (1 + 2 * Real.pi) ^ (1 / 2 : ℝ) * (1 + |ξ|) ^ (1 / 2 : ℝ) :=
          Real.mul_rpow (by positivity) (by positivity)
  have hb : 0 ≤ C * (1 + |ξ|) ^ (-(2 : ℝ)) :=
    mul_nonneg hCpos.le (Real.rpow_nonneg (by positivity) _)
  calc gwt ξ = ‖ghat1 ξ‖ * (1 + |2 * Real.pi * ξ|) ^ (1 / 2 : ℝ) := rfl
    _ ≤ (C * (1 + |ξ|) ^ (-(2 : ℝ))) *
          ((1 + 2 * Real.pi) ^ (1 / 2 : ℝ) * (1 + |ξ|) ^ (1 / 2 : ℝ)) :=
        mul_le_mul hC2 h2 (Real.rpow_nonneg (by positivity) _) hb
    _ = C * (1 + 2 * Real.pi) ^ (1 / 2 : ℝ) * (1 + |ξ|) ^ (-(3 / 2 : ℝ)) := by
        rw [show (-(3 / 2 : ℝ)) = -2 + (1 / 2 : ℝ) by norm_num, Real.rpow_add hξ]
        ring

/-- The weighted mass is finite: `gwt` is integrable. -/
lemma gwt_integrable
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ ξ : ℝ, ‖ghat1 ξ‖ ≤ C / (1 + |ξ|) ^ 2) :
    Integrable gwt := by
  obtain ⟨C, hCpos, hC⟩ := hdec
  set D : ℝ := C * (1 + 2 * Real.pi) ^ (1 / 2 : ℝ) with hD
  have hbase : Integrable (fun ξ : ℝ => (1 + |ξ|) ^ (-(3 / 2 : ℝ))) := by
    simpa [Real.norm_eq_abs] using
      (integrable_one_add_norm (E := ℝ) (μ := volume) (r := (3 / 2 : ℝ)) (by norm_num))
  have hdom : Integrable (fun ξ : ℝ => D * (1 + |ξ|) ^ (-(3 / 2 : ℝ))) := by
    simpa using hbase.const_mul D
  refine hdom.mono' gwt_continuous.aestronglyMeasurable ?_
  filter_upwards with ξ
  rw [Real.norm_of_nonneg (gwt_nonneg ξ)]
  exact gwt_decay C hCpos hC ξ

theorem ghat1_weighted_mass
    (hdecay : ∃ C : ℝ, 0 < C ∧ ∀ ξ : ℝ, ‖Work.GM.S2.ghat1 ξ‖ ≤ C / (1 + |ξ|) ^ 2)
    (hfin : ∃ M : ℝ, 0 < M ∧ (∫ ξ, ‖Work.GM.S2.ghat1 ξ‖) ≤ M) :
    ∃ M₁ : ℝ, 0 < M₁ ∧ MeasureTheory.Integrable Work.GM.S2.gwt ∧
      (∫ ξ, Work.GM.S2.gwt ξ) ≤ M₁ := by
  have hint : Integrable gwt := gwt_integrable hdecay
  refine ⟨(∫ ξ, gwt ξ) + 1, ?_, hint, ?_⟩
  · have hnn : (0 : ℝ) ≤ ∫ ξ, gwt ξ := integral_nonneg (fun ξ => gwt_nonneg ξ)
    linarith
  · linarith

end Work.GM.S2
