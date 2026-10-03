import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Submission.Port.Aesm

namespace Commons.MeasureTheory.Lp

open _root_.MeasureTheory Filter
open scoped ENNReal Topology

theorem tendsto_eLpNorm_of_ae_tendsto_of_bound {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {p : ENNReal} (hp0 : p ≠ 0) (hpT : p ≠ ⊤)
    {f : ℕ → α → ℂ} {g : α → ℂ} {B : α → ENNReal}
    (hf : ∀ n, MeasureTheory.AEStronglyMeasurable (f n) μ)
    (hB : MeasureTheory.eLpNorm B p μ < ⊤)
    (hbound : ∀ᵐ x ∂μ, ∀ n, ENNReal.ofReal ‖f n x‖ ≤ B x)
    (hlim : ∀ᵐ x ∂μ, Filter.Tendsto (fun n => f n x) Filter.atTop (nhds (g x))) :
    Filter.Tendsto (fun n => MeasureTheory.eLpNorm (f n - g) p μ) Filter.atTop (nhds 0) := by
  have hrpos : 0 < p.toReal := ENNReal.toReal_pos hp0 hpT
  have hr : 0 ≤ p.toReal := hrpos.le
  -- The a.e. limit is a.e. strongly measurable.
  have hg : AEStronglyMeasurable g μ := aestronglyMeasurable_of_tendsto_ae atTop hf hlim
  -- Finiteness of `∫ B ^ p.toReal`.
  have hBlin : ∫⁻ x, B x ^ p.toReal ∂μ < ⊤ := by
    simpa only [enorm_eq_self] using
      (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (f := B) hp0 hpT hB)
  -- Finiteness of the integral of the dominating function `(2 * B) ^ p.toReal`.
  have hbound_int : ∫⁻ x, (2 * B x) ^ p.toReal ∂μ ≠ ⊤ := by
    have heq : ∫⁻ x, (2 * B x) ^ p.toReal ∂μ
        = 2 ^ p.toReal * ∫⁻ x, B x ^ p.toReal ∂μ := by
      rw [lintegral_congr fun x => ENNReal.mul_rpow_of_nonneg 2 (B x) hr]
      rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hr (by norm_num))]
    rw [heq]
    exact (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hr (by norm_num)) hBlin).ne
  -- Dominated convergence for the `ℝ≥0∞`-valued integrands.
  have hDCT : Tendsto (fun n => ∫⁻ x, ‖f n x - g x‖ₑ ^ p.toReal ∂μ) atTop (𝓝 0) := by
    have h := tendsto_lintegral_of_dominated_convergence' (μ := μ)
      (F := fun n x => ‖f n x - g x‖ₑ ^ p.toReal) (f := fun _ => (0 : ℝ≥0∞))
      (fun x => (2 * B x) ^ p.toReal) ?_ ?_ hbound_int ?_
    · simpa using h
    · intro n
      exact (ENNReal.continuous_rpow_const (y := p.toReal)).measurable.comp_aemeasurable
        ((hf n).sub hg).enorm
    · intro n
      filter_upwards [hbound, hlim] with x hxb hxl
      have h1 : ‖f n x‖ₑ ≤ B x := by simpa using hxb n
      have h2 : ‖g x‖ₑ ≤ B x := by
        have ht : Tendsto (fun k => ‖f k x‖ₑ) atTop (𝓝 ‖g x‖ₑ) :=
          (continuous_enorm.tendsto (g x)).comp hxl
        exact le_of_tendsto ht (Eventually.of_forall fun k => by simpa using hxb k)
      have h3 : ‖f n x - g x‖ₑ ≤ 2 * B x := by
        calc ‖f n x - g x‖ₑ ≤ ‖f n x‖ₑ + ‖g x‖ₑ := enorm_sub_le
          _ ≤ B x + B x := add_le_add h1 h2
          _ = 2 * B x := by rw [two_mul]
      exact ENNReal.rpow_le_rpow h3 hr
    · filter_upwards [hlim] with x hxl
      have h0 : Tendsto (fun n => f n x - g x) atTop (𝓝 0) := by
        simpa using hxl.sub_const (g x)
      have h1 : Tendsto (fun n => ‖f n x - g x‖ₑ) atTop (𝓝 0) := by
        have h := (continuous_enorm.tendsto (0 : ℂ)).comp h0
        rw [show ((fun a : ℂ => ‖a‖ₑ) ∘ fun n => f n x - g x) = fun n => ‖f n x - g x‖ₑ
          from rfl] at h
        simpa using h
      have h2 := (ENNReal.continuous_rpow_const (y := p.toReal)).continuousAt.tendsto.comp h1
      rwa [ENNReal.zero_rpow_of_pos hrpos] at h2
  -- Rewrite `eLpNorm` in terms of the lintegral and pass to the limit.
  have hconv : Tendsto (fun n => (∫⁻ x, ‖f n x - g x‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal))
      atTop (𝓝 0) := by
    have h := (ENNReal.continuous_rpow_const (y := 1 / p.toReal)).continuousAt.tendsto.comp hDCT
    rwa [ENNReal.zero_rpow_of_pos (one_div_pos.mpr hrpos)] at h
  have heq : (fun n => eLpNorm (f n - g) p μ)
      = fun n => (∫⁻ x, ‖f n x - g x‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal) := by
    funext n
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hp0 hpT]
    simp only [Pi.sub_apply]
  rw [heq]
  exact hconv

end Commons.MeasureTheory.Lp