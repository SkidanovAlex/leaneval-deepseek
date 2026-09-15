import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.WithDensity

open MeasureTheory Filter
open scoped ENNReal

namespace Commons.MeasureTheory.Lp

/-- If the `L²` seminorm-squared integral `∫⁻ ‖v i - u‖ₑ ^ 2 ∂μ` tends to `0`, then the
corresponding classes in `Lp E 2 μ` converge to each other in norm. -/
theorem tendsto_norm_toLp_of_tendsto_lintegral_enorm_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {ι : Type*} {l : Filter ι} {E : Type*} [NormedAddCommGroup E]
    {v : ι → α → E} {u : α → E}
    (hv : ∀ i, MemLp (v i) 2 μ) (hu : MemLp u 2 μ)
    (h : Tendsto (fun i => ∫⁻ x, ‖v i x - u x‖ₑ ^ (2 : ℝ) ∂μ) l (nhds 0)) :
    Tendsto (fun i => ‖(hv i).toLp (v i) - hu.toLp u‖) l (nhds 0) := by
  have key : ∀ i, ENNReal.ofReal (‖(hv i).toLp (v i) - hu.toLp u‖ ^ 2)
      = ∫⁻ x, ‖v i x - u x‖ₑ ^ (2 : ℝ) ∂μ := by
    intro i
    have h1 : ‖(hv i).toLp (v i) - hu.toLp u‖ₑ = eLpNorm (v i - u) 2 μ := by
      rw [← edist_eq_enorm_sub]
      exact Lp.edist_toLp_toLp (v i) u (hv i) hu
    have hC := MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (f := v i - u)
      (p := (2 : NNReal)) (by norm_num)
    have step1 : ENNReal.ofReal (‖(hv i).toLp (v i) - hu.toLp u‖ ^ 2)
        = ‖(hv i).toLp (v i) - hu.toLp u‖ₑ ^ (2 : ℝ) := by
      rw [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm, ← ENNReal.rpow_two]
    calc ENNReal.ofReal (‖(hv i).toLp (v i) - hu.toLp u‖ ^ 2)
        = ‖(hv i).toLp (v i) - hu.toLp u‖ₑ ^ (2 : ℝ) := step1
      _ = (eLpNorm (v i - u) 2 μ) ^ (2 : ℝ) := by rw [h1]
      _ = ∫⁻ x, ‖(v i - u) x‖ₑ ^ (2 : ℝ) ∂μ := hC
      _ = ∫⁻ x, ‖v i x - u x‖ₑ ^ (2 : ℝ) ∂μ := by simp only [Pi.sub_apply]
  have h2 : ∀ i, ‖(hv i).toLp (v i) - hu.toLp u‖
      = Real.sqrt ((∫⁻ x, ‖v i x - u x‖ₑ ^ (2 : ℝ) ∂μ).toReal) := by
    intro i
    rw [← Real.sqrt_sq (norm_nonneg _)]
    congr 1
    rw [← key i, ENNReal.toReal_ofReal (sq_nonneg _)]
  rw [funext h2]
  have h3 : Tendsto (fun i => (∫⁻ x, ‖v i x - u x‖ₑ ^ (2 : ℝ) ∂μ).toReal) l (nhds 0) :=
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  have h4 : Tendsto (fun i => Real.sqrt ((∫⁻ x, ‖v i x - u x‖ₑ ^ (2 : ℝ) ∂μ).toReal))
      l (nhds 0) := by
    have := Real.continuous_sqrt.continuousAt.tendsto.comp h3
    rwa [Real.sqrt_zero] at this
  exact h4

/-- For a measure with density `ENNReal.ofReal ∘ F` (with `F ≥ 0`),
the `L²`-energy integral against the density can be written as an integral against
`volume` of `ofReal (‖g x‖ ^ 2 * F x)`. -/
theorem lintegral_enorm_sq_withDensity_ofReal {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    {F : (Fin d → ℂ) → ℝ} (hFc : Continuous F) (hFnn : ∀ x, 0 ≤ F x)
    (g : (Fin d → ℂ) → E) :
    ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ)
        ∂((volume : Measure (Fin d → ℂ)).withDensity (fun x => ENNReal.ofReal (F x)))
      = ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2 * F x) ∂(volume : Measure (Fin d → ℂ)) := by
  have hFfinite : ∀ᵐ x ∂(volume : Measure (Fin d → ℂ)), ENNReal.ofReal (F x) < ∞ :=
    Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top
  have hFmeas : AEMeasurable (fun x : Fin d → ℂ => ENNReal.ofReal (F x)) volume :=
    (hFc.measurable.ennreal_ofReal).aemeasurable
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable₀ volume hFmeas hFfinite]
  apply lintegral_congr
  intro x
  simp only [Pi.mul_apply]
  rw [← ofReal_norm, ENNReal.rpow_two, ← ENNReal.ofReal_pow (norm_nonneg _) 2,
    ← ENNReal.ofReal_mul (hFnn x), mul_comm]

theorem tendsto_norm_toLp_sub_of_tendsto_lintegral_ofReal {d : ℕ} {ι : Type*} {l : Filter ι}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (Fin d → ℂ) → ℝ} (hFc : Continuous F) (hFnn : ∀ x, 0 ≤ F x)
    {w : ι → (Fin d → ℂ) → E} {u : (Fin d → ℂ) → E}
    (hw : ∀ i, MeasureTheory.MemLp (w i) 2
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)).withDensity
        (fun x => ENNReal.ofReal (F x))))
    (hu : MeasureTheory.MemLp u 2
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)).withDensity
        (fun x => ENNReal.ofReal (F x))))
    (h : Filter.Tendsto (fun i => ∫⁻ x, ENNReal.ofReal (‖w i x - u x‖ ^ 2 * F x)
      ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ))) l (nhds 0)) :
    Filter.Tendsto (fun i => ‖(hw i).toLp (w i) - hu.toLp u‖) l (nhds 0) := by
  let μ : Measure (Fin d → ℂ) :=
    (volume : Measure (Fin d → ℂ)).withDensity (fun x => ENNReal.ofReal (F x))
  have hmem : ∀ i, MemLp (w i) 2 μ := hw
  have humem : MemLp u 2 μ := hu
  have heq : ∀ i, ∫⁻ x, ‖w i x - u x‖ₑ ^ (2 : ℝ) ∂μ
      = ∫⁻ x, ENNReal.ofReal (‖w i x - u x‖ ^ 2 * F x) ∂(volume : Measure (Fin d → ℂ)) :=
    fun i => lintegral_enorm_sq_withDensity_ofReal hFc hFnn (w i - u)
  have h' : Tendsto (fun i => ∫⁻ x, ‖w i x - u x‖ₑ ^ (2 : ℝ) ∂μ) l (nhds 0) := by
    rw [funext heq]
    exact h
  exact tendsto_norm_toLp_of_tendsto_lintegral_enorm_sq hmem humem h'

end Commons.MeasureTheory.Lp