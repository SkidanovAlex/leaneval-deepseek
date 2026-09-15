import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

open MeasureTheory Metric Filter
open scoped ENNReal BigOperators ContDiff

set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {d : ℕ}
local notation "ℂᵈ" => (Fin d → ℂ)

/-!
# The weighted Lebesgue measure `e^{-φ} dvol` of Cohen's §5

This module sets up the measure-theoretic infrastructure used to state Hörmander's `∂̄`-theorem in
its `L²` form: the weighted measure `μ_φ = e^{-φ} · volume` on `ℂᵈ`, the formula
`∫ g ∂μ_φ = ∫ g · e^{-φ}` identifying its Bochner integral with the weighted Lebesgue integral,
local finiteness, and the fact that `MemLp` elements are locally integrable (so that the
fundamental lemma of the calculus of variations applies to them).
-/

namespace Submission.FUP

/-- The density `e^{-φ}` as an `ℝ≥0∞`-valued function. -/
noncomputable def wtDensity (φ : ℂᵈ → ℝ) (z : ℂᵈ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(φ z)))

/-- The weighted Lebesgue measure `e^{-φ} dvol`. -/
noncomputable def wtMeasure (φ : ℂᵈ → ℝ) : Measure ℂᵈ := volume.withDensity (wtDensity φ)

@[simp] lemma wtDensity_apply (φ : ℂᵈ → ℝ) (z : ℂᵈ) :
    wtDensity φ z = ENNReal.ofReal (Real.exp (-(φ z))) := rfl

lemma measurable_wtDensity (φ : ℂᵈ → ℝ) (hφ : Continuous φ) : Measurable (wtDensity φ) :=
  ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp hφ.neg.measurable)

lemma wtDensity_lt_top (φ : ℂᵈ → ℝ) (z : ℂᵈ) : wtDensity φ z < ⊤ := ENNReal.ofReal_lt_top

lemma toReal_wtDensity (φ : ℂᵈ → ℝ) (z : ℂᵈ) :
    (wtDensity φ z).toReal = Real.exp (-(φ z)) :=
  ENNReal.toReal_ofReal (Real.exp_nonneg _)

/-- The Bochner integral against `μ_φ = e^{-φ}dvol` is the weighted Lebesgue integral. -/
lemma integral_wtMeasure {φ : ℂᵈ → ℝ} (hφ : Continuous φ) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (g : ℂᵈ → E) :
    ∫ z, g z ∂(wtMeasure φ) = ∫ z, Real.exp (-(φ z)) • g z := by
  rw [wtMeasure, integral_withDensity_eq_integral_toReal_smul (measurable_wtDensity φ hφ)
    (Eventually.of_forall (wtDensity_lt_top φ))]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  show (wtDensity φ z).toReal • g z = Real.exp (-(φ z)) • g z
  rw [toReal_wtDensity]

/-- The `ℝ≥0∞`-valued integral over `μ_φ`. -/
lemma lintegral_wtMeasure {φ : ℂᵈ → ℝ} (hφ : Continuous φ) (g : ℂᵈ → ℝ≥0∞) :
    ∫⁻ z, g z ∂(wtMeasure φ) = ∫⁻ z, wtDensity φ z * g z := by
  have h := lintegral_withDensity_eq_lintegral_mul_non_measurable volume
    (measurable_wtDensity φ hφ) (Eventually.of_forall fun z => wtDensity_lt_top φ z) g
  simpa only [wtMeasure, Pi.mul_apply] using h

lemma wtMeasure_apply (φ : ℂᵈ → ℝ) {s : Set ℂᵈ} (hs : MeasurableSet s) :
    wtMeasure φ s = ∫⁻ z in s, wtDensity φ z := by
  rw [wtMeasure, withDensity_apply _ hs]

lemma wtMeasure_absolutelyContinuous (φ : ℂᵈ → ℝ) : wtMeasure φ ≪ volume := by
  rw [wtMeasure]; exact withDensity_absolutelyContinuous _ _

/-- `μ_φ` gives every closed ball finite measure (for a continuous weight `φ`). -/
lemma wtMeasure_closedBall_lt_top {φ : ℂᵈ → ℝ} (hφ : Continuous φ) (x : ℂᵈ) (r : ℝ) :
    wtMeasure φ (closedBall x r) < ⊤ := by
  rcases (isCompact_closedBall x r).exists_bound_of_continuousOn hφ.neg.continuousOn with ⟨C, hC⟩
  have hbound : ∀ z ∈ closedBall x r, Real.exp (-(φ z)) ≤ Real.exp C := by
    intro z hz
    have h1 : -(φ z) ≤ C := by
      have h2 := hC z hz
      rw [Real.norm_eq_abs] at h2
      exact le_trans (le_abs_self _) h2
    exact Real.exp_le_exp.mpr h1
  rw [wtMeasure_apply φ measurableSet_closedBall]
  calc ∫⁻ z in closedBall x r, wtDensity φ z
      ≤ ∫⁻ _ in closedBall x r, ENNReal.ofReal (Real.exp C) :=
        setLIntegral_mono' measurableSet_closedBall fun z hz =>
          ENNReal.ofReal_le_ofReal (hbound z hz)
    _ = ENNReal.ofReal (Real.exp C) * volume (closedBall x r) := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (measure_closedBall_lt_top (μ := volume))

/-- `μ_φ` is a locally finite measure (for a continuous weight `φ`). -/
theorem isLocallyFiniteMeasure_wtMeasure {φ : ℂᵈ → ℝ} (hφ : Continuous φ) :
    IsLocallyFiniteMeasure (wtMeasure φ) :=
  ⟨fun x => ⟨closedBall x 1, closedBall_mem_nhds x one_pos, wtMeasure_closedBall_lt_top hφ x 1⟩⟩

/-- `μ_φ` is finite on compact sets (for a continuous weight `φ`). -/
theorem isFiniteMeasureOnCompacts_wtMeasure {φ : ℂᵈ → ℝ} (hφ : Continuous φ) :
    IsFiniteMeasureOnCompacts (wtMeasure φ) := by
  refine ⟨fun K hK => ?_⟩
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn (continuous_norm.continuousOn)
  have hsub : K ⊆ closedBall (0 : ℂᵈ) (max R 0) := fun z hz =>
    mem_closedBall_zero_iff.mpr (le_trans (by simpa using hR z hz) (le_max_left _ _))
  exact lt_of_le_of_lt (measure_mono hsub) (wtMeasure_closedBall_lt_top hφ 0 (max R 0))

/-- A smooth compactly supported function lies in `L²(μ_φ)`. -/
lemma memLp_wtMeasure_of_contDiff_hasCompactSupport {φ : ℂᵈ → ℝ} (hφ : Continuous φ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ψ : ℂᵈ → E} (h1 : ContDiff ℝ ∞ ψ)
    (h2 : HasCompactSupport ψ) :
    MemLp ψ 2 (wtMeasure φ) := by
  haveI : IsFiniteMeasureOnCompacts (wtMeasure φ) := isFiniteMeasureOnCompacts_wtMeasure hφ
  have hcs : HasCompactSupport (fun z : ℂᵈ => ‖ψ z‖ ^ 2) :=
    h2.mono' fun z hz => subset_tsupport ψ (Function.mem_support.mpr fun h => hz (by simp [h]))
  have hint : Integrable (fun z : ℂᵈ => ‖ψ z‖ ^ 2) (wtMeasure φ) :=
    (h1.continuous.norm.pow 2).integrable_of_hasCompactSupport hcs
  exact (memLp_two_iff_integrable_sq_norm h1.continuous.aestronglyMeasurable).mpr hint


/-- A continuous compactly supported function lies in `L²(μ_φ)`. -/
lemma memLp_wtMeasure_of_continuous_hasCompactSupport {φ : ℂᵈ → ℝ} (hφ : Continuous φ)
    {E : Type*} [NormedAddCommGroup E] {ψ : ℂᵈ → E} (h1 : Continuous ψ)
    (h2 : HasCompactSupport ψ) :
    MemLp ψ 2 (wtMeasure φ) := by
  haveI : IsFiniteMeasureOnCompacts (wtMeasure φ) := isFiniteMeasureOnCompacts_wtMeasure hφ
  exact h1.memLp_of_hasCompactSupport h2

end Submission.FUP
