/-
`L²`-membership of the formal adjoint `pertAdj A φ g`.

The formal adjoint of the perturbed `∂̄`-operator is smooth with compact support as soon as `A`,
`φ` and `g` are smooth and `g` has compact support (`Submission.Work.NN.Assemble.pertAdjRegular`).
Since the weighted measure `wMeas n φ = e^{-φ} dz` is finite on compact sets whenever `φ` is
continuous, a continuous compactly supported function lies in `L²` of it
(`MeasureTheory.Continuous.memLp_of_hasCompactSupport`).  This file records the missing
"finite on compacts" input and draws the conclusion.
-/
import Mathlib
import Submission.Work.NN.Core.PertL2Defs
import Submission.Work.NN.Assemble.pertAdjRegular

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff ENNReal NNReal

namespace Work.NN.Core

/-- The weighted measure `wMeas n φ = e^{-φ} dz` is finite on compact sets as soon as the weight
`φ` is continuous: on a compact set `K` the density `e^{-φ}` is bounded above by its value at a
point of `K`, and `volume K < ∞`. -/
theorem wMeas_isFiniteMeasureOnCompacts {n : ℕ} {φ : Work.NN.Assemble.Cn n → ℝ}
    (hφ : Continuous φ) :
    MeasureTheory.IsFiniteMeasureOnCompacts (Work.NN.Core.wMeas n φ) := by
  refine ⟨fun K hK => ?_⟩
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨x, _hxK, hxmax⟩ := hK.exists_isMaxOn hne (continuous_neg.comp_continuousOn hφ.continuousOn)
  rw [Work.NN.Core.wMeas, withDensity_apply _ hK.measurableSet]
  have hpoint : ∀ z ∈ K, (((Real.exp (-(φ z))).toNNReal : ℝ≥0) : ℝ≥0∞)
      ≤ ((Real.exp (-(φ x))).toNNReal : ℝ≥0∞) := by
    intro z hz
    have h1 : -φ z ≤ -φ x := hxmax hz
    have h2 : Real.exp (-(φ z)) ≤ Real.exp (-(φ x)) := Real.exp_le_exp.mpr h1
    exact ENNReal.coe_le_coe.mpr (Real.toNNReal_le_toNNReal h2)
  calc ∫⁻ z in K, (((Real.exp (-(φ z))).toNNReal : ℝ≥0) : ℝ≥0∞) ∂volume
      ≤ ∫⁻ _z in K, ((Real.exp (-(φ x))).toNNReal : ℝ≥0∞) ∂volume :=
        setLIntegral_mono measurable_const hpoint
    _ = ((Real.exp (-(φ x))).toNNReal : ℝ≥0∞) * volume K := setLIntegral_const _ _
    _ < (⊤ : ℝ≥0∞) := ENNReal.mul_lt_top ENNReal.coe_lt_top hK.measure_lt_top

theorem memLp_pertAdj {n : ℕ} {φ : Work.NN.Assemble.Cn n → ℝ}
    (hφ : ∀ m : ℕ, ContDiff ℝ m φ)
    {A : Work.NN.Assemble.Cn n → Work.NN.Assemble.Cn n →L[ℝ] Work.NN.Assemble.Cn n}
    (hA : ∀ m : ℕ, ContDiff ℝ m A)
    {g : Work.NN.Assemble.Cn n → Work.NN.Assemble.Cn n →L[ℝ] ℂ}
    (hg : ∀ m : ℕ, ContDiff ℝ m g) (hgs : HasCompactSupport g) :
    MeasureTheory.MemLp (Work.NN.Assemble.pertAdj A φ g) 2 (Work.NN.Core.wMeas n φ) := by
  obtain ⟨hcont, hcs⟩ := Work.NN.Assemble.pertAdjRegular hA hφ hg hgs
  haveI : MeasureTheory.IsFiniteMeasureOnCompacts (Work.NN.Core.wMeas n φ) :=
    wMeas_isFiniteMeasureOnCompacts (hφ 0).continuous
  exact (hcont 0).continuous.memLp_of_hasCompactSupport hcs

end Work.NN.Core
