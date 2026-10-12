import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.BoxPIndFlat
import Submission.Work.BoseFixB1S.BoxQIndCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

/-! ## The abstract integral AM–GM -/

/-- **AM–GM for integrals.**  For real functions `φ`, `ψ` with integrable squares and integrable
product over a measure space,

    `∫ φ ψ ≤ (∫ φ² + ∫ ψ²) / 2`.

Pointwise `2 φ x ψ x ≤ φ x² + ψ x²` (the difference is `(φ x − ψ x)²`), integrated. -/
theorem integral_mul_le_half_sq_add {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {φ ψ : α → ℝ} (hφ : MeasureTheory.Integrable (fun x => φ x ^ 2) μ)
    (hψ : MeasureTheory.Integrable (fun x => ψ x ^ 2) μ)
    (hφψ : MeasureTheory.Integrable (fun x => φ x * ψ x) μ) :
    (∫ x, φ x * ψ x ∂μ) ≤ ((∫ x, φ x ^ 2 ∂μ) + (∫ x, ψ x ^ 2 ∂μ)) / 2 := by
  have hpt : ∀ x : α, 2 * (φ x * ψ x) ≤ φ x ^ 2 + ψ x ^ 2 := by
    intro x
    nlinarith [sq_nonneg (φ x - ψ x)]
  have hL : MeasureTheory.Integrable (fun x : α => 2 * (φ x * ψ x)) μ := hφψ.const_mul 2
  have hR : MeasureTheory.Integrable (fun x : α => φ x ^ 2 + ψ x ^ 2) μ := hφ.add hψ
  have hmono := MeasureTheory.integral_mono hL hR hpt
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hφ hψ] at hmono
  linarith

/-! ## The mixed pair AM–GM -/

theorem boxPairMixedAvgLe {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {i j : Fin N} (hij : i ≠ j) {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x) ^ 2)
      ≤ ((∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)
        + (∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxPInd volA A j Φ x) ^ 2)) / 2 := by
  -- a bound of `Φ` on the (compact) box
  obtain ⟨C, hC⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn
    (s := abox N ℓ) (f := Φ) hΦc.continuousOn
  have hbound : ∀ x ∈ abox N ℓ, |Φ x| ≤ |C| := by
    intro x hx
    have h := hC x hx
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_abs_self C)
  -- structural facts about the two projections
  have hmPi : Measurable (Work.UBBInputs8.boxPInd volA A i Φ) :=
    measurable_boxPInd volA A hA i hΦc.measurable
  have hmPj : Measurable (Work.UBBInputs8.boxPInd volA A j Φ) :=
    measurable_boxPInd volA A hA j hΦc.measurable
  have hbPi : ∀ x ∈ abox N ℓ, |Work.UBBInputs8.boxPInd volA A i Φ x| ≤ |C| :=
    abs_boxPInd_le hℓ hvol hA hvolA hAc i hbound
  have hbPj : ∀ x ∈ abox N ℓ, |Work.UBBInputs8.boxPInd volA A j Φ x| ≤ |C| :=
    abs_boxPInd_le hℓ hvol hA hvolA hAc j hbound
  have hIpi : IntegrableOn (fun x : X N => (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)
      (abox N ℓ) volume := integrableOn_sq_of_bound (N := N) hℓ hmPi hbPi
  have hIpj : IntegrableOn (fun x : X N => (Work.UBBInputs8.boxPInd volA A j Φ x) ^ 2)
      (abox N ℓ) volume := integrableOn_sq_of_bound (N := N) hℓ hmPj hbPj
  have hIij : IntegrableOn (fun x : X N =>
      Work.UBBInputs8.boxPInd volA A i Φ x * Work.UBBInputs8.boxPInd volA A j Φ x)
      (abox N ℓ) volume :=
    integrableOn_mul_of_bound (N := N) hℓ hmPi hmPj hbPi hbPj
  -- the two-slot peel, in `Measure.real` form
  have hvolA' : volA = (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))).real A := by
    rw [MeasureTheory.Measure.real_def]
    exact hvolA
  have hpair := Q0C.pair_mixed_N (volA := volA) hℓ hvol hA hvolA' hAc hij hΦc
  rw [← hpair]
  exact integral_mul_le_half_sq_add hIpi hIpj hIij

end Work.BoseFixB1S
