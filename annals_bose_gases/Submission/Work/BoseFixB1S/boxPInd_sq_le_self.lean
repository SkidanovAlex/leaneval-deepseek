import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.intAbsCS
import Submission.Work.BoseFixB1S.n0SumAqEqX
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open MeasureTheory
open scoped Real BigOperators

set_option maxHeartbeats 1000000

theorem boxPInd_sq_le_self {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (i : Fin N)
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨm : Measurable Ψ) {C : ℝ}
    (hΨb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Ψ x| ≤ C) :
    (∫ x in Submission.BoseGases.abox N ℓ, (Work.UBBInputs8.boxPInd volA A i Ψ x) ^ 2)
      ≤ ∫ x in Submission.BoseGases.abox N ℓ, (Ψ x) ^ 2 := by
  classical
  have hPm : Measurable (Work.UBBInputs8.boxPInd volA A i Ψ) :=
    measurable_boxPInd volA A hA i hΨm
  have hPb : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxPInd volA A i Ψ x| ≤ C :=
    abs_boxPInd_le hℓ hvol hA hvolA hAc i hΨb
  have hP2 : Integrable (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd volA A i Ψ x) ^ 2)
      ((MeasureTheory.volume : Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N ℓ)) := integrableOn_sq_of_bound hℓ hPm hPb
  have hΨ2 : Integrable (fun x : Submission.BoseGases.X N => (Ψ x) ^ 2)
      ((MeasureTheory.volume : Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N ℓ)) := integrableOn_sq_of_bound hℓ hΨm hΨb
  set s : ℝ := ∫ x in Submission.BoseGases.abox N ℓ,
      (Work.UBBInputs8.boxPInd volA A i Ψ x) ^ 2 with hs
  set t : ℝ := ∫ x in Submission.BoseGases.abox N ℓ, (Ψ x) ^ 2 with ht
  -- `Pᵢ` is an orthogonal projection: `∫ (PᵢΨ)² = ∫ Ψ·PᵢΨ`
  have hself : s = ∫ x in Submission.BoseGases.abox N ℓ,
      Ψ x * Work.UBBInputs8.boxPInd volA A i Ψ x := by
    rw [hs]
    exact n0Sum_pInd_sq_selfMul (N := N) (ℓ := ℓ) (volA := volA) hℓ hvol hA hvolA hAc i
      hΨm hΨb
  -- symmetric form of the same identity
  have hsym : s = ∫ x in Submission.BoseGases.abox N ℓ,
      Work.UBBInputs8.boxPInd volA A i Ψ x * Ψ x := by
    rw [hself]
    refine integral_congr_ae ?_
    filter_upwards with x
    ring
  -- Cauchy–Schwarz at the pair `(PᵢΨ, Ψ)`
  have hCS := int_abs_mul_le_sqrt_mul_sqrt
    (μ := (MeasureTheory.volume : Measure (Submission.BoseGases.X N)).restrict
      (Submission.BoseGases.abox N ℓ))
    hPm.aestronglyMeasurable hΨm.aestronglyMeasurable hP2 hΨ2
  -- `s ≤ √s·√t`
  have hbound : s ≤ Real.sqrt s * Real.sqrt t := by
    calc s = (∫ x in Submission.BoseGases.abox N ℓ,
          Work.UBBInputs8.boxPInd volA A i Ψ x * Ψ x) := hsym
      _ ≤ |∫ x in Submission.BoseGases.abox N ℓ,
            Work.UBBInputs8.boxPInd volA A i Ψ x * Ψ x| := le_abs_self _
      _ ≤ ∫ x in Submission.BoseGases.abox N ℓ,
            |Work.UBBInputs8.boxPInd volA A i Ψ x * Ψ x| := by
          simpa only [Real.norm_eq_abs] using
            (norm_integral_le_integral_norm
              (f := fun x : Submission.BoseGases.X N =>
                Work.UBBInputs8.boxPInd volA A i Ψ x * Ψ x)
              (μ := (MeasureTheory.volume : Measure (Submission.BoseGases.X N)).restrict
                (Submission.BoseGases.abox N ℓ)))
      _ ≤ Real.sqrt s * Real.sqrt t := by simpa only [hs, ht] using hCS
  have hs0 : 0 ≤ s := by
    rw [hs]
    exact integral_nonneg fun x => sq_nonneg _
  have ht0 : 0 ≤ t := by
    rw [ht]
    exact integral_nonneg fun x => sq_nonneg _
  -- the elementary arithmetic: `s ≤ √s·√t`, `s, t ≥ 0` ⟹ `s ≤ t`
  have hst : s ≤ t := by
    rcases eq_or_lt_of_le hs0 with h0 | hpos
    · rw [← h0]
      exact ht0
    · have hsqrt_pos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hpos
      have hmul : Real.sqrt s * Real.sqrt s ≤ Real.sqrt t * Real.sqrt s := by
        rw [← pow_two, Real.sq_sqrt hs0]
        calc s ≤ Real.sqrt s * Real.sqrt t := hbound
          _ = Real.sqrt t * Real.sqrt s := by ring
      have hle : Real.sqrt s ≤ Real.sqrt t := le_of_mul_le_mul_right hmul hsqrt_pos
      calc s = (Real.sqrt s) ^ 2 := (Real.sq_sqrt hs0).symm
        _ ≤ (Real.sqrt t) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hle 2
        _ = t := Real.sq_sqrt ht0
  calc (∫ x in Submission.BoseGases.abox N ℓ, (Work.UBBInputs8.boxPInd volA A i Ψ x) ^ 2)
      = s := hs.symm
    _ ≤ t := hst
    _ = ∫ x in Submission.BoseGases.abox N ℓ, (Ψ x) ^ 2 := ht

end Work.BoseFixB1S
