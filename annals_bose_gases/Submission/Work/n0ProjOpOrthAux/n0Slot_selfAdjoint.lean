import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.boxPIndSelfAdjoint
import Submission.Work.BoseFixB1S.n0IterEigen
import Submission.Work.BoseFixB1S.n0SlotDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory

namespace Work.n0ProjOpOrthAux

theorem n0Slot_selfAdjoint {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (b : Fin N → Bool) (i : Fin N) {Φ Ψ : Submission.BoseGases.X N → ℝ}
    (hΦ : Work.BoseFixB1S.GoodState ℓ Φ) (hΨ : Work.BoseFixB1S.GoodState ℓ Ψ) :
    (∫ x in Submission.BoseGases.abox N ℓ, Work.BoseFixB1S.n0Slot volA A b i Φ x * Ψ x)
      = ∫ x in Submission.BoseGases.abox N ℓ, Φ x * Work.BoseFixB1S.n0Slot volA A b i Ψ x := by
  obtain ⟨hΦm, CΦ, hΦb⟩ := hΦ
  obtain ⟨hΨm, CΨ, hΨb⟩ := hΨ
  by_cases h : b i = true
  · -- the `true` branch is the FS box projection: self-adjoint by `boxPIndSelfAdjoint`
    rw [Work.BoseFixB1S.n0Slot_eq_true volA A b i Φ h,
      Work.BoseFixB1S.n0Slot_eq_true volA A b i Ψ h]
    exact Work.BoseFixB1S.boxPIndSelfAdjoint hℓ hvol hA hvolA hAc i hΦm hΦb hΨm hΨb
  · -- the `false` branch is `1 − P_{B,i}`: split both sides with `integral_sub`
    have hb : b i = false := by simpa using h
    rw [Work.BoseFixB1S.n0Slot_eq_false volA A b i Φ hb,
      Work.BoseFixB1S.n0Slot_eq_false volA A b i Ψ hb]
    have hInt1 : IntegrableOn (fun x : Submission.BoseGases.X N => Φ x * Ψ x)
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume :=
      Work.BoseFixB1S.integrableOn_mul_of_bound hℓ hΦm hΨm hΦb hΨb
    have hInt2 : IntegrableOn
        (fun x : Submission.BoseGases.X N => Work.UBBInputs8.boxPInd volA A i Φ x * Ψ x)
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume :=
      Work.BoseFixB1S.integrableOn_mul_of_bound hℓ
        (Work.BoseFixB1S.measurable_boxPInd volA A hA i hΦm) hΨm
        (Work.BoseFixB1S.abs_boxPInd_le hℓ hvol hA hvolA hAc i hΦb) hΨb
    have hInt3 : IntegrableOn
        (fun x : Submission.BoseGases.X N => Φ x * Work.UBBInputs8.boxPInd volA A i Ψ x)
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume :=
      Work.BoseFixB1S.integrableOn_mul_of_bound hℓ hΦm
        (Work.BoseFixB1S.measurable_boxPInd volA A hA i hΨm) hΦb
        (Work.BoseFixB1S.abs_boxPInd_le hℓ hvol hA hvolA hAc i hΨb)
    have hadj := Work.BoseFixB1S.boxPIndSelfAdjoint hℓ hvol hA hvolA hAc i hΦm hΦb hΨm hΨb
    simp only [Pi.sub_apply]
    calc (∫ x in Submission.BoseGases.abox N ℓ,
            (Φ x - Work.UBBInputs8.boxPInd volA A i Φ x) * Ψ x)
        = ∫ x in Submission.BoseGases.abox N ℓ,
            (Φ x * Ψ x - Work.UBBInputs8.boxPInd volA A i Φ x * Ψ x) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          ring
      _ = (∫ x in Submission.BoseGases.abox N ℓ, Φ x * Ψ x)
            - ∫ x in Submission.BoseGases.abox N ℓ,
                Work.UBBInputs8.boxPInd volA A i Φ x * Ψ x := by
          rw [MeasureTheory.integral_sub hInt1 hInt2]
      _ = (∫ x in Submission.BoseGases.abox N ℓ, Φ x * Ψ x)
            - ∫ x in Submission.BoseGases.abox N ℓ,
                Φ x * Work.UBBInputs8.boxPInd volA A i Ψ x := by
          rw [hadj]
      _ = ∫ x in Submission.BoseGases.abox N ℓ,
            (Φ x * Ψ x - Φ x * Work.UBBInputs8.boxPInd volA A i Ψ x) := by
          rw [MeasureTheory.integral_sub hInt1 hInt3]
      _ = ∫ x in Submission.BoseGases.abox N ℓ,
            Φ x * (Ψ x - Work.UBBInputs8.boxPInd volA A i Ψ x) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          ring

end Work.n0ProjOpOrthAux
