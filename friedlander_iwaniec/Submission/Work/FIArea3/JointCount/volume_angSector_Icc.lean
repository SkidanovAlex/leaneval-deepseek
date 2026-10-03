import Mathlib
import Submission.Work.FIArea3.JointCount.angSector
import Submission.Work.FIArea3.JointCount.polarBand_volume

namespace Work.FIArea3.JointCount

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- For `-π ≤ α` and `β ≤ π`, the truncated interval `[α, β] ∩ (-π, π)` has linear measure `β - α`.
It differs from the half-open interval `(α, β] ∩ (-π, π)` only by the possible single point `α`. -/
lemma volume_Icc_inter_Ioo_pi (α β : ℝ) (hα : -Real.pi ≤ α) (hβ : β ≤ Real.pi) :
    MeasureTheory.volume (Set.Icc α β ∩ Set.Ioo (-Real.pi) Real.pi)
      = ENNReal.ofReal (β - α) := by
  set S : Set ℝ := Set.Icc α β ∩ Set.Ioo (-Real.pi) Real.pi with hS
  set T : Set ℝ := Set.Ioc α β ∩ Set.Ioo (-Real.pi) Real.pi with hT
  have hTS : T ⊆ S := by
    intro x hx
    rw [hT, Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ioo] at hx
    rw [hS, Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ioo]
    exact ⟨⟨hx.1.1.le, hx.1.2⟩, hx.2⟩
  have hdiff : S \ T ⊆ {α} := by
    rintro x ⟨hxS, hxT⟩
    rw [hS, Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ioo] at hxS
    simp only [Set.mem_singleton_iff]
    by_contra hne
    exact hxT (by
      rw [hT, Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ioo]
      exact ⟨⟨lt_of_le_of_ne hxS.1.1 (Ne.symm hne), hxS.1.2⟩, hxS.2⟩)
  have h0 : MeasureTheory.volume (S \ T) = 0 :=
    measure_mono_null hdiff (measure_singleton α)
  have hST : MeasureTheory.volume S = MeasureTheory.volume T :=
    (MeasureTheory.measure_eq_measure_of_null_sdiff hTS h0).symm
  have hTle : MeasureTheory.volume T ≤ ENNReal.ofReal (β - α) := by
    calc MeasureTheory.volume T ≤ MeasureTheory.volume (Set.Ioc α β) :=
          measure_mono Set.inter_subset_left
      _ = ENNReal.ofReal (β - α) := Real.volume_Ioc
  have hTge : ENNReal.ofReal (β - α) ≤ MeasureTheory.volume T := by
    rw [← Real.volume_Ioo (a := α) (b := β)]
    apply measure_mono
    intro x hx
    rw [Set.mem_Ioo] at hx
    rw [hT, Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ioo]
    exact ⟨⟨hx.1, hx.2.le⟩, lt_of_le_of_lt hα hx.1, lt_of_lt_of_le hx.2 hβ⟩
  have hTeq : MeasureTheory.volume T = ENNReal.ofReal (β - α) := le_antisymm hTle hTge
  rw [hS] at hST
  rw [hST, hTeq]

/-- Real-valued version of `volume_Icc_inter_Ioo_pi`. -/
lemma toReal_volume_Icc_inter_Ioo_pi (α β : ℝ) (hα : -Real.pi ≤ α) (hβ : β ≤ Real.pi)
    (hαβ : α ≤ β) :
    (MeasureTheory.volume (Set.Icc α β ∩ Set.Ioo (-Real.pi) Real.pi)).toReal = β - α := by
  rw [volume_Icc_inter_Ioo_pi α β hα hβ, ENNReal.toReal_ofReal (sub_nonneg.mpr hαβ)]

theorem volume_angSector_Icc (a b α β : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hα : -Real.pi ≤ α) (hβ : β ≤ Real.pi) (hαβ : α ≤ β) :
    MeasureTheory.volume (angSector a b (Set.Icc α β))
      = ENNReal.ofReal ((b ^ 2 - a ^ 2) / 2 * (β - α)) := by
  have hvol := polarBand_volume a b (Set.Icc α β) ha hab measurableSet_Icc
  unfold angSector
  rw [hvol, toReal_volume_Icc_inter_Ioo_pi α β hα hβ hαβ]

end

end Work.FIArea3.JointCount
