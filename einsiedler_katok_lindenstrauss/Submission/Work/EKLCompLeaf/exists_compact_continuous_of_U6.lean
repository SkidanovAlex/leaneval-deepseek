import Mathlib
import Submission.Work.EKLComp.C8Defs

/-!
# `Work.EKLCompLeaf.exists_compact_continuous_of_U6`

`U6clause` (the Luzin clause of `P_Leafwise` at `U = U_01`) already provides, for every
`ε > 0`, a compact `K ⊆ X'` with `μ Kᶜ < ε` on which every map
`x ↦ ∫ g, f g ∂(ν x)` (`f` compactly supported continuous) is continuous.

The requested statement is the special case `ε = η` together with the arithmetic
conversion `μ Kᶜ < η  ⟹  1 - η < (μ K).toReal`, which uses only that `μ` is a probability
measure.  No hypothesis on `ν` (in particular no local finiteness) is needed for *these*
conclusions: the values `∫ g, f g ∂(ν x)` are already handed to us as a function known to be
continuous on `K`.

(Note: strengthening the conclusion by additionally demanding `ν`-equality of limits along
`X₁` is *not* a consequence of `U6clause` alone — see
`Submission/Work/EKLCompLeaf/luzin_riesz.lean` — but that extra clause is not part of this
lemma.)
-/

open scoped ENNReal

namespace Work.EKLCompLeaf

theorem exists_compact_continuous_of_U6
    {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' : Set Work.EKLContract.X3}
    (hU6 : Work.EKLComp.U6clause μ ν X') (η : ℝ) (hη : 0 < η) :
    ∃ X₁ : Set Work.EKLContract.X3, IsCompact X₁ ∧ X₁ ⊆ X' ∧ 1 - η < (μ X₁).toReal ∧
      (∀ f : CompactlySupportedContinuousMap Work.EKLContract.SL3 ℝ,
        ContinuousOn (fun x => ∫ g, f g ∂(ν x)) X₁) := by
  classical
  obtain ⟨K, hKc, hKsub, hKμ, hKcont⟩ :=
    hU6 (ENNReal.ofReal η) (ENNReal.ofReal_pos.mpr hη)
  refine ⟨K, hKc, hKsub, ?_, hKcont⟩
  have hηnn : 0 ≤ η := le_of_lt hη
  -- `μ Kᶜ` is finite, because it is `< ENNReal.ofReal η < ⊤`.
  have hcompl_ne_top : μ Kᶜ ≠ ⊤ := ne_top_of_lt hKμ
  -- `μ K` is finite, because `μ K ≤ μ univ = 1`.
  have hK_ne_top : μ K ≠ ⊤ := by
    have hle : μ K ≤ μ Set.univ := MeasureTheory.measure_mono (Set.subset_univ K)
    rw [MeasureTheory.measure_univ] at hle
    exact ne_top_of_le_ne_top ENNReal.one_ne_top hle
  -- `1 ≤ μ K + μ Kᶜ` (subadditivity along `K ∪ Kᶜ = univ`).
  have hone : (1 : ℝ≥0∞) ≤ μ K + μ Kᶜ := by
    have h := MeasureTheory.measure_union_le (μ := μ) K Kᶜ
    rwa [Set.union_compl_self, MeasureTheory.measure_univ] at h
  -- hence `1 ≤ (μ K).toReal + (μ Kᶜ).toReal`.
  have hone' : (1 : ℝ) ≤ (μ K).toReal + (μ Kᶜ).toReal := by
    have hne : μ K + μ Kᶜ ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hK_ne_top, hcompl_ne_top⟩
    have h := ENNReal.toReal_mono hne hone
    rwa [ENNReal.toReal_add hK_ne_top hcompl_ne_top, ENNReal.toReal_one] at h
  -- and `(μ Kᶜ).toReal < η`.
  have hcompl_lt : (μ Kᶜ).toReal < η := by
    have h := (ENNReal.toReal_lt_toReal hcompl_ne_top ENNReal.ofReal_ne_top).mpr hKμ
    rwa [ENNReal.toReal_ofReal hηnn] at h
  linarith

end Work.EKLCompLeaf
