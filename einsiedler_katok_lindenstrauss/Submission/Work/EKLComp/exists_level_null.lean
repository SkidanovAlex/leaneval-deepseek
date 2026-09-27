import Mathlib
import Submission.Work.EKLComp.USCBasic

namespace Work.EKLComp

theorem exists_level_null (μ : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsProbabilityMeasure μ] {m : ℕ} (Φ : Fin m → Work.EKLContract.X3 → ℝ) (hΦ : ∀ i, Measurable (Φ i)) : ∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∀ i, μ (Φ i ⁻¹' ({c} : Set ℝ)) = 0 := by
  -- For each `i`, only countably many levels `c` carry positive mass.
  have hB : (⋃ i, {c : ℝ | 0 < μ (Φ i ⁻¹' ({c} : Set ℝ))}).Countable := by
    apply Set.countable_iUnion
    intro i
    have h := MeasureTheory.Measure.countable_meas_level_set_pos (μ := μ) (g := Φ i) (hΦ i)
    refine h.mono ?_
    intro c hc
    simp only [Set.mem_ofPred_eq] at hc ⊢
    have hset : Φ i ⁻¹' ({c} : Set ℝ) = {a | Φ i a = c} := by ext a; simp
    rw [hset] at hc
    exact hc
  -- Hence `(0,1)` cannot be covered by the bad levels, since `(0,1)` is uncountable.
  have hnotsub : ¬ (Set.Ioo (0:ℝ) 1 ⊆ (⋃ i, {c : ℝ | 0 < μ (Φ i ⁻¹' ({c} : Set ℝ))})) := by
    intro hsub
    have hcnt : (Set.Ioo (0:ℝ) 1).Countable := hB.mono hsub
    rw [Cardinal.Real.Ioo_countable_iff] at hcnt
    norm_num at hcnt
  rw [Set.not_subset] at hnotsub
  obtain ⟨c, hcA, hcB⟩ := hnotsub
  refine ⟨c, hcA.1, hcA.2, fun i => ?_⟩
  have hci : c ∉ ({c : ℝ | 0 < μ (Φ i ⁻¹' ({c} : Set ℝ))}) :=
    fun hh => hcB (Set.mem_iUnion.mpr ⟨i, hh⟩)
  simp only [Set.mem_ofPred_eq] at hci
  exact le_antisymm (not_lt.mp hci) zero_le

end Work.EKLComp
