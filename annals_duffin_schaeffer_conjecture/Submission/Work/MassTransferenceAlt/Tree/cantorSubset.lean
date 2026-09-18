import Mathlib
import Submission.Work.MassTransferenceAlt.Tree.Data
import Submission.Work.MassTransferenceAlt.Tree.childrenMem

namespace Work.MassTransferenceAlt.Tree

open Work.MassTransferenceAlt

/-- The balls of level `n` are among the indices used by level `n`. -/
lemma lev_subset_used {d : ℝ} {c ρ : ℕ → ℝ} {η : ℝ} (T : TreeData d c ρ η) (n : ℕ) :
    T.lev n ⊆ T.used n := by
  induction n with
  | zero => rw [T.used_zero]
  | succ n ih =>
      rw [T.used_succ]
      exact fun i hi => Finset.mem_union_right _ hi

/-- The sets of used indices are monotone in the level. -/
lemma used_mono {d : ℝ} {c ρ : ℕ → ℝ} {η : ℝ} (T : TreeData d c ρ η) {a b : ℕ}
    (hab : a ≤ b) : T.used a ⊆ T.used b := by
  induction hab with
  | refl => exact Finset.Subset.refl _
  | step hab ih =>
      refine ih.trans ?_
      rw [T.used_succ]
      exact Finset.subset_union_left

/-- Every point of the Cantor set lies in a ball of every level. -/
lemma exists_mem_lev_of_mem_cantor {d : ℝ} {c ρ : ℕ → ℝ} {η : ℝ} (T : TreeData d c ρ η)
    {z : ℝ} (hz : z ∈ cantor T) (n : ℕ) :
    ∃ i ∈ T.lev n, z ∈ Iv (c i) (ρ i) := by
  have h := cantor_subset_levSet T n hz
  simp only [levSet, Set.mem_iUnion] at h
  obtain ⟨i, h'⟩ := h
  obtain ⟨hi, hzi⟩ := h'
  exact ⟨i, hi, hzi⟩

/-- **The Cantor set lies in the small limsup set.** -/
theorem cantorSubset (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1) (c ρ : ℕ → ℝ) (η : ℝ)
    (T : Work.MassTransferenceAlt.TreeData d c ρ η) :
    Work.MassTransferenceAlt.cantor T ⊆
      (Set.Icc (0:ℝ) 1 ∩
        {z : ℝ | {i : ℕ | 0 < ρ i ∧ |z - c i| ≤ ρ i}.Infinite}) := by
  intro z hz
  -- `z` belongs to a ball of every level of the tree
  have hball : ∀ n, ∃ i ∈ T.lev n, z ∈ Iv (c i) (ρ i) :=
    fun n => exists_mem_lev_of_mem_cantor T hz n
  constructor
  · -- the ball of level `0` is contained in `[0,1]`
    obtain ⟨i, hi, hzi⟩ := hball 0
    have hg := T.good 0 i hi
    rw [mem_Iv] at hzi
    rw [Set.mem_Icc]
    obtain ⟨ha, hb⟩ := abs_le.mp hzi
    constructor <;> linarith [hg.2.2.1, hg.2.2.2]
  · -- the balls through `z` have pairwise distinct indices, one per level
    classical
    choose f hf_mem hf_iv using hball
    have hf_inj : Function.Injective f := by
      have key : ∀ {m n : ℕ}, m < n → f m ≠ f n := by
        intro m n hmn
        have hn1 : 1 ≤ n := by omega
        -- the ball of level `n` is fresh at level `n`
        have hfn : f n ∉ T.used (n - 1) := by
          have h1 : f n ∈ T.lev ((n - 1) + 1) := by
            rw [Nat.sub_add_cancel hn1]; exact hf_mem n
          exact T.fresh (n - 1) (f n) h1
        -- the ball of level `m < n` was already used at level `n`
        have hfm : f m ∈ T.used (n - 1) :=
          (used_mono T (by omega)) (lev_subset_used T m (hf_mem m))
        intro hEq
        exact hfn (hEq ▸ hfm)
      intro m n hmn
      rcases lt_trichotomy m n with h | h | h
      · exact absurd hmn (key h)
      · exact h
      · exact absurd hmn.symm (key h)
    refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective hf_inj)
    intro y hy
    obtain ⟨k, rfl⟩ := hy
    refine ⟨(T.good k (f k) (hf_mem k)).1, ?_⟩
    have h := hf_iv k
    rwa [mem_Iv] at h

end Work.MassTransferenceAlt.Tree
