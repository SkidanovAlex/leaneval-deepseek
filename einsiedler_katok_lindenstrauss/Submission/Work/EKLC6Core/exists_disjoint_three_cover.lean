import Mathlib

/-!
# `Work.EKLC6Core.exists_disjoint_three_cover`

A one-dimensional Vitali-type covering lemma for the exceptional-set estimates of
Einsiedler–Katok–Lindenstrauss:

> if a finite family of open intervals `(p.1, p.2)` covers the closed interval `[a, b]`, then a
> pairwise disjoint subfamily `T` with total length at least `(b - a) / 3` can be extracted.

The proof has three ingredients.

* `Ioo_subset_Ioo_triple` — the classical `3`-times trick: two intersecting intervals, the shorter
  of which is contained in the interval obtained by dilating the longer one by the factor `3`
  about its centre.
* `exists_disjoint_maxLen_subfamily` — the greedy selection (recursion on the cardinality, always
  taking a longest interval disjoint from those already selected) of a pairwise disjoint
  subfamily `T ⊆ S` such that every member of `S` meets some member of `T` of at least the same
  length.
* `le_sum_of_Icc_subset_iUnion_Ioo` — if a finite family of open intervals covers `[a, b]`, its
  total length is at least `b - a` (proved by induction: remove an interval covering the left end
  `a` and restart at its right end).

Combining the last two: `[a, b]` is covered by the `3`-dilates of the members of `T`, whose total
length is at most `∑_{q ∈ T} 3 * (q.2 - q.1)`.
-/

open Set

namespace Work.EKLC6Core

/-- **A finite open cover of a closed interval has total length at least its span.**

If `F` is a finite family of open intervals `(l i, r i)` (with `l i < r i`) whose union covers
`[a, b]`, then `b - a ≤ ∑ i ∈ F, (r i - l i)`. -/
theorem le_sum_of_Icc_subset_iUnion_Ioo {ι : Type*} (l r : ι → ℝ) :
    ∀ (F : Finset ι) {a b : ℝ}, (∀ i ∈ F, l i < r i) →
      (Set.Icc a b ⊆ ⋃ i ∈ F, Set.Ioo (l i) (r i)) → b - a ≤ ∑ i ∈ F, (r i - l i) := by
  classical
  intro F
  induction F using Finset.strongInductionOn with
  | _ F ih =>
    intro a b hlt hcov
    by_cases hab : a ≤ b
    · -- an interval of `F` covers the left endpoint `a`
      obtain ⟨p, hpF, hp_mem⟩ :=
        Set.mem_iUnion₂.mp (hcov (Set.mem_Icc.mpr ⟨le_rfl, hab⟩))
      obtain ⟨hlp, har⟩ := Set.mem_Ioo.mp hp_mem
      rcases le_or_gt b (r p) with hbr | hrb
      · -- `b` is still inside that interval
        have h1 : b - a ≤ r p - l p := by linarith
        have h2 : r p - l p ≤ ∑ i ∈ F, (r i - l i) :=
          Finset.single_le_sum (fun i hi => sub_nonneg.mpr (le_of_lt (hlt i hi))) hpF
        linarith
      · -- restart the cover at the right endpoint of that interval
        have hsub : F.erase p ⊂ F := Finset.erase_ssubset hpF
        have hlt' : ∀ i ∈ F.erase p, l i < r i := fun i hi => hlt i (Finset.mem_of_mem_erase hi)
        have hcov' : Set.Icc (r p) b ⊆ ⋃ i ∈ F.erase p, Set.Ioo (l i) (r i) := by
          intro x hx
          obtain ⟨hx1, hx2⟩ := Set.mem_Icc.mp hx
          obtain ⟨i, hiF, hxi⟩ :=
            Set.mem_iUnion₂.mp (hcov (Set.mem_Icc.mpr ⟨by linarith, hx2⟩))
          refine Set.mem_iUnion₂.mpr ⟨i, ?_, hxi⟩
          rcases eq_or_ne i p with rfl | hne
          · exact absurd hxi.2 (not_lt.mpr hx1)
          · exact Finset.mem_erase.mpr ⟨hne, hiF⟩
        have ih' : b - r p ≤ ∑ i ∈ F.erase p, (r i - l i) := ih (F.erase p) hsub hlt' hcov'
        have hsum : ∑ i ∈ F, (r i - l i) = (∑ i ∈ F.erase p, (r i - l i)) + (r p - l p) := by
          rw [← Finset.sum_erase_add F (fun i => r i - l i) hpF]
        calc b - a = (b - r p) + (r p - a) := by ring
          _ ≤ (b - r p) + (r p - l p) := by linarith
          _ ≤ (∑ i ∈ F.erase p, (r i - l i)) + (r p - l p) := by linarith
          _ = ∑ i ∈ F, (r i - l i) := hsum.symm
    · -- `a > b`: then `b - a < 0` and the sum is nonnegative
      rw [not_le] at hab
      have h0 : 0 ≤ ∑ i ∈ F, (r i - l i) :=
        Finset.sum_nonneg (fun i hi => sub_nonneg.mpr (le_of_lt (hlt i hi)))
      linarith

/-- **The `3`-times trick.** If the open intervals `(p.1, p.2)` and `(q.1, q.2)` meet and `p` is
no longer than `q`, then `(p.1, p.2)` is contained in the interval with the same centre as
`(q.1, q.2)` and three times its length. -/
theorem Ioo_subset_Ioo_triple {p q : ℝ × ℝ} (hlen : p.2 - p.1 ≤ q.2 - q.1)
    (hne : ¬ Disjoint (Set.Ioo p.1 p.2) (Set.Ioo q.1 q.2)) :
    Set.Ioo p.1 p.2 ⊆ Set.Ioo (q.1 - (q.2 - q.1)) (q.2 + (q.2 - q.1)) := by
  obtain ⟨y, hy1, hy2⟩ := Set.not_disjoint_iff.mp hne
  obtain ⟨hyp1, hyp2⟩ := Set.mem_Ioo.mp hy1
  obtain ⟨hyq1, hyq2⟩ := Set.mem_Ioo.mp hy2
  intro x hx
  obtain ⟨hxp1, hxp2⟩ := Set.mem_Ioo.mp hx
  rw [Set.mem_Ioo]
  constructor <;> linarith

/-- **Greedy selection of a maximal disjoint subfamily, longest first.**

For a finite family `S` of nondegenerate open intervals there is a pairwise disjoint
`T ⊆ S` such that every `p ∈ S` meets some `q ∈ T` with `q.2 - q.1 ≥ p.2 - p.1`. -/
theorem exists_disjoint_maxLen_subfamily (S : Finset (ℝ × ℝ)) (hS : ∀ p ∈ S, p.1 < p.2) :
    ∃ T : Finset (ℝ × ℝ), T ⊆ S ∧
      (∀ p ∈ T, ∀ q ∈ T, p ≠ q → Disjoint (Set.Ioo p.1 p.2) (Set.Ioo q.1 q.2)) ∧
      (∀ p ∈ S, ∃ q ∈ T, ¬ Disjoint (Set.Ioo p.1 p.2) (Set.Ioo q.1 q.2) ∧
        p.2 - p.1 ≤ q.2 - q.1) := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    rcases S.eq_empty_or_nonempty with hS0 | hSne
    · subst hS0
      exact ⟨∅, by simp, by simp, by simp⟩
    · -- a longest interval `p₀` of `S`
      obtain ⟨p₀, hp₀S, hmax⟩ := S.exists_max_image (fun p => p.2 - p.1) hSne
      have hp₀lt : p₀.1 < p₀.2 := hS p₀ hp₀S
      have hp₀nd : ¬ Disjoint (Set.Ioo p₀.1 p₀.2) (Set.Ioo p₀.1 p₀.2) :=
        Set.not_disjoint_iff.mpr ⟨(p₀.1 + p₀.2) / 2,
          ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
      -- the intervals of `S` disjoint from `p₀`
      set B : Finset (ℝ × ℝ) :=
        S.filter (fun q => Disjoint (Set.Ioo q.1 q.2) (Set.Ioo p₀.1 p₀.2)) with hB
      have hBS : B ⊆ S := Finset.filter_subset _ _
      have hp₀B : p₀ ∉ B := by
        intro hmem
        exact hp₀nd (Finset.mem_filter.mp hmem).2
      have hBsub : B ⊂ S :=
        Finset.ssubset_iff_subset_ne.mpr ⟨hBS, fun h => hp₀B (h ▸ hp₀S)⟩
      have hBlt : ∀ p ∈ B, p.1 < p.2 := fun p hp => hS p (hBS hp)
      obtain ⟨T', hT'S, hT'disj, hT'cov⟩ := ih B hBsub hBlt
      refine ⟨insert p₀ T', ?_, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hp₀S
        · exact hBS (hT'S hx)
      · intro p hp q hq hpq
        rcases Finset.mem_insert.mp hp with hpp | hp
        · rcases Finset.mem_insert.mp hq with hqq | hq
          · exact absurd (hpp.trans hqq.symm) hpq
          · rw [hpp]
            exact ((Finset.mem_filter.mp (hT'S hq)).2).symm
        · rcases Finset.mem_insert.mp hq with hqq | hq
          · rw [hqq]
            exact (Finset.mem_filter.mp (hT'S hp)).2
          · exact hT'disj p hp q hq hpq
      · intro p hpS
        by_cases hpB : p ∈ B
        · obtain ⟨q, hqT, hne, hlen⟩ := hT'cov p hpB
          exact ⟨q, Finset.mem_insert_of_mem hqT, hne, hlen⟩
        · refine ⟨p₀, Finset.mem_insert_self _ _, ?_, hmax p hpS⟩
          intro hdisj
          exact hpB (Finset.mem_filter.mpr ⟨hpS, hdisj⟩)

/-- **Extraction of a disjoint subfamily of size at least a third of the covered interval.**

If a finite family `S` of nondegenerate open intervals covers `[a, b]`, then there is a pairwise
disjoint `T ⊆ S` with `b - a ≤ 3 * ∑ p ∈ T, (p.2 - p.1)`. -/
theorem exists_disjoint_three_cover (S : Finset (ℝ × ℝ)) {a b : ℝ} (hab : a ≤ b)
    (hlt : ∀ p ∈ S, p.1 < p.2)
    (hcov : Set.Icc a b ⊆ ⋃ p ∈ S, Set.Ioo p.1 p.2) :
    ∃ T : Finset (ℝ × ℝ), T ⊆ S ∧
      (∀ p ∈ T, ∀ q ∈ T, p ≠ q → Disjoint (Set.Ioo p.1 p.2) (Set.Ioo q.1 q.2)) ∧
      (b - a) ≤ 3 * ∑ p ∈ T, (p.2 - p.1) := by
  classical
  -- the hypothesis `a ≤ b` is in fact not needed for the argument
  have _ := hab
  obtain ⟨T, hTS, hTdisj, hTcov⟩ := exists_disjoint_maxLen_subfamily S hlt
  refine ⟨T, hTS, hTdisj, ?_⟩
  have hTlt : ∀ q ∈ T, q.1 < q.2 := fun q hq => hlt q (hTS hq)
  -- `[a, b]` is covered by the `3`-dilates of the members of `T`
  have hcov3 : Set.Icc a b ⊆
      ⋃ q ∈ T, Set.Ioo (q.1 - (q.2 - q.1)) (q.2 + (q.2 - q.1)) := by
    intro x hx
    obtain ⟨p, hpS, hxp⟩ := Set.mem_iUnion₂.mp (hcov hx)
    obtain ⟨q, hqT, hne, hlen⟩ := hTcov p hpS
    exact Set.mem_iUnion₂.mpr ⟨q, hqT, Ioo_subset_Ioo_triple hlen hne hxp⟩
  have hlenT : ∀ q ∈ T, q.1 - (q.2 - q.1) < q.2 + (q.2 - q.1) := by
    intro q hq
    have := hTlt q hq
    linarith
  have hmain := le_sum_of_Icc_subset_iUnion_Ioo (fun q => q.1 - (q.2 - q.1))
    (fun q => q.2 + (q.2 - q.1)) T hlenT hcov3
  calc b - a ≤ ∑ q ∈ T, ((q.2 + (q.2 - q.1)) - (q.1 - (q.2 - q.1))) := hmain
    _ = 3 * ∑ q ∈ T, (q.2 - q.1) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        ring

end Work.EKLC6Core
