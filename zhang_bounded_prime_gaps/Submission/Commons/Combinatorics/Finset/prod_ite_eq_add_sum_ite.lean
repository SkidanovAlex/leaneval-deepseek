import Mathlib.Algebra.BigOperators.Ring.Finset
import Submission.Commons.Combinatorics.Embedding.sum_preimage_expOf_smul

namespace Commons.Combinatorics.Finset

/-- For a function `x : ι → α` on a finite type and a distinguished value `o`, the "at most one
coordinate differs from `o`" indicator decomposes as the all-equal term plus the single-deviation
terms. -/
theorem prod_ite_eq_add_sum_ite {ι α R : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    [CommRing R] (x : ι → α) (o : α) :
    (∏ j, (if x j = o then (1 : R) else 0))
      + ∑ i, (if x i = o then (0 : R) else 1) *
          (∏ j ∈ Finset.univ.erase i, (if x j = o then (1 : R) else 0))
      = if (Finset.univ.filter (fun j => x j ≠ o)).card ≤ 1 then (1 : R) else 0 := by
  classical
  set D : Finset ι := Finset.univ.filter (fun j => x j ≠ o) with hD
  have memD : ∀ j, j ∈ D ↔ x j ≠ o := by
    intro j
    rw [hD]
    simp
  have hterm1 : (∏ j, (if x j = o then (1 : R) else 0)) = if D.card = 0 then (1 : R) else 0 := by
    rw [Fintype.prod_boole (p := fun j => x j = o)]
    have hiff : (∀ j, x j = o) ↔ D.card = 0 := by
      rw [Finset.card_eq_zero, hD, Finset.filter_eq_empty_iff]
      simp
    by_cases h : D.card = 0
    · rw [if_pos h, if_pos (hiff.mpr h)]
    · rw [if_neg h, if_neg (fun hc => h (hiff.mp hc))]
  have hsummand : ∀ i, (if x i = o then (0 : R) else 1) *
        (∏ j ∈ Finset.univ.erase i, (if x j = o then (1 : R) else 0))
        = if D = {i} then (1 : R) else 0 := by
    intro i
    by_cases hi : x i = o
    · have hne : D ≠ {i} := by
        intro h
        have hmem : i ∈ D := by rw [h]; exact Finset.mem_singleton_self i
        exact (memD i).mp hmem hi
      rw [if_neg hne, if_pos hi]
      simp
    · have hiff : (∀ j ∈ Finset.univ.erase i, x j = o) ↔ D = {i} := by
        rw [Finset.eq_singleton_iff_unique_mem]
        constructor
        · intro h
          refine ⟨(memD i).mpr hi, fun b hb => ?_⟩
          by_contra hbi
          have hbj : b ∈ Finset.univ.erase i := by
            rw [Finset.mem_erase]
            exact ⟨hbi, Finset.mem_univ b⟩
          exact (memD b).mp hb (h b hbj)
        · rintro ⟨_, huniq⟩ j hj
          rw [Finset.mem_erase] at hj
          obtain ⟨hji, _⟩ := hj
          by_contra hxj
          have hxj' : x j ≠ o := hxj
          have hjD : j ∈ D := (memD j).mpr hxj'
          exact hji (huniq j hjD)
      rw [Finset.prod_boole (p := fun j => x j = o) (s := Finset.univ.erase i)]
      rw [if_neg hi]
      simp only [one_mul]
      by_cases hc : D = {i}
      · rw [if_pos hc, if_pos (hiff.mpr hc)]
      · rw [if_neg hc, if_neg (fun hq => hc (hiff.mp hq))]
  have hterm2 : (∑ i, (if x i = o then (0 : R) else 1) *
        (∏ j ∈ Finset.univ.erase i, (if x j = o then (1 : R) else 0)))
        = if D.card = 1 then (1 : R) else 0 := by
    simp_rw [hsummand]
    rw [Finset.sum_boole (fun i => D = {i}) Finset.univ]
    by_cases h : D.card = 1
    · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
      have hF : Finset.univ.filter (fun i => D = {i}) = {a} := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro hi
          have h2 : ({i} : Finset ι) = {a} := by rw [← hi, ha]
          exact Finset.singleton_inj.mp h2
        · intro hi
          rw [hi]
          exact ha
      rw [hF, Finset.card_singleton, h]
      simp
    · have hF : Finset.univ.filter (fun i => D = {i}) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro i _ hDi
        exact h (by rw [hDi]; exact Finset.card_singleton i)
      rw [hF, Finset.card_empty, if_neg h]
      simp
  rw [hterm1, hterm2]
  have key : (if D.card = 0 then (1 : R) else 0) + (if D.card = 1 then (1 : R) else 0)
      = if D.card ≤ 1 then (1 : R) else 0 := by
    by_cases h0 : D.card = 0
    · rw [if_pos h0, if_neg (by omega : ¬ D.card = 1), if_pos (by omega : D.card ≤ 1)]
      simp
    · by_cases h1 : D.card = 1
      · rw [if_neg h0, if_pos h1, if_pos (by omega : D.card ≤ 1)]
        simp
      · rw [if_neg h0, if_neg h1, if_neg (by omega : ¬ D.card ≤ 1)]
        simp
  exact key

end Commons.Combinatorics.Finset