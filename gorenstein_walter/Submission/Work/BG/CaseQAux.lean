/-
Generic `Finset` helpers used by the "COMB413" case analysis of
`Submission/Work/BG/C413Defs.lean` (see `Work.BG.comb413`).

Nothing here is specific to the configuration: these are the elementary "supports from
membership" and "column supports from membership" manipulations that the case analysis
(`Work.BG.c4_exists`, `Work.BG.caseQ_false`, `Work.BG.caseP_false`) needs over and over.
-/
import Mathlib
import Submission.Work.BG.C413Defs

namespace Work.BG

set_option linter.unusedSectionVars false

variable {ι J : Type*} [Fintype ι] [Fintype J] [DecidableEq ι] [DecidableEq J]

/-! ## Supports from membership -/

/-- If three distinct rows lie in a column whose size is `0`, `1` or `3`, that column is
exactly the triple. -/
theorem colF_eq_of_three (v : J → ι → ℤ) {i : ι} {x y z : J}
    (h3 : (ColF v i).card ∈ ({0, 1, 3} : Finset ℕ))
    (hx : x ∈ ColF v i) (hy : y ∈ ColF v i) (hz : z ∈ ColF v i)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : ColF v i = {x, y, z} := by
  have hsub : ({x, y, z} : Finset J) ⊆ ColF v i := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl <;> assumption
  have hc3 : ({x, y, z} : Finset J).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hxy, hxz]),
      Finset.card_insert_of_notMem (by simp [hyz]), Finset.card_singleton]
  have hge : 3 ≤ (ColF v i).card := by
    calc (3 : ℕ) = ({x, y, z} : Finset J).card := hc3.symm
      _ ≤ _ := Finset.card_le_card hsub
  have hc := h3
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc
  have hceq : (ColF v i).card = 3 := by omega
  exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm

/-- If four distinct elements lie in a row whose support has exactly four elements, the
support is exactly that quadruple. -/
theorem supp_eq_of_four (v : J → ι → ℤ) {j : J}
    (h1j : (Supp v j).card = 4) {w x y z : ι}
    (hw : w ∈ Supp v j) (hx : x ∈ Supp v j) (hy : y ∈ Supp v j) (hz : z ∈ Supp v j)
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    Supp v j = {w, x, y, z} := by
  have hsub : ({w, x, y, z} : Finset ι) ⊆ Supp v j := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl <;> assumption
  have hc : ({w, x, y, z} : Finset ι).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hwx, hwy, hwz]),
      Finset.card_insert_of_notMem (by simp [hxy, hxz]),
      Finset.card_insert_of_notMem (by simp [hyz]), Finset.card_singleton]
  exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm

/-- Rewriting a membership in a support that has been identified with an explicit set. -/
theorem mem_supp_iff (v : J → ι → ℤ) {j : J} {i : ι} {S : Finset ι} (h : Supp v j = S) :
    v j i ≠ 0 ↔ i ∈ S := by
  rw [← mem_Supp, h]

/-- Rewriting a vanishing entry from a support that has been identified with an explicit set. -/
theorem zero_of_not_mem_supp (v : J → ι → ℤ) {j : J} {i : ι} {S : Finset ι}
    (h : Supp v j = S) (hne : i ∉ S) : v j i = 0 := by
  by_contra hc
  exact hne (by rw [← h, mem_Supp]; exact hc)

/-! ## Extracting the missing element -/

/-- If `x` and `y` are two distinct elements of a column of size three, the column is
`{x, y, g}` for a unique third element `g`. -/
theorem colF_eq_insert_third (v : J → ι → ℤ) {i : ι} {x y : J}
    (hx : x ∈ ColF v i) (hy : y ∈ ColF v i) (hxy : x ≠ y) (hcard : (ColF v i).card = 3) :
    ∃ g : J, ColF v i = {x, y, g} ∧ g ∉ ({x, y} : Finset J) := by
  have hsub : ({x, y} : Finset J) ⊆ ColF v i := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl <;> assumption
  have hc : (ColF v i \ {x, y}).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, hcard, Finset.card_pair hxy]
  obtain ⟨g, hg⟩ := Finset.card_eq_one.mp hc
  refine ⟨g, ?_, ?_⟩
  · rw [← Finset.union_sdiff_of_subset hsub, hg]
    ext t
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  · have hmem : g ∈ ColF v i \ {x, y} := by rw [hg]; simp
    exact (Finset.mem_sdiff.mp hmem).2

/-- A two-element set containing `i` is `{i, j}` for some `j ≠ i`. -/
theorem exists_other_of_card_two {S : Finset ι} {i : ι} (hi : i ∈ S) (hcard : S.card = 2) :
    ∃ j, j ≠ i ∧ S = {i, j} := by
  have hsub : ({i} : Finset ι) ⊆ S := by simpa using hi
  have hc : (S \ {i}).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, hcard, Finset.card_singleton]
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hc
  have hmem : j ∈ S \ {i} := by rw [hj]; simp
  have hjS : j ∈ S := (Finset.mem_sdiff.mp hmem).1
  have hji : j ≠ i := fun h => (Finset.mem_sdiff.mp hmem).2 (by simpa [h])
  refine ⟨j, hji, ?_⟩
  ext t
  constructor
  · intro ht
    by_cases hti : t = i
    · subst hti; simp
    · have h' : t ∈ S \ {i} := Finset.mem_sdiff.mpr ⟨ht, by simpa using hti⟩
      rw [hj] at h'
      simp only [Finset.mem_singleton] at h'
      subst h'
      simp
  · intro ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact hi
    · exact hjS

/-- Two distinct elements of a set of size two. -/
theorem mem_of_card_two_of_not {S : Finset ι} {i i' : ι} (h : S = {i, i'}) (hne : i ≠ i') :
    i ∈ S ∧ i' ∈ S ∧ S.card = 2 := by
  subst h
  exact ⟨by simp, by simp, Finset.card_pair hne⟩

end Work.BG
