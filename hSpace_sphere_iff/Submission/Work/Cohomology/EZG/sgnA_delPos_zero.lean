import Mathlib
import Submission.Work.Cohomology.EZShuffleGen

open Finset

namespace Work.Cohomology.EZG

/-!
# The shuffle sign after deleting the position `0`

`sgnA A = (-1) ^ (invA A)` is the sign of the `(p,q)`-shuffle `A ⊆ Fin (p+q)`, where `invA A`
counts the inversions of `A`, i.e. the pairs `i ∈ A`, `j ∉ A` with `j < i`.

This file computes the sign of `A` in terms of the sign of `delPosP A 0`, the shuffle obtained by
deleting the *smallest* position.  Writing `B = delPosP A 0 = {t : Fin n | t.succ ∈ A}`, the two
shuffles agree after shifting `B` up by one:

* if `0 ∈ A`, then `A = insert 0 (B.image Fin.succ)` and `invA A = invA B`;
* if `0 ∉ A`, then `A = B.image Fin.succ` and `invA A = invA B + A.card`.

Both statements follow from a single per-element count, `lowA_succ_eq`: for every `t : Fin n`, the
number of non-elements of `A` below `t.succ` is the number of non-elements of `B` below `t`, plus
`1` exactly when `0 ∉ A`.
-/

/-- `lowA A i` is the number of non-elements of `A` that are strictly below `i`. -/
def lowA {n : ℕ} (A : Finset (Fin n)) (i : Fin n) : ℕ :=
  ((Finset.univ \ A).filter (fun j : Fin n => j.val < i.val)).card

/-- `invA` is the sum of `lowA` over the elements of `A`. -/
lemma invA_eq_sum_lowA {n : ℕ} (A : Finset (Fin n)) : invA A = A.sum (lowA A) := rfl

/-- Membership in `delPosP A 0`, spelled out via the successor embedding. -/
lemma mem_delPosP_zero {n : ℕ} {A : Finset (Fin (n+1))} {t : Fin n} :
    t ∈ delPosP A 0 ↔ t.succ ∈ A := by
  rw [mem_delPosP, Fin.succAbove_of_le_castSucc 0 t (by simp)]

/-- The key per-element count: the non-elements of `A` below `t.succ` are the non-elements of
`delPosP A 0` below `t` (shifted up by one), together with `0` when `0 ∉ A`. -/
lemma lowA_succ_eq {n : ℕ} (A : Finset (Fin (n+1))) (t : Fin n) :
    lowA A t.succ = lowA (delPosP A 0) t + (if (0 : Fin (n+1)) ∈ A then 0 else 1) := by
  have hcard : ((Finset.univ \ A).filter (fun j : Fin (n+1) => j.val < t.succ.val)).card
      = ((Finset.univ \ delPosP A 0).filter (fun s : Fin n => s.val < t.val)).card
        + (if (0 : Fin (n+1)) ∈ A then 0 else 1) := by
    set S1 := (Finset.univ \ A).filter (fun j : Fin (n+1) => j.val < t.succ.val) with hS1
    set S2 := (Finset.univ \ delPosP A 0).filter (fun s : Fin n => s.val < t.val) with hS2
    have hmemS1 : ∀ j : Fin (n+1), j ∈ S1 ↔ j ∉ A ∧ j.val < t.succ.val := by
      intro j; rw [hS1]
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
    have hmemS2 : ∀ s : Fin n, s ∈ S2 ↔ s ∉ delPosP A 0 ∧ s.val < t.val := by
      intro s; rw [hS2]
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
    have hcard' : (S1.erase 0).card = S2.card := by
      refine (Finset.card_bij (fun (s : Fin n) (_ : s ∈ S2) => s.succ) ?_ ?_ ?_).symm
      · intro s hs
        rw [Finset.mem_erase, hmemS1]
        rw [hmemS2] at hs
        rw [mem_delPosP_zero] at hs
        exact ⟨Fin.succ_ne_zero s, hs.1, by simp only [Fin.val_succ]; omega⟩
      · intro s1 _ s2 _ h
        exact Fin.succ_inj.mp h
      · intro j hj
        rw [Finset.mem_erase, hmemS1] at hj
        obtain ⟨hj0, hjA, hjlt⟩ := hj
        obtain ⟨s, hs⟩ := Fin.eq_succ_of_ne_zero hj0
        refine ⟨s, ?_, hs.symm⟩
        rw [hmemS2, mem_delPosP_zero]
        refine ⟨hs ▸ hjA, ?_⟩
        rw [hs] at hjlt
        simp only [Fin.val_succ] at hjlt
        omega
    have hsplit : S1.card = (S1.erase 0).card + (if (0 : Fin (n+1)) ∈ S1 then 1 else 0) := by
      by_cases h : (0 : Fin (n+1)) ∈ S1
      · rw [if_pos h]; exact (Finset.card_erase_add_one h).symm
      · rw [if_neg h, Finset.erase_eq_self.mpr h, add_zero]
    have h0 : ((0 : Fin (n+1)) ∈ S1) ↔ ((0 : Fin (n+1)) ∉ A) := by
      rw [hmemS1]
      exact ⟨fun h => h.1, fun h => ⟨h, by simp⟩⟩
    have hite : (if (0 : Fin (n+1)) ∈ S1 then 1 else 0)
        = (if (0 : Fin (n+1)) ∈ A then 0 else 1) := by
      by_cases h : (0 : Fin (n+1)) ∈ A
      · rw [if_pos h, if_neg (fun hh => (h0.mp hh) h)]
      · rw [if_neg h, if_pos (h0.mpr h)]
    rw [hsplit, hite, hcard']
  simpa only [lowA] using hcard

/-- The elements of `A` above `0`, shifted down, lie in `delPosP A 0`. -/
lemma image_succ_delPosP_zero_subset {n : ℕ} (A : Finset (Fin (n+1))) :
    (delPosP A 0).image Fin.succ ⊆ A := by
  intro j hj
  rw [Finset.mem_image] at hj
  obtain ⟨s, hs, rfl⟩ := hj
  exact mem_delPosP_zero.mp hs

/-- Every element of `A` is either `0` or the successor of an element of `delPosP A 0`. -/
lemma subset_insert_zero_image_succ {n : ℕ} (A : Finset (Fin (n+1))) :
    A ⊆ insert 0 ((delPosP A 0).image Fin.succ) := by
  intro j hj
  by_cases h : j = 0
  · rw [h]; exact Finset.mem_insert_self _ _
  · obtain ⟨s, hs⟩ := Fin.eq_succ_of_ne_zero h
    rw [Finset.mem_insert]
    exact Or.inr (Finset.mem_image.mpr ⟨s, mem_delPosP_zero.mpr (hs ▸ hj), hs.symm⟩)

/-- If `0 ∈ A` then `A` is `0` together with the shifted `delPosP A 0`. -/
lemma eq_insert_of_mem_zero {n : ℕ} {A : Finset (Fin (n+1))} (h0 : (0 : Fin (n+1)) ∈ A) :
    A = insert 0 ((delPosP A 0).image Fin.succ) :=
  Finset.Subset.antisymm (subset_insert_zero_image_succ A) (by
    intro j hj
    rw [Finset.mem_insert] at hj
    rcases hj with rfl | hj
    · exact h0
    · exact image_succ_delPosP_zero_subset A hj)

/-- If `0 ∉ A` then `A` is exactly the shifted `delPosP A 0`. -/
lemma eq_image_of_notMem_zero {n : ℕ} {A : Finset (Fin (n+1))} (h0 : (0 : Fin (n+1)) ∉ A) :
    A = (delPosP A 0).image Fin.succ :=
  Finset.Subset.antisymm (by
    intro j hj
    have hj0 : j ≠ 0 := fun h => h0 (h ▸ hj)
    obtain ⟨s, hs⟩ := Fin.eq_succ_of_ne_zero hj0
    exact Finset.mem_image.mpr ⟨s, mem_delPosP_zero.mpr (hs ▸ hj), hs.symm⟩)
    (image_succ_delPosP_zero_subset A)

/-- `0` is not the successor of anything. -/
lemma zero_notMem_image_succ {n : ℕ} (A : Finset (Fin (n+1))) :
    (0 : Fin (n+1)) ∉ (delPosP A 0).image Fin.succ := by
  intro h
  rw [Finset.mem_image] at h
  obtain ⟨s, _, hs⟩ := h
  exact Fin.succ_ne_zero s hs

/-- Deleting the position `0` changes the inversion count by `0` or `A.card`. -/
lemma invA_delPosP_zero {n : ℕ} (A : Finset (Fin (n+1))) :
    invA A = invA (delPosP A 0) + (if (0 : Fin (n+1)) ∈ A then 0 else A.card) := by
  have hz0 : lowA A (0 : Fin (n+1)) = 0 := by simp [lowA]
  have hsuc : ∀ (S : Finset (Fin n)),
      (S.image Fin.succ).sum (lowA A) = S.sum (fun t => lowA A t.succ) :=
    fun S => Finset.sum_image (fun x _ y _ h => Fin.succ_inj.mp h)
  have hmain : A.sum (lowA A) = (delPosP A 0).sum (lowA (delPosP A 0))
      + (if (0 : Fin (n+1)) ∈ A then 0 else A.card) := by
    by_cases h0 : (0 : Fin (n+1)) ∈ A
    · rw [if_pos h0, add_zero]
      calc A.sum (lowA A)
          = (insert 0 ((delPosP A 0).image Fin.succ)).sum (lowA A) :=
              Finset.sum_congr (eq_insert_of_mem_zero h0) (fun x _ => rfl)
        _ = lowA A 0 + ((delPosP A 0).image Fin.succ).sum (lowA A) :=
              Finset.sum_insert (zero_notMem_image_succ A)
        _ = ((delPosP A 0).image Fin.succ).sum (lowA A) := by rw [hz0, zero_add]
        _ = (delPosP A 0).sum (fun t => lowA A t.succ) := hsuc (delPosP A 0)
        _ = (delPosP A 0).sum (lowA (delPosP A 0)) :=
              Finset.sum_congr rfl (fun t _ => by rw [lowA_succ_eq, if_pos h0, add_zero])
    · rw [if_neg h0]
      have hcard : (delPosP A 0).card = A.card := by
        rw [congrArg Finset.card (eq_image_of_notMem_zero h0)]
        exact (Finset.card_image_of_injective (delPosP A 0) (f := Fin.succ)
          (fun x y h => Fin.succ_inj.mp h)).symm
      calc A.sum (lowA A)
          = ((delPosP A 0).image Fin.succ).sum (lowA A) :=
              Finset.sum_congr (eq_image_of_notMem_zero h0) (fun x _ => rfl)
        _ = (delPosP A 0).sum (fun t => lowA A t.succ) := hsuc (delPosP A 0)
        _ = (delPosP A 0).sum (fun t => lowA (delPosP A 0) t + 1) :=
              Finset.sum_congr rfl (fun t _ => by rw [lowA_succ_eq, if_neg h0])
        _ = (delPosP A 0).sum (lowA (delPosP A 0)) + (delPosP A 0).sum (fun _ => 1) :=
              Finset.sum_add_distrib
        _ = (delPosP A 0).sum (lowA (delPosP A 0)) + A.card := by
              rw [Finset.sum_const, hcard]
              simp
  rw [invA_eq_sum_lowA A, invA_eq_sum_lowA (delPosP A 0)]
  exact hmain

/-- The sign of a shuffle with the smallest position deleted. -/
theorem sgnA_delPos_zero {n : ℕ} (A : Finset (Fin (n + 1))) :
    sgnA A = sgnA (delPosP A 0) *
      (if (0 : Fin (n + 1)) ∈ A then 1 else (-1 : ℤ) ^ A.card) := by
  simp only [sgnA]
  rw [invA_delPosP_zero A]
  by_cases h0 : (0 : Fin (n + 1)) ∈ A
  · rw [if_pos h0, add_zero, if_pos h0, mul_one]
  · rw [if_neg h0, pow_add, if_neg h0]

end Work.Cohomology.EZG
