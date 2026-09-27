import Mathlib
import Submission.Work.Cohomology.EZShuffleGen

namespace Work.Cohomology.EZG

/-!
# The shuffle sign after deleting the *last* position

For a shuffle `A ⊆ Fin (n+1)`, `delPosP A (Fin.last n) ⊆ Fin n` is the shuffle obtained by
deleting the last position.  Note that `Fin.succAbove (Fin.last n) = Fin.castSucc`, so
`delPosP A (Fin.last n)` is simply `A` with the (possible) last element removed and the result
re-indexed along `Fin.castSucc`.

This file computes how the shuffle sign `sgnA` changes when the last position is deleted, which
is one of the steps in the boundary computation of the Eilenberg–Zilber shuffle chain.

The crucial input is that the number of inversions contributed by an element `i ∈ A` with
`i ≠ Fin.last n` is unchanged by the deletion (`sgnAL_cntB_last_eq`), while the element
`Fin.last n` (when present) contributes exactly `n+1 - A.card` inversions
(`sgnAL_cntB_last_of_mem`).
-/

/-- `A.filter (· ≠ Fin.last n)` is the image of the deleted shuffle `delPosP A (Fin.last n)`
under `Fin.castSucc`. -/
lemma sgnAL_filter_ne_last_eq_image {n : ℕ} (A : Finset (Fin (n+1))) :
    A.filter (fun i => i ≠ Fin.last n)
      = (delPosP A (Fin.last n)).image Fin.castSucc := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨hiA, hi⟩
    exact ⟨i.castPred hi, by
      rw [mem_delPosP, Fin.succAbove_last_apply, Fin.castSucc_castPred i hi]
      exact hiA, Fin.castSucc_castPred i hi⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨by rwa [mem_delPosP, Fin.succAbove_last_apply] at ht, Fin.castSucc_ne_last t⟩

/-- Deleting the last position does not change the number of complement elements below an
element `t : Fin n` of the shuffle. -/
lemma sgnAL_cntB_last_eq {n : ℕ} (A : Finset (Fin (n+1))) (t : Fin n) :
    cntB A t.val = cntB (delPosP A (Fin.last n)) t.val := by
  unfold cntB
  have hset : ((Finset.univ : Finset (Fin (n+1))) \ A).filter (fun i => i.val < t.val)
      = (((Finset.univ : Finset (Fin n)) \ delPosP A (Fin.last n)).filter
          (fun i => i.val < t.val)).image Fin.castSucc := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨hjA, hjt⟩
      have hjn : j.val < n := lt_trans hjt t.isLt
      have hne : j ≠ Fin.last n := fun h => by
        rw [h, Fin.val_last] at hjn; exact Nat.lt_irrefl n hjn
      refine ⟨j.castPred hne, ⟨?_, by rw [Fin.coe_castPred]; exact hjt⟩,
        Fin.castSucc_castPred j hne⟩
      intro hcon
      exact hjA (by
        have h1 := mem_delPosP.mp hcon
        rwa [Fin.succAbove_last_apply, Fin.castSucc_castPred j hne] at h1)
    · rintro ⟨a, ⟨haB, hat⟩, rfl⟩
      refine ⟨?_, by simpa using hat⟩
      intro hcon
      exact haB (mem_delPosP.mpr (by rw [Fin.succAbove_last_apply]; exact hcon))
  rw [hset, Finset.card_image_of_injective _ (Fin.castSucc_injective n)]

/-- The last element of `A` (when it belongs to `A`) contributes exactly `n+1 - A.card`
inversions. -/
lemma sgnAL_cntB_last_of_mem {n : ℕ} (A : Finset (Fin (n+1))) (h : Fin.last n ∈ A) :
    cntB A (Fin.last n).val = n + 1 - A.card := by
  have hge : 1 ≤ A.card := Finset.one_le_card.mpr ⟨_, h⟩
  have hsum := cnt_add_cntB A (m := n) (Nat.le_succ n)
  have hcnt : cnt A n = A.card - 1 := by
    rw [cnt]
    have hfl : A.filter (fun i => i.val < n) = A.erase (Fin.last n) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hiA, hi⟩
        refine ⟨?_, hiA⟩
        intro hcon
        rw [hcon, Fin.val_last] at hi
        exact Nat.lt_irrefl n hi
      · rintro ⟨hne, hiA⟩
        refine ⟨hiA, ?_⟩
        have h1 : i.val ≤ n := Nat.le_of_lt_succ i.isLt
        have h2 : i.val ≠ n := fun hh => hne (Fin.ext (by rw [Fin.val_last]; exact hh))
        omega
    rw [hfl, Finset.card_erase_of_mem h]
  rw [Fin.val_last]
  omega

/-- A parity helper: `(-1)^(a + 2c) = (-1)^a`. -/
lemma sgnAL_neg_one_pow_eq_of_eq_add_mul_two {a b c : ℕ} (h : b = a + 2*c) :
    (-1 : ℤ)^b = (-1)^a := by
  subst h
  rw [pow_add, pow_mul]
  norm_num

/-- Deleting the last position of a shuffle changes its inversion number by `n+1 - A.card`
exactly when the last position belongs to `A`. -/
lemma sgnAL_invA_last {n : ℕ} (A : Finset (Fin (n+1))) :
    invA A = invA (delPosP A (Fin.last n)) + (if Fin.last n ∈ A then (n+1 - A.card) else 0) := by
  have hdef : invA A = A.sum (fun i => cntB A i.val) := rfl
  have hdefB : invA (delPosP A (Fin.last n)) =
      (delPosP A (Fin.last n)).sum (fun t => cntB (delPosP A (Fin.last n)) t.val) := rfl
  rw [hdef, hdefB]
  have hsplit : A.sum (fun i => cntB A i.val) =
      (A.filter (fun i => i ≠ Fin.last n)).sum (fun i => cntB A i.val)
      + (if Fin.last n ∈ A then cntB A (Fin.last n).val else 0) := by
    rw [← Finset.sum_filter_add_sum_filter_not A (fun i => i ≠ Fin.last n)
      (fun i => cntB A i.val)]
    congr 1
    have hf : A.filter (fun i => ¬ i ≠ Fin.last n) = A.filter (fun i => i = Fin.last n) :=
      Finset.filter_congr (fun i _ => not_ne_iff)
    rw [hf]
    by_cases h : Fin.last n ∈ A
    · rw [if_pos h]
      have hsingle : A.filter (fun i => i = Fin.last n) = {Fin.last n} := by
        ext i; simp only [Finset.mem_filter, Finset.mem_singleton]
        exact ⟨fun ⟨_, h2⟩ => h2, fun h2 => ⟨h2 ▸ h, h2⟩⟩
      rw [hsingle, Finset.sum_singleton]
    · rw [if_neg h]
      have hemp : A.filter (fun i => i = Fin.last n) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro i hi hi'
        exact h (hi' ▸ hi)
      rw [hemp, Finset.sum_empty]
  rw [hsplit]
  congr 1
  · rw [sgnAL_filter_ne_last_eq_image A]
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro t ht
      rw [Fin.val_castSucc]
      exact sgnAL_cntB_last_eq A t
    · intro a _ b _ hh
      exact Fin.castSucc_injective n hh
  · by_cases h : Fin.last n ∈ A
    · rw [if_pos h, if_pos h, sgnAL_cntB_last_of_mem A h]
    · rw [if_neg h, if_neg h]

theorem sgnA_delPos_last {n : ℕ} (A : Finset (Fin (n + 1))) :
    sgnA A * (-1 : ℤ) ^ (n + 1) = sgnA (delPosP A (Fin.last n)) *
      (if Fin.last n ∈ A then (-1 : ℤ) ^ A.card
        else (-1 : ℤ) ^ A.card * (-1 : ℤ) ^ (n + 1 - A.card)) := by
  have hcard : A.card ≤ n + 1 := by simpa using Finset.card_le_univ A
  have hrec := sgnAL_invA_last A
  have hsgn : sgnA A = sgnA (delPosP A (Fin.last n)) *
      (-1 : ℤ) ^ (if Fin.last n ∈ A then (n+1 - A.card) else 0) := by
    rw [sgnA, sgnA, hrec, pow_add]
  have key : (-1 : ℤ) ^ (if Fin.last n ∈ A then (n+1 - A.card) else 0) * (-1)^(n+1) =
      (if Fin.last n ∈ A then (-1 : ℤ)^A.card
        else (-1 : ℤ)^A.card * (-1)^(n+1-A.card)) := by
    by_cases h : Fin.last n ∈ A
    · rw [if_pos h, if_pos h, ← pow_add]
      apply sgnAL_neg_one_pow_eq_of_eq_add_mul_two (c := n + 1 - A.card)
      omega
    · rw [if_neg h, if_neg h, pow_zero, one_mul, ← pow_add,
        show A.card + (n + 1 - A.card) = n + 1 by omega]
  rw [hsgn, mul_assoc, key]

end Work.Cohomology.EZG
