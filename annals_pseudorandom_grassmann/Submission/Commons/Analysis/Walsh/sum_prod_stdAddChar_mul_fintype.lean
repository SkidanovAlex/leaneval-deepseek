import Mathlib
import Submission.Commons.Analysis.Walsh.sum_coord_chi

namespace Commons.Analysis.Walsh

open Finset BigOperators

/-- The standard additive character on `𝔽₂` is self-inverse at every point. -/
private lemma stdAddChar_mul_self (a : ZMod 2) :
    ZMod.stdAddChar a * ZMod.stdAddChar a = 1 := by
  rw [← AddChar.map_add_eq_mul, CharTwo.add_self_eq_zero, AddChar.map_zero_eq_one]

theorem sum_prod_stdAddChar_mul_fintype {ι : Type*} [Fintype ι] [DecidableEq ι] (S T : Finset ι) :
    (∑ x : ι → ZMod 2,
        (∏ i ∈ S, ZMod.stdAddChar (x i)) * (∏ j ∈ T, ZMod.stdAddChar (x j)))
      = if S = T then (2 : ℂ) ^ Fintype.card ι else 0 := by
  classical
  -- Merge the two products into a single coordinatewise product.
  have hstep : ∀ x : ι → ZMod 2,
      (∏ i ∈ S, ZMod.stdAddChar (x i)) * (∏ j ∈ T, ZMod.stdAddChar (x j)) =
        ∏ i : ι, ((if i ∈ S then ZMod.stdAddChar (x i) else 1) *
                  (if i ∈ T then ZMod.stdAddChar (x i) else 1)) := by
    intro x
    rw [← Finset.prod_ite_mem_eq S (fun i => ZMod.stdAddChar (x i)),
        ← Finset.prod_ite_mem_eq T (fun i => ZMod.stdAddChar (x i)),
        ← Finset.prod_mul_distrib]
  rw [Finset.sum_congr rfl (fun x _ => hstep x)]
  rw [sum_prod_pi' (fun i (a : ZMod 2) =>
        (if i ∈ S then ZMod.stdAddChar a else 1) *
        (if i ∈ T then ZMod.stdAddChar a else 1))]
  have hcoord : ∀ i : ι,
      (∑ a : ZMod 2, (if i ∈ S then ZMod.stdAddChar a else 1) *
          (if i ∈ T then ZMod.stdAddChar a else 1))
        = if i ∈ (S \ T) ∪ (T \ S) then 0 else 2 := by
    intro i
    by_cases hS : i ∈ S
    · by_cases hT : i ∈ T
      · have hmem : i ∉ (S \ T) ∪ (T \ S) := by simp [hS, hT]
        rw [if_neg hmem]
        have : (∑ a : ZMod 2, (if i ∈ S then ZMod.stdAddChar a else 1) *
              (if i ∈ T then ZMod.stdAddChar a else 1)) = ∑ _a : ZMod 2, (1 : ℂ) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [if_pos hS, if_pos hT]
          exact stdAddChar_mul_self a
        rw [this, Finset.sum_const, Finset.card_univ, ZMod.card]
        norm_num
      · have hmem : i ∈ (S \ T) ∪ (T \ S) := by simp [hS, hT]
        rw [if_pos hmem]
        have : (∑ a : ZMod 2, (if i ∈ S then ZMod.stdAddChar a else 1) *
              (if i ∈ T then ZMod.stdAddChar a else 1)) = ∑ a : ZMod 2, ZMod.stdAddChar a := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [if_pos hS, if_neg hT, mul_one]
        rw [this, sum_stdAddChar_two]
    · by_cases hT : i ∈ T
      · have hmem : i ∈ (S \ T) ∪ (T \ S) := by simp [hS, hT]
        rw [if_pos hmem]
        have : (∑ a : ZMod 2, (if i ∈ S then ZMod.stdAddChar a else 1) *
              (if i ∈ T then ZMod.stdAddChar a else 1)) = ∑ a : ZMod 2, ZMod.stdAddChar a := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [if_neg hS, if_pos hT, one_mul]
        rw [this, sum_stdAddChar_two]
      · have hmem : i ∉ (S \ T) ∪ (T \ S) := by simp [hS, hT]
        rw [if_neg hmem]
        have : (∑ a : ZMod 2, (if i ∈ S then ZMod.stdAddChar a else 1) *
              (if i ∈ T then ZMod.stdAddChar a else 1)) = ∑ _a : ZMod 2, (1 : ℂ) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [if_neg hS, if_neg hT, one_mul]
        rw [this, Finset.sum_const, Finset.card_univ, ZMod.card]
        norm_num
  rw [Finset.prod_congr rfl (fun i _ => hcoord i),
      prod_ite_mem_zero ((S \ T) ∪ (T \ S)) 2]
  by_cases h : S = T
  · subst h
    have hA : (S \ S) ∪ (S \ S) = (∅ : Finset ι) := by ext i; simp
    rw [hA, if_pos rfl, if_pos rfl]
  · rw [if_neg h]
    have hA : (S \ T) ∪ (T \ S) ≠ ∅ := by
      intro hh
      apply h
      ext i
      constructor
      · intro hi
        by_contra hni
        have : i ∈ (S \ T) ∪ (T \ S) :=
          Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hi, hni⟩))
        rw [hh] at this
        simp at this
      · intro hi
        by_contra hni
        have : i ∈ (S \ T) ∪ (T \ S) :=
          Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hi, hni⟩))
        rw [hh] at this
        simp at this
    rw [if_neg hA]

end Commons.Analysis.Walsh
