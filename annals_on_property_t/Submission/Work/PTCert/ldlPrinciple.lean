import Mathlib
import Submission.Work.PTCert.Interfaces

/-! Guidance from the project lead (the requester): ... -/

open scoped BigOperators Matrix

namespace Work.PTCert

open Submission.PTCert

/-- `|x * y| ≤ (x² + y²)/2`. -/
lemma abs_mul_le_half (x y : ℝ) : |x * y| ≤ (x ^ 2 + y ^ 2) / 2 := by
  have h : (2 : ℝ) * (|x| * |y|) ≤ x ^ 2 + y ^ 2 := by
    have hh := sq_nonneg (|x| - |y|)
    rw [sub_sq, sq_abs, sq_abs] at hh
    linarith
  rw [abs_mul]
  linarith

/-- Swapping the two indices in a sum over off-diagonal pairs. -/
lemma sum_erase_comm' {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (S : Finset α) (F : α → α → M) :
    (∑ i ∈ S, ∑ j ∈ S.erase i, F i j) = ∑ j ∈ S, ∑ i ∈ S.erase j, F i j := by
  have step : ∀ i, (∑ j ∈ S.erase i, F i j) = ∑ j ∈ S, if j ≠ i then F i j else 0 := by
    intro i
    rw [← Finset.filter_ne' S i, Finset.sum_filter]
  calc ∑ i ∈ S, ∑ j ∈ S.erase i, F i j
      = ∑ i ∈ S, ∑ j ∈ S, (if j ≠ i then F i j else 0) := Finset.sum_congr rfl fun i _ => step i
    _ = ∑ j ∈ S, ∑ i ∈ S, (if j ≠ i then F i j else 0) := Finset.sum_comm
    _ = ∑ j ∈ S, ∑ i ∈ S.erase j, F i j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [show (∑ i ∈ S, (if j ≠ i then F i j else 0))
              = ∑ i ∈ S, (if i ≠ j then F i j else 0) from
          Finset.sum_congr rfl fun i _ => by
            by_cases h : j = i
            · simp [h]
            · simp [h, Ne.symm h]]
        rw [← Finset.filter_ne' S j, Finset.sum_filter]

/-- A symmetric real matrix which is diagonally dominant with nonnegative diagonal is
positive semidefinite. -/
lemma posSemidef_of_diag_dominant {n : ℕ} (R : Matrix (Fin n) (Fin n) ℝ)
    (hsym : R.transpose = R)
    (hdom : ∀ i, ∑ j ∈ Finset.univ.erase i, |R i j| ≤ R i i) :
    R.PosSemidef := by
  classical
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hsym
  · intro x
    have hR : ∀ i j, R i j = R j i := by
      intro i j
      have h := congrFun (congrFun hsym i) j
      rw [Matrix.transpose_apply] at h
      exact h.symm
    have hdot : star x ⬝ᵥ (R *ᵥ x) = ∑ i, ∑ j, x i * R i j * x j := by
      simp [dotProduct, Matrix.mulVec, star_trivial, Finset.mul_sum, mul_assoc]
    rw [hdot]
    have hsplit1 : (∑ i, ∑ j, x i * R i j * x j)
        = (∑ i, x i * R i i * x i)
          + ∑ i, ∑ j ∈ Finset.univ.erase i, x i * R i j * x j := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      exact (Finset.sum_erase_add Finset.univ (fun j => x i * R i j * x j)
              (Finset.mem_univ i)).symm.trans (add_comm _ _)
    have hA : (∑ i, x i * R i i * x i)
        = (∑ i, (R i i - ∑ j ∈ Finset.univ.erase i, |R i j|) * (x i) ^ 2)
          + ∑ i, (∑ j ∈ Finset.univ.erase i, |R i j|) * (x i) ^ 2 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    have hB : (∑ i, (∑ j ∈ Finset.univ.erase i, |R i j|) * (x i) ^ 2)
        = ∑ i, ∑ j ∈ Finset.univ.erase i, |R i j| * ((x i) ^ 2 + (x j) ^ 2) / 2 := by
      have key : ∀ i, (∑ j ∈ Finset.univ.erase i, |R i j| * ((x i) ^ 2 + (x j) ^ 2) / 2)
          = (∑ j ∈ Finset.univ.erase i, |R i j|) * (x i) ^ 2 / 2
            + ∑ j ∈ Finset.univ.erase i, |R i j| * (x j) ^ 2 / 2 := by
        intro i
        have h1 : (∑ j ∈ Finset.univ.erase i, |R i j| * ((x i) ^ 2 + (x j) ^ 2) / 2)
            = ∑ j ∈ Finset.univ.erase i,
                (|R i j| * (x i) ^ 2 / 2 + |R i j| * (x j) ^ 2 / 2) :=
          Finset.sum_congr rfl (fun j _ => by ring)
        rw [h1, Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul]
      have h2 : (∑ i, ∑ j ∈ Finset.univ.erase i, |R i j| * ((x i) ^ 2 + (x j) ^ 2) / 2)
          = (∑ i, (∑ j ∈ Finset.univ.erase i, |R i j|) * (x i) ^ 2 / 2)
            + ∑ i, ∑ j ∈ Finset.univ.erase i, |R i j| * (x j) ^ 2 / 2 := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun i _ => key i)
      have h3 : (∑ i, ∑ j ∈ Finset.univ.erase i, |R i j| * (x j) ^ 2 / 2)
          = ∑ i, (∑ j ∈ Finset.univ.erase i, |R i j|) * (x i) ^ 2 / 2 := by
        rw [sum_erase_comm' (Finset.univ) (fun i j => |R i j| * (x j) ^ 2 / 2)]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [← Finset.sum_div, ← Finset.sum_mul]
        refine congrArg (fun t => t * (x j) ^ 2 / 2) ?_
        exact Finset.sum_congr rfl (fun i _ => congrArg abs (hR i j))
      calc (∑ i, (∑ j ∈ Finset.univ.erase i, |R i j|) * (x i) ^ 2)
          = (∑ i, (∑ j ∈ Finset.univ.erase i, |R i j|) * (x i) ^ 2 / 2)
            + (∑ i, (∑ j ∈ Finset.univ.erase i, |R i j|) * (x i) ^ 2 / 2) := by
              rw [← Finset.sum_add_distrib]
              exact Finset.sum_congr rfl (fun i _ => by ring)
        _ = (∑ i, (∑ j ∈ Finset.univ.erase i, |R i j|) * (x i) ^ 2 / 2)
            + (∑ i, ∑ j ∈ Finset.univ.erase i, |R i j| * (x j) ^ 2 / 2) := by rw [← h3]
        _ = ∑ i, ∑ j ∈ Finset.univ.erase i, |R i j| * ((x i) ^ 2 + (x j) ^ 2) / 2 := h2.symm
    have hC : (∑ i, ∑ j ∈ Finset.univ.erase i, |R i j| * ((x i) ^ 2 + (x j) ^ 2) / 2)
        + (∑ i, ∑ j ∈ Finset.univ.erase i, x i * R i j * x j)
        = ∑ i, ∑ j ∈ Finset.univ.erase i,
            (x i * R i j * x j + |R i j| * ((x i) ^ 2 + (x j) ^ 2) / 2) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    have hmain : (∑ i, ∑ j, x i * R i j * x j)
        = (∑ i, (R i i - ∑ j ∈ Finset.univ.erase i, |R i j|) * (x i) ^ 2)
          + ∑ i, ∑ j ∈ Finset.univ.erase i,
              (x i * R i j * x j + |R i j| * ((x i) ^ 2 + (x j) ^ 2) / 2) := by
      rw [hsplit1, hA, hB, add_assoc, hC]
    rw [hmain]
    have hA' : 0 ≤ ∑ i, (R i i - ∑ j ∈ Finset.univ.erase i, |R i j|) * (x i) ^ 2 :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (sub_nonneg.mpr (hdom i)) (sq_nonneg _))
    have hB' : 0 ≤ ∑ i, ∑ j ∈ Finset.univ.erase i,
        (x i * R i j * x j + |R i j| * ((x i) ^ 2 + (x j) ^ 2) / 2) :=
      Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => ?_))
    · linarith
    · have h1 : |x i * x j| ≤ ((x i) ^ 2 + (x j) ^ 2) / 2 := abs_mul_le_half (x i) (x j)
      have h2 : |R i j| * |x i * x j| ≤ |R i j| * (((x i) ^ 2 + (x j) ^ 2) / 2) :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      have h3 : |R i j * (x i * x j)| = |R i j| * |x i * x j| := abs_mul _ _
      have h4 : -(R i j * (x i * x j)) ≤ |R i j| * |x i * x j| := by
        rw [← h3]; exact neg_le_abs _
      have h5 : R i j * (x i * x j) = x i * R i j * x j := by ring
      linarith [h2, h4, h5]

theorem ldlPrinciple : LdlPrinciple := by
  intro n W L R d hd hsym hdom hW
  rw [hW]
  refine Matrix.PosSemidef.add ?_ ?_
  · have hdiag : (Matrix.diagonal d).PosSemidef := Matrix.PosSemidef.diagonal (fun i => hd i)
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hdiag.mul_mul_conjTranspose_same L
  · exact posSemidef_of_diag_dominant R hsym hdom

end Work.PTCert
