import Mathlib
import Submission.Work.TMC14Core.SmTraceAux

/-!
# TMC14Core: the determinant of the shooting matrix

`det (smMat (q+1) d t) = tr (transProd d (q+1)) - (t + t⁻¹)`.

Multiplying `smMat` on the right by the change-of-basis matrix `TMat` (defined in
`SmTraceAux`, where `det TMat = 1`) turns it into a matrix whose rows of index `≥ 2` are
standard basis vectors; hence its determinant is that of the top left `2 × 2` block, whose
entries are computed with the transfer matrices.  Unimodularity of `transProd` finishes the
computation.
-/

open LeanEval.Analysis.TenMartini


noncomputable section
namespace Work.TMC14Core

namespace SmTrace
open Matrix

/-! ### Rows of `smMat` as functionals -/

lemma mul_apply_eq_mulVec (n : ℕ) (M B : Matrix (Fin (n+2)) (Fin (n+2)) ℂ) (i j : Fin (n+2)) :
    (M * B) i j = (M.mulVec (fun k => B k j)) i := by
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

lemma ite_zero_mul (P : Prop) [Decidable P] (a b : ℂ) :
    ((if P then a else 0) * b) = if P then a * b else 0 := by
  by_cases h : P <;> simp [h]

lemma sum_ite_val_eq {N : ℕ} (f : Fin N → ℂ) (c : ℕ) (hc : c < N) (a : ℂ) :
    ∑ k : Fin N, (if k.val = c then a * f k else 0) = a * f ⟨c, hc⟩ := by
  have h : ∀ k : Fin N, (k.val = c) ↔ (k = ⟨c, hc⟩) :=
    fun k => ⟨fun hk => Fin.ext hk, fun hk => by rw [hk]⟩
  simp only [h]
  rw [Finset.sum_ite_eq' Finset.univ ⟨c, hc⟩ (fun k => a * f k)]
  simp

lemma smMat_mulVec_zero (n : ℕ) (d : ℕ → ℂ) (t : ℂ) (x : Fin (n+2) → ℂ) :
    ((smMat n d t).mulVec x) 0 = x 0 - t⁻¹ * x ⟨n, by omega⟩ := by
  rw [Matrix.mulVec, dotProduct]
  simp only [smMat, Matrix.of_apply]
  simp only [Fin.val_zero]
  simp only [true_and, add_mul, Finset.sum_add_distrib]
  simp only [show ¬ ((0:ℕ) = 1) by simp, show ¬ (2 ≤ (0:ℕ)) by simp,
    false_and, if_false, zero_mul, Finset.sum_const_zero]
  simp only [ite_zero_mul, sum_ite_val_eq x 0 (by omega) 1, sum_ite_val_eq x n (by omega) (-t⁻¹)]
  simp
  ring

lemma smMat_mulVec_one (n : ℕ) (d : ℕ → ℂ) (t : ℂ) (x : Fin (n+2) → ℂ) :
    ((smMat n d t).mulVec x) 1 = -t * x 1 + x ⟨n+1, by omega⟩ := by
  rw [Matrix.mulVec, dotProduct]
  simp only [smMat, Matrix.of_apply]
  simp only [Fin.val_one]
  simp only [true_and, add_mul, Finset.sum_add_distrib]
  simp only [show ¬ ((1:ℕ) = 0) by simp, show ¬ (2 ≤ (1:ℕ)) by simp,
    false_and, if_false, zero_mul, Finset.sum_const_zero]
  simp only [ite_zero_mul, sum_ite_val_eq x 1 (by omega) (-t), sum_ite_val_eq x (n+1) (by omega) 1]
  simp

lemma smMat_mulVec_of (n : ℕ) (d : ℕ → ℂ) (t : ℂ) (x : Fin (n+2) → ℂ)
    (i : Fin (n+2)) (hi : 2 ≤ i.val) :
    ((smMat n d t).mulVec x) i
      = x ⟨i.val-2, by omega⟩ - d (i.val-2) * x ⟨i.val-1, by omega⟩ + x i := by
  rw [Matrix.mulVec, dotProduct]
  simp only [smMat, Matrix.of_apply]
  have h0 : ¬ (i.val = 0) := by omega
  have h1 : ¬ (i.val = 1) := by omega
  simp only [h0, h1, false_and, if_false, zero_add]
  simp only [hi, true_and]
  have h2 : ∀ k : Fin (n+2), (k.val + 2 = i.val) ↔ (k.val = i.val - 2) := fun k => by omega
  have h3 : ∀ k : Fin (n+2), (k.val + 1 = i.val) ↔ (k.val = i.val - 1) := fun k => by omega
  simp only [h2, h3]
  simp only [add_mul, Finset.sum_add_distrib]
  simp only [ite_zero_mul, sum_ite_val_eq x (i.val - 2) (by omega) 1,
    sum_ite_val_eq x (i.val - 1) (by omega) (-(d (i.val-2))), sum_ite_val_eq x i.val (by omega) 1]
  simp
  ring

lemma smMat_mulVec_row (n : ℕ) (d : ℕ → ℂ) (t : ℂ) (x : Fin (n+2) → ℂ)
    (i : ℕ) (hi : i + 2 < n + 2) :
    ((smMat n d t).mulVec x) ⟨i+2, hi⟩
      = x ⟨i, by omega⟩ - d i * x ⟨i+1, by omega⟩ + x ⟨i+2, hi⟩ := by
  have h2 : 2 ≤ (⟨i+2, hi⟩ : Fin (n+2)).val := by simp
  have h := smMat_mulVec_of n d t x (⟨i+2, hi⟩ : Fin (n+2)) h2
  have e1 : (⟨(⟨i+2, hi⟩ : Fin (n+2)).val - 2, by omega⟩ : Fin (n+2)) = ⟨i, by omega⟩ :=
    Fin.ext (by simp)
  have e2 : (⟨(⟨i+2, hi⟩ : Fin (n+2)).val - 1, by omega⟩ : Fin (n+2)) = ⟨i+1, by omega⟩ :=
    Fin.ext (by simp)
  have e3 : (⟨i+2, hi⟩ : Fin (n+2)).val - 2 = i := by simp
  rw [e1, e2, e3] at h
  exact h

/-! ### Multiplying by `TMat` -/

lemma smMat_mul_TMat_delta (n : ℕ) (d : ℕ → ℂ) (t : ℂ)
    (j : Fin (n+2)) (i : ℕ) (hi : i + 2 < n + 2) :
    (smMat n d t * TMat n d) ⟨i+2, hi⟩ j
      = if (⟨i+2, hi⟩ : Fin (n+2)) = j then 1 else 0 := by
  rw [mul_apply_eq_mulVec, smMat_mulVec_row n d t (fun k => TMat n d k j) i hi,
    TMat_col_rec n d j i hi]
  by_cases h : j.val = i + 2
  · rw [if_pos h, if_pos (Fin.ext h.symm)]
  · rw [if_neg h, if_neg (fun he => h (by have := congrArg Fin.val he; simp at this; omega))]

lemma smMat_mul_TMat_of (n : ℕ) (d : ℕ → ℂ) (t : ℂ)
    (i j : Fin (n+2)) (hi : 2 ≤ i.val) :
    (smMat n d t * TMat n d) i j = if i = j then 1 else 0 := by
  have hidx : (⟨i.val - 2 + 2, by omega⟩ : Fin (n+2)) = i :=
    Fin.ext (by simp; omega)
  rw [← hidx]
  exact smMat_mul_TMat_delta n d t j (i.val - 2) (by omega)

lemma smMat_mul_TMat_00 (n : ℕ) (d : ℕ → ℂ) (t : ℂ) :
    (smMat n d t * TMat n d) 0 0 = 1 - t⁻¹ * (transProd d n) 1 1 := by
  rw [mul_apply_eq_mulVec, smMat_mulVec_zero, TMat_col_zero, TMat_col_zero]
  simp

lemma smMat_mul_TMat_01 (n : ℕ) (d : ℕ → ℂ) (t : ℂ) :
    (smMat n d t * TMat n d) 0 1 = -t⁻¹ * (transProd d n) 1 0 := by
  rw [mul_apply_eq_mulVec, smMat_mulVec_zero, TMat_col_one, TMat_col_one]
  simp

lemma smMat_mul_TMat_10 (n : ℕ) (d : ℕ → ℂ) (t : ℂ) :
    (smMat n d t * TMat n d) 1 0 = (transProd d n) 0 1 := by
  rw [mul_apply_eq_mulVec, smMat_mulVec_one, TMat_col_zero, TMat_col_zero]
  rw [show ((1 : Fin (n+2)) : ℕ) = 1 from Fin.val_one _]
  rw [transProd_one, transProd_succ_11]
  simp [tm2]

lemma smMat_mul_TMat_11 (n : ℕ) (d : ℕ → ℂ) (t : ℂ) :
    (smMat n d t * TMat n d) 1 1 = (transProd d n) 0 0 - t := by
  rw [mul_apply_eq_mulVec, smMat_mulVec_one, TMat_col_one, TMat_col_one]
  rw [show ((1 : Fin (n+2)) : ℕ) = 1 from Fin.val_one _]
  rw [transProd_one, transProd_succ_10]
  simp [tm2]
  ring

/-! ### The determinant identity -/

lemma smMat_det_trace (n : ℕ) (d : ℕ → ℂ) (t : ℂ) (ht : t ≠ 0) :
    (smMat n d t).det = (transProd d n).trace - (t + t⁻¹) := by
  have h1 : (smMat n d t).det = (smMat n d t * TMat n d).det := by
    rw [Matrix.det_mul, TMat_det n d, mul_one]
  rw [h1, det_eq_topleft_of n (smMat n d t * TMat n d) (smMat_mul_TMat_of n d t)]
  rw [smMat_mul_TMat_00, smMat_mul_TMat_01, smMat_mul_TMat_10, smMat_mul_TMat_11]
  rw [Matrix.trace_fin_two]
  have hdetA : (transProd d n) 0 0 * (transProd d n) 1 1 - (transProd d n) 0 1 * (transProd d n) 1 0 = 1 := by
    have h := transProd_det d n
    rwa [Matrix.det_fin_two] at h
  have h0 : t⁻¹ * t = 1 := by rw [mul_comm]; exact mul_inv_cancel₀ ht
  have key : (1 - t⁻¹ * (transProd d n) 1 1) * ((transProd d n) 0 0 - t)
      - (-t⁻¹ * (transProd d n) 1 0) * (transProd d n) 0 1
      = (transProd d n) 0 0 + (transProd d n) 1 1 - (t + t⁻¹) := by
    have hk : (1 - t⁻¹ * (transProd d n) 1 1) * ((transProd d n) 0 0 - t)
        - (-t⁻¹ * (transProd d n) 1 0) * (transProd d n) 0 1
        - ((transProd d n) 0 0 + (transProd d n) 1 1 - (t + t⁻¹))
        = t⁻¹ * (1 - ((transProd d n) 0 0 * (transProd d n) 1 1
            - (transProd d n) 0 1 * (transProd d n) 1 0))
          + (transProd d n) 1 1 * (t⁻¹ * t - 1) := by ring
    rw [hdetA, sub_self, mul_zero, zero_add, h0, sub_self, mul_zero] at hk
    exact sub_eq_zero.mp hk
  exact key

end SmTrace

theorem smMat_trace (q : ℕ) (d : ℕ → ℂ) (t : ℂ) (ht : t ≠ 0) :
    (Work.TMC14Core.smMat (q+1) d t).det = (Work.TMC14Core.transProd d (q+1)).trace - (t + t⁻¹) :=
  SmTrace.smMat_det_trace (q+1) d t ht

end Work.TMC14Core
