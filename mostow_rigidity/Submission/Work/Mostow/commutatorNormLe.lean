import Mathlib
import Submission.Work.Mostow.StabLift

namespace Work.Mostow

-- File: Submission/Work/Mostow/commutatorNormLe.lean (module Submission.Work.Mostow.commutatorNormLe).
-- Useful imports: import Submission.Work.Mostow.StabLift (LambdaMat_mul, LambdaMat_inv, LambdaMat_one).
-- `open scoped Matrix.Norms.Operator` (submultiplicative operator norm, ‖1‖ = 1);
-- `open scoped commutatorElement` for ⁅g, h⁆ = g * h * g⁻¹ * h⁻¹.
-- Mathematical content (contraction of commutators near the identity):
-- with A = LambdaMat g = 1 + a, B = LambdaMat h = 1 + b and ‖a‖, ‖b‖ ≤ 1/4 one has
-- ‖⁅A, B⁆ - 1‖ ≤ 4 ‖a‖ ‖b‖.  Pure normed-ring algebra: LambdaMat (⁅g,h⁆) = ⁅A,B⁆ by
-- LambdaMat_mul/LambdaMat_inv, and with A' = LambdaMat g⁻¹, B' = LambdaMat h⁻¹ (so A*A' = A'*A = 1,
-- B*B' = B'*B = 1) one has ⁅A,B⁆ - 1 = (A*B - C*A) * A' * B' and A*B - B*A = a*b - b*a, while
-- ‖A' - 1‖ ≤ ‖a‖ / (1 - ‖a‖) ≤ 4/3 ‖a‖ and similarly for B', whence ‖A'*B'‖ ≤ 16/9.
-- Only `2 * (16/9) ≤ 4` remains.
open scoped Matrix.Norms.Operator
open scoped commutatorElement
open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {n : ℕ}

/-- Contraction of the multiplicative commutator in a matrix ring, with the (submultiplicative)
operator norm: if `A * A' = 1`, `B * B' = 1` and `A`, `B` are within `1/4` of the identity, then
`A * B * A' * B'` is within `4 ‖A - 1‖ ‖B - 1‖` of the identity.

This is the pure normed-ring content of `commutatorNormLe`; note that no invertibility of `A', B'`
beyond `A * A' = 1`, `B * B' = 1` is used. -/
lemma commutator_contraction {n : ℕ}
    (A B A' B' : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ)
    (hAA' : A * A' = 1) (hBB' : B * B' = 1)
    (hAn : ‖A - 1‖ ≤ 1 / 4) (hBn : ‖B - 1‖ ≤ 1 / 4) :
    ‖A * B * A' * B' - 1‖ ≤ 4 * ‖A - 1‖ * ‖B - 1‖ := by
  -- `A A' = 1` gives `A' = 1 - (A-1) A'`, whence `‖A'‖ ≤ 1 + ‖A-1‖ ‖A'‖ ≤ 4/3`.
  have hA'norm : ‖A'‖ ≤ 4 / 3 := by
    have h1 : A' = 1 - (A - 1) * A' := by
      have h3 : (1 + (A - 1)) * A' = 1 := by
        rw [show (1 + (A - 1)) = A from by abel]; exact hAA'
      rw [add_mul, one_mul] at h3
      exact eq_sub_iff_add_eq.mpr h3
    have h2 : ‖A'‖ ≤ 1 + ‖A - 1‖ * ‖A'‖ := by
      calc ‖A'‖ = ‖1 - (A - 1) * A'‖ := by conv_lhs => rw [h1]
        _ ≤ ‖(1 : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ)‖ + ‖(A - 1) * A'‖ :=
            norm_sub_le _ _
        _ = 1 + ‖(A - 1) * A'‖ := by rw [norm_one]
        _ ≤ 1 + ‖A - 1‖ * ‖A'‖ := by gcongr; exact norm_mul_le _ _
    nlinarith [h2, hAn, norm_nonneg A']
  have hB'norm : ‖B'‖ ≤ 4 / 3 := by
    have h1 : B' = 1 - (B - 1) * B' := by
      have h3 : (1 + (B - 1)) * B' = 1 := by
        rw [show (1 + (B - 1)) = B from by abel]; exact hBB'
      rw [add_mul, one_mul] at h3
      exact eq_sub_iff_add_eq.mpr h3
    have h2 : ‖B'‖ ≤ 1 + ‖B - 1‖ * ‖B'‖ := by
      calc ‖B'‖ = ‖1 - (B - 1) * B'‖ := by conv_lhs => rw [h1]
        _ ≤ ‖(1 : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ)‖ + ‖(B - 1) * B'‖ :=
            norm_sub_le _ _
        _ = 1 + ‖(B - 1) * B'‖ := by rw [norm_one]
        _ ≤ 1 + ‖B - 1‖ * ‖B'‖ := by gcongr; exact norm_mul_le _ _
    nlinarith [h2, hBn, norm_nonneg B']
  -- `A B - B A = (A-1)(B-1) - (B-1)(A-1)`, so `‖A B - B A‖ ≤ 2 ‖A-1‖ ‖B-1‖`.
  have hAB : ‖A * B - B * A‖ ≤ 2 * ‖A - 1‖ * ‖B - 1‖ := by
    have he : A * B - B * A = (A - 1) * (B - 1) - (B - 1) * (A - 1) := by
      rw [sub_mul, mul_sub, one_mul, mul_one, sub_mul, mul_sub, one_mul, mul_one]; abel
    rw [he]
    calc ‖(A - 1) * (B - 1) - (B - 1) * (A - 1)‖
        ≤ ‖(A - 1) * (B - 1)‖ + ‖(B - 1) * (A - 1)‖ := norm_sub_le _ _
      _ ≤ ‖A - 1‖ * ‖B - 1‖ + ‖B - 1‖ * ‖A - 1‖ := by
          gcongr <;> exact norm_mul_le _ _
      _ = 2 * ‖A - 1‖ * ‖B - 1‖ := by ring
  -- `A B A' B' - 1 = (A B - B A) (A' B')` because `B A A' B' = B B' = 1`.
  have hdec : A * B * A' * B' - 1 = (A * B - B * A) * (A' * B') := by
    have hBA : (B * A) * (A' * B') = 1 := by
      rw [mul_assoc, ← mul_assoc A A' B', hAA', one_mul, hBB']
    rw [sub_mul, hBA]
    rw [mul_assoc]
  have hA'mul : ‖A' * B'‖ ≤ 16 / 9 := by
    calc ‖A' * B'‖ ≤ ‖A'‖ * ‖B'‖ := norm_mul_le _ _
      _ ≤ (4 / 3) * (4 / 3) := by gcongr
      _ = 16 / 9 := by norm_num
  rw [hdec]
  calc ‖(A * B - B * A) * (A' * B')‖
      ≤ ‖A * B - B * A‖ * ‖A' * B'‖ := norm_mul_le _ _
    _ ≤ (2 * ‖A - 1‖ * ‖B - 1‖) * (16 / 9) := by
        refine mul_le_mul hAB hA'mul (norm_nonneg _) ?_
        positivity
    _ ≤ 4 * ‖A - 1‖ * ‖B - 1‖ := by
        nlinarith [norm_nonneg (A - 1), norm_nonneg (B - 1),
          mul_nonneg (norm_nonneg (A - 1)) (norm_nonneg (B - 1))]

/-- `Λ` carries the group commutator of `PO(n,1)` to the multiplicative commutator of matrices. -/
lemma LambdaMat_commutator (hA : POActionProp n) (g h : PO n 1) :
    LambdaMat ⁅g, h⁆ = LambdaMat g * LambdaMat h * LambdaMat g⁻¹ * LambdaMat h⁻¹ := by
  rw [show ⁅g, h⁆ = ((g * h) * g⁻¹) * h⁻¹ from by rw [commutatorElement_def],
    LambdaMat_mul hA, LambdaMat_mul hA, LambdaMat_mul hA]

theorem commutatorNormLe (n : ℕ) (hA : POActionProp n)
    (g h : PO n 1)
    (hg : ‖Work.Mostow.LambdaMat g - 1‖ ≤ 1 / 4)
    (hh : ‖Work.Mostow.LambdaMat h - 1‖ ≤ 1 / 4) :
    ‖Work.Mostow.LambdaMat ⁅g, h⁆ - 1‖ ≤
      4 * ‖Work.Mostow.LambdaMat g - 1‖ * ‖Work.Mostow.LambdaMat h - 1‖ := by
  have hkey := commutator_contraction (LambdaMat g) (LambdaMat h) (LambdaMat g⁻¹) (LambdaMat h⁻¹)
    (LambdaMat_inv hA g) (LambdaMat_inv hA h) hg hh
  rw [LambdaMat_commutator hA g h]
  exact hkey

end

end Work.Mostow
