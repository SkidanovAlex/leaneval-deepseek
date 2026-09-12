import Submission.WnormToolkit
import Submission.DivLinear

/-!
# Weighted-norm product and interconversion bounds on the Serre interval

For the real-polynomial weighted norm `wnorm k` of `Submission.Contracts`
(weight `w = weight muSerre`, sup over `[aSerre,bSerre]`) and the unweighted
sup-norm `DivLinear.supNorm` on the same interval:

* `‖P·Q‖_k ≤ ‖P‖_k · ‖Q‖`  and  `‖P·Q‖_k ≤ ‖P‖ · ‖Q‖_k`
  (used to bound the weighted `(n−m)`-norm of `P̃·Q` in the early-ints
  assembly from the weighted norm of `P̃` and the sup-norm of `Q`);
* `‖P‖_k ≤ M^k · ‖P‖` when `M ≥ 0` bounds the weight from above
  (`M` from `WeightedNorm.weight_bdd_on_Icc`).
-/

noncomputable section

open scoped Real
open Polynomial

namespace Submission.WnormProduct

open Submission.Contracts
open Submission.Serre
open Submission.SerreExample
open Submission.WeightedNorm
open Submission.WnormToolkit
open Submission.DivLinear

/-- pointwise value of the product is `w^k|P(x)||Q(x)|`. -/
lemma ptwise_eval_mul (k : ℕ) (P Q : Polynomial ℝ) (x : ℝ) :
    (weight muSerre x) ^ k * |(P * Q).eval x| =
      ((weight muSerre x) ^ k * |P.eval x|) * |Q.eval x| := by
  rw [eval_mul, abs_mul]
  ring

/-- `‖P·Q‖_k ≤ ‖P‖_k · ‖Q‖`. -/
lemma wnorm_mul_le_sup (k : ℕ) (P Q : Polynomial ℝ) :
    wnorm k (P * Q) ≤ wnorm k P * DivLinear.supNorm Q := by
  apply wnorm_sSup_le
  intro x hx
  calc
    (weight muSerre x) ^ k * |(P * Q).eval x|
        = ((weight muSerre x) ^ k * |P.eval x|) * |Q.eval x| := ptwise_eval_mul k P Q x
    _ ≤ wnorm k P * |Q.eval x| := by
        exact mul_le_mul_of_nonneg_right (wnorm_ge_pointwise k P hx) (abs_nonneg _)
    _ ≤ wnorm k P * DivLinear.supNorm Q := by
        exact mul_le_mul_of_nonneg_left (DivLinear.abs_eval_le_supNorm (P := Q) x hx) (wnorm_nonneg k P)

/-- `‖P·Q‖_k ≤ ‖P‖ · ‖Q‖_k` (right factor weighted). -/
lemma wnorm_sup_mul_le (k : ℕ) (P Q : Polynomial ℝ) :
    wnorm k (P * Q) ≤ DivLinear.supNorm P * wnorm k Q := by
  rw [mul_comm]
  calc wnorm k (Q * P) ≤ wnorm k Q * DivLinear.supNorm P := wnorm_mul_le_sup k Q P
    _ = DivLinear.supNorm P * wnorm k Q := by rw [mul_comm]

/-- bound form of the product inequality (left factor weighted). -/
lemma wnorm_mul_le_of_weighted {k : ℕ} {P Q : Polynomial ℝ} {A B : ℝ}
    (hP : wnorm k P ≤ A) (hQ : DivLinear.supNorm Q ≤ B) (hA : 0 ≤ A) :
    wnorm k (P * Q) ≤ A * B := by
  calc wnorm k (P * Q) ≤ wnorm k P * DivLinear.supNorm Q := wnorm_mul_le_sup k P Q
    _ ≤ A * B := by
        exact mul_le_mul hP hQ (DivLinear.supNorm_nonneg Q) hA

/-- bound form of the product inequality (right factor weighted). -/
lemma wnorm_mul_le_of_sup {k : ℕ} {P Q : Polynomial ℝ} {A B : ℝ}
    (hP : DivLinear.supNorm P ≤ A) (hQ : wnorm k Q ≤ B) :
    wnorm k (P * Q) ≤ A * B := by
  calc wnorm k (P * Q) ≤ DivLinear.supNorm P * wnorm k Q := wnorm_sup_mul_le k P Q
    _ ≤ A * B := by
        exact mul_le_mul hP hQ (wnorm_nonneg k Q) (le_trans (DivLinear.supNorm_nonneg P) hP)

/-- `‖P‖_k ≤ M^k · ‖P‖` when `0 ≤ M` bounds the weight on the interval. -/
lemma wnorm_le_Mpow_sup {k : ℕ} {M : ℝ} {P : Polynomial ℝ}
    (hM : 0 ≤ M) (hMb : ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre →
      weight muSerre x ≤ M) :
    wnorm k P ≤ M ^ k * DivLinear.supNorm P := by
  apply wnorm_sSup_le
  intro x hx
  calc
    (weight muSerre x) ^ k * |P.eval x| ≤ M ^ k * |P.eval x| := by
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (le_of_lt (weight_pos muSerre x)) (hMb x hx) k) (abs_nonneg _)
    _ ≤ M ^ k * DivLinear.supNorm P := by
        exact mul_le_mul_of_nonneg_left (DivLinear.abs_eval_le_supNorm (P := P) x hx) (pow_nonneg hM k)

end Submission.WnormProduct
