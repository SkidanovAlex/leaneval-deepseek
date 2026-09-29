import Mathlib
import Submission.Work.ConvR.basic

/-!
# Auxiliary norm and linearity lemmas for the ConvR `norms` package

This file (owned by the `Work.ConvR.norms` area) collects the elementary facts about the
synthetic ring `ℝ = ℂ[y]/(y^r+1)` and its DFT that the main `norms` statement needs:

* `vget_sub` : `vget` is additive;
* `yMul_norm_le` : multiplication by `y^e` does not increase the sup norm;
* `yMul_sub` : multiplication by `y^e` is additive;
* `synDFT_apply`, `synDFT_sub` : the synthetic DFT is a sum of `yMul`-images, hence additive.

The remaining conjuncts of `Work.ConvR.norms` (`negaMul` bounds/additivity and the `convR`
bound) are proved in the sibling files `negaNorm.lean`, `negaLin.lean`, `synNorm.lean` and
assembled in `norms.lean`.
-/

set_option autoImplicit false

namespace Work.ConvR

open HvdH

/-- `vget` is additive in the vector. -/
theorem vget_sub {n : ℕ} (u v : Fin n → ℂ) (i : ℕ) :
    HvdH.vget (u - v) i = HvdH.vget u i - HvdH.vget v i := by
  by_cases h : i < n
  · rw [HvdH.vget, dite_eq_left h, HvdH.vget, dite_eq_left h, HvdH.vget, dite_eq_left h]
    rfl
  · rw [HvdH.vget, dite_eq_right h, HvdH.vget, dite_eq_right h, HvdH.vget, dite_eq_right h]
    simp

/-- Multiplication by `y^e` does not increase the sup norm: `y^e` acts by a signed permutation
of the coefficients. -/
theorem yMul_norm_le (r : ℕ) (e : ℤ) (a : Fin r → ℂ) :
    ‖HvdH.yMul r e a‖ ≤ ‖a‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg a)).2 (fun k => ?_)
  rw [HvdH.yMul]
  have h1 : ‖(if Even ((((k : ℤ) - e) % (r : ℤ) + e - (k : ℤ)) / (r : ℤ)) then (1 : ℂ) else -1)‖
      = 1 := by
    split <;> simp
  rw [norm_mul, h1, one_mul]
  by_cases h : (((k : ℤ) - e) % (r : ℤ)).toNat < r
  · rw [HvdH.vget, dite_eq_left h]
    exact norm_le_pi_norm a ⟨_, h⟩
  · rw [HvdH.vget, dite_eq_right h]
    simp

/-- Multiplication by `y^e` is additive (indeed `ℂ`-linear). -/
theorem yMul_sub (r : ℕ) (e : ℤ) (a b : Fin r → ℂ) :
    HvdH.yMul r e (a - b) = HvdH.yMul r e a - HvdH.yMul r e b := by
  funext k
  rw [Pi.sub_apply]
  rw [HvdH.yMul, HvdH.yMul, HvdH.yMul]
  simp only [HvdH.vget]
  split <;> split <;> (try rw [Pi.sub_apply]) <;> ring

/-- Explicit form of the synthetic DFT as a sum of `yMul`-images. -/
theorem synDFT_apply (r : ℕ) (ts : List ℕ) (sgn : ℤ) (u : Fin ts.prod → Fin r → ℂ)
    (j : Fin ts.prod) (c : Fin r) :
    HvdH.synDFT r ts sgn u j c = 1 / (ts.prod : ℂ) * ∑ k : Fin ts.prod,
      HvdH.yMul r (sgn * HvdH.synExp r ts (HvdH.digits ts (j : ℕ)) (HvdH.digits ts (k : ℕ)))
        (u k) c := rfl

/-- The synthetic DFT is additive in the array. -/
theorem synDFT_sub (r : ℕ) (ts : List ℕ) (sgn : ℤ) (u v : Fin ts.prod → Fin r → ℂ) :
    HvdH.synDFT r ts sgn (u - v) = HvdH.synDFT r ts sgn u - HvdH.synDFT r ts sgn v := by
  funext j c
  rw [Pi.sub_apply, Pi.sub_apply]
  rw [synDFT_apply, synDFT_apply, synDFT_apply]
  have h1 : (∑ x : Fin ts.prod,
        HvdH.yMul r (sgn * HvdH.synExp r ts (HvdH.digits ts (j : ℕ)) (HvdH.digits ts (x : ℕ)))
          ((u - v) x) c)
      = (∑ k : Fin ts.prod,
          HvdH.yMul r (sgn * HvdH.synExp r ts (HvdH.digits ts (j : ℕ)) (HvdH.digits ts (k : ℕ)))
            (u k) c)
        - (∑ k : Fin ts.prod,
          HvdH.yMul r (sgn * HvdH.synExp r ts (HvdH.digits ts (j : ℕ)) (HvdH.digits ts (k : ℕ)))
            (v k) c) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [Pi.sub_apply]
    rw [HvdH.yMul, HvdH.yMul, HvdH.yMul]
    simp only [HvdH.vget]
    split <;> split <;> (try rw [Pi.sub_apply]) <;> ring
  rw [h1]
  ring

end Work.ConvR
