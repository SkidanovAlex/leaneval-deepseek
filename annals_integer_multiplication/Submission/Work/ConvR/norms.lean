import Mathlib
import Submission.Work.ConvR.basic
import Submission.Work.ConvR.normsAux
import Submission.Work.ConvR.negaNorm
import Submission.Work.ConvR.negaLin
import Submission.Work.ConvR.synNorm

/-!
# Norm and linearity facts for the convolution over `ℝ = ℂ[y]/(y^r+1)` (paper §2.3, §3)

This file assembles the `norms` package used by the ConvR pipeline (paper Lemma 2.5,
Proposition 3.4 and the error analysis of the synthetic transform):

* `yMul r e` (multiplication by `y^e`) is a contraction and is additive
  (`Submission/Work/ConvR/normsAux.lean`);
* `negaMul` (the product of `ℂ[y]/(y^r+1)`) satisfies `‖negaMul r a b‖ ≤ r‖a‖‖b‖` and is additive
  in each variable (`Submission/Work/ConvR/negaNorm.lean`, `negaLin.lean`);
* `synDFT` is a contraction and is additive (`Submission/Work/ConvR/synNorm.lean`,
  `normsAux.lean`);
* `convR` is a contraction: `‖convR r ts u v‖ ≤ ‖u‖ ‖v‖`, which is the pointwise product
  estimate `‖negaMul r a b‖ ≤ r‖a‖‖b‖` combined with the normalisation `1/(M·r)`, `M = ∏ tᵢ`
  (proved here).

The theorem `norms` is the conjunction of all eight facts, in the order requested by the
ConvR area; the `KernelLib` hypothesis is not needed (everything here is pure mathematics).
-/

set_option autoImplicit false

namespace Work.ConvR

open HvdH

/-- Explicit form of the convolution `M_ℝ` of the synthetic ring: it is `1/(M·r)` times the
sum over the `M = ts.prod` shifts `k` of the negacyclic product of `u k` with the `(j-k)`-th
slice of `v`. -/
theorem convR_apply (r : ℕ) (ts : List ℕ) (u v : Fin ts.prod → Fin r → ℂ)
    (j : Fin ts.prod) (c : Fin r) :
    HvdH.convR r ts u v j c = 1 / ((ts.prod * r : ℕ) : ℂ) * ∑ k : Fin ts.prod,
      HvdH.negaMul r (u k)
        (fun c' => if h : HvdH.subIdx ts (j : ℕ) (k : ℕ) < ts.prod then v ⟨_, h⟩ c' else 0) c :=
  rfl

/-- Each shifted slice `v_{j-k}` of the convolution has sup norm at most `‖v‖`. -/
theorem convR_slice_norm_le (r : ℕ) (ts : List ℕ) (v : Fin ts.prod → Fin r → ℂ)
    (j k : Fin ts.prod) :
    ‖(fun c' => if h : HvdH.subIdx ts (j : ℕ) (k : ℕ) < ts.prod then v ⟨_, h⟩ c' else 0)‖
      ≤ ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg v)).2 (fun c' => ?_)
  by_cases h : HvdH.subIdx ts (j : ℕ) (k : ℕ) < ts.prod
  · rw [dite_eq_left h]
    exact le_trans (norm_le_pi_norm (v ⟨_, h⟩) c') (norm_le_pi_norm v ⟨_, h⟩)
  · rw [dite_eq_right h]
    simp

/-- The synthetic convolution is a contraction for the sup norm. -/
theorem convR_norm (r : ℕ) (ts : List ℕ) (u v : Fin ts.prod → Fin r → ℂ)
    (hM : 0 < ts.prod) (hr : 0 < r) : ‖HvdH.convR r ts u v‖ ≤ ‖u‖ * ‖v‖ := by
  have hnn : 0 ≤ ‖u‖ * ‖v‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  refine (pi_norm_le_iff_of_nonneg hnn).2 (fun j => ?_)
  refine (pi_norm_le_iff_of_nonneg hnn).2 (fun c => ?_)
  rw [convR_apply]
  have hSum : ‖∑ k : Fin ts.prod, HvdH.negaMul r (u k)
        (fun c' => if h : HvdH.subIdx ts (j : ℕ) (k : ℕ) < ts.prod then v ⟨_, h⟩ c' else 0) c‖
      ≤ (ts.prod : ℝ) * ((r : ℝ) * ‖u‖ * ‖v‖) := by
    calc ‖∑ k : Fin ts.prod, HvdH.negaMul r (u k)
          (fun c' => if h : HvdH.subIdx ts (j : ℕ) (k : ℕ) < ts.prod then v ⟨_, h⟩ c' else 0) c‖
        ≤ ∑ k : Fin ts.prod, ‖HvdH.negaMul r (u k)
            (fun c' => if h : HvdH.subIdx ts (j : ℕ) (k : ℕ) < ts.prod then v ⟨_, h⟩ c' else 0) c‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _k : Fin ts.prod, (r : ℝ) * ‖u‖ * ‖v‖ := by
          apply Finset.sum_le_sum
          intro k _
          calc ‖HvdH.negaMul r (u k)
                (fun c' => if h : HvdH.subIdx ts (j : ℕ) (k : ℕ) < ts.prod then v ⟨_, h⟩ c' else 0) c‖
              ≤ ‖HvdH.negaMul r (u k)
                (fun c' => if h : HvdH.subIdx ts (j : ℕ) (k : ℕ) < ts.prod then v ⟨_, h⟩ c' else 0)‖ :=
                norm_le_pi_norm _ c
            _ ≤ (r : ℝ) * ‖u k‖ * ‖(fun c' => if h : HvdH.subIdx ts (j : ℕ) (k : ℕ) < ts.prod then v ⟨_, h⟩ c' else 0)‖ :=
                negaNorm r _ _
            _ ≤ (r : ℝ) * ‖u‖ * ‖v‖ := by
                have h1 : ‖u k‖ ≤ ‖u‖ := norm_le_pi_norm u k
                have h2 : ‖(fun c' => if h : HvdH.subIdx ts (j : ℕ) (k : ℕ) < ts.prod then v ⟨_, h⟩ c' else 0)‖ ≤ ‖v‖ :=
                  convR_slice_norm_le r ts v j k
                have hu : (0 : ℝ) ≤ ‖u‖ := norm_nonneg _
                calc (r : ℝ) * ‖u k‖ * ‖(fun c' => if h : HvdH.subIdx ts (j : ℕ) (k : ℕ) < ts.prod then v ⟨_, h⟩ c' else 0)‖
                    = (r : ℝ) * (‖u k‖ * ‖(fun c' => if h : HvdH.subIdx ts (j : ℕ) (k : ℕ) < ts.prod then v ⟨_, h⟩ c' else 0)‖) := by ring
                  _ ≤ (r : ℝ) * (‖u‖ * ‖v‖) := by
                      apply mul_le_mul_of_nonneg_left
                      · exact mul_le_mul h1 h2 (norm_nonneg _) hu
                      · exact Nat.cast_nonneg r
                  _ = (r : ℝ) * ‖u‖ * ‖v‖ := by ring
      _ = (ts.prod : ℝ) * ((r : ℝ) * ‖u‖ * ‖v‖) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc ‖1 / ((ts.prod * r : ℕ) : ℂ) * (∑ k : Fin ts.prod, HvdH.negaMul r (u k)
        (fun c' => if h : HvdH.subIdx ts (j : ℕ) (k : ℕ) < ts.prod then v ⟨_, h⟩ c' else 0) c)‖
      = ‖(1 / ((ts.prod * r : ℕ) : ℂ))‖ * ‖∑ k : Fin ts.prod, HvdH.negaMul r (u k)
        (fun c' => if h : HvdH.subIdx ts (j : ℕ) (k : ℕ) < ts.prod then v ⟨_, h⟩ c' else 0) c‖ :=
        norm_mul _ _
    _ = ((ts.prod * r : ℕ) : ℝ)⁻¹ * ‖∑ k : Fin ts.prod, HvdH.negaMul r (u k)
        (fun c' => if h : HvdH.subIdx ts (j : ℕ) (k : ℕ) < ts.prod then v ⟨_, h⟩ c' else 0) c‖ := by
        rw [one_div, norm_inv, Complex.norm_natCast]
    _ ≤ ((ts.prod * r : ℕ) : ℝ)⁻¹ * ((ts.prod : ℝ) * ((r : ℝ) * ‖u‖ * ‖v‖)) := by
        apply mul_le_mul_of_nonneg_left hSum
        positivity
    _ = ‖u‖ * ‖v‖ := by
        rw [Nat.cast_mul,
          show (ts.prod : ℝ) * ((r : ℝ) * ‖u‖ * ‖v‖)
              = ((ts.prod : ℝ) * (r : ℝ)) * (‖u‖ * ‖v‖) by ring]
        have hx : ((ts.prod : ℝ) * (r : ℝ)) ≠ 0 := by positivity
        rw [← mul_assoc, inv_mul_cancel₀ hx, one_mul]

/-- **The `norms` package of the ConvR area**: `yMul` is a contraction and additive; `negaMul`
is bounded by `r‖a‖‖b‖` and additive in each variable; `synDFT` is a contraction and additive;
`convR` is a contraction.  The hypothesis `KernelLib` is not needed. -/
theorem norms (hK : HvdH.KernelLib) :
    (∀ (r : ℕ) (e : ℤ) (a : Fin r → ℂ), ‖HvdH.yMul r e a‖ ≤ ‖a‖) ∧
    (∀ (r : ℕ) (e : ℤ) (a b : Fin r → ℂ), HvdH.yMul r e (a - b) = HvdH.yMul r e a - HvdH.yMul r e b) ∧
    (∀ (r : ℕ) (a b : Fin r → ℂ), ‖HvdH.negaMul r a b‖ ≤ r * ‖a‖ * ‖b‖) ∧
    (∀ (r : ℕ) (a a' b : Fin r → ℂ),
      HvdH.negaMul r (a - a') b = HvdH.negaMul r a b - HvdH.negaMul r a' b) ∧
    (∀ (r : ℕ) (a b b' : Fin r → ℂ),
      HvdH.negaMul r a (b - b') = HvdH.negaMul r a b - HvdH.negaMul r a b') ∧
    (∀ (r : ℕ) (ts : List ℕ) (sgn : ℤ) (u : Fin ts.prod → Fin r → ℂ),
      0 < ts.prod → ‖HvdH.synDFT r ts sgn u‖ ≤ ‖u‖) ∧
    (∀ (r : ℕ) (ts : List ℕ) (sgn : ℤ) (u v : Fin ts.prod → Fin r → ℂ),
      HvdH.synDFT r ts sgn (u - v) = HvdH.synDFT r ts sgn u - HvdH.synDFT r ts sgn v) ∧
    (∀ (r : ℕ) (ts : List ℕ) (u v : Fin ts.prod → Fin r → ℂ),
      0 < ts.prod → 0 < r → ‖HvdH.convR r ts u v‖ ≤ ‖u‖ * ‖v‖) := by
  refine ⟨yMul_norm_le, yMul_sub, negaNorm, ?_, ?_, synNorm, synDFT_sub, convR_norm⟩
  · exact fun r => (negaLin r).1
  · exact fun r => (negaLin r).2

end Work.ConvR
