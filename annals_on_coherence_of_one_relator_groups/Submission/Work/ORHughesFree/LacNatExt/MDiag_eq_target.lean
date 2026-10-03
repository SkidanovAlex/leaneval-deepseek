/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `1 + B·diag(t)` is the truncation `lacMDiag B (d+1)`

`lacMDiag B D = 1 + ∑_{k<D} C_k·t · diag(t^k)` is the "linearization target" of
`Submission.Work.ORHughesFree.NaturalExtension.PolyTDefs`: the matrix `1 + B * diag(t)` written as
a sum of the `D` lowest coefficient matrices `C_k = coeffMat B k`, each multiplied by `t`.

This file proves that, when all coefficients of `B` of negative degree vanish and `upperDeg B ≤ d`,
this sum with `D = d + 1` reproduces `1 + B·diag(t)`.

The mathematical content is entirely at the level of a single entry `f = B i j` of `B`: writing
`f = ∑_{k=0}^{d} (f_k) t^k` (`f_k = coeffElt f k`), the identity is
`(∑_{k=0}^{d} f_k·t·t^k) = (∑_{k=0}^{d} f_k t^k)·t`.  The two ingredients of this element-level
computation are proved in the sibling files of this directory and imported below:

* `lacelt_eq_sum_single` : expansion of an element whose coefficients vanish outside `[0,d]` into
  monomials, `f = ∑_{k=0}^{d} (coeffElt f k)·t^k`;
* `lacsum_single_mul_skewLaurentT` : distributing the right factor `t` over such a sum;
* `lacsum_AtC_diag_apply` : the entrywise computation `(C_k·t · diag(t^k))_{ij} = (C_k)_{ij}·t^{k+1}`
  of the `k`-th summand of `lacMDiag`.

The matrix identity then follows by comparing entries, using `Matrix.mul_diagonal` and the
coefficient extraction `coeffMat_apply`.
-/
import Mathlib
import Submission.Work.ORHughesFree.LacNatExt.PolyTDefs
import Submission.Work.ORHughesFree.LacNatExt.elt_eq_sum_single
import Submission.Work.ORHughesFree.LacNatExt.sum_single_mul_skewLaurentT
import Submission.Work.ORHughesFree.LacNatExt.sum_AtC_diag_apply

set_option autoImplicit false

namespace Work.ORHughesFree.NaturalExtension

open Matrix

/-! ## The element-level identity -/

/-- Element-level form of `lacMDiag_eq_target`: for `f` with all coefficients outside `[0,d]`
vanishing, `f·t = ∑_{k=0}^{d} (coeffElt f k)·t^{k+1}`.  This is the expansion
`lacelt_eq_sum_single` of `f` into monomials, multiplied by `t` via `lacsum_single_mul_skewLaurentT`. -/
theorem lacMDiagEq_elt_mul_t {R : Type*} [Ring R] [MulSemiringAction (Multiplicative ℤ) R]
    (f : SkewL R) (d : ℕ) (hneg : ∀ k : ℤ, k < 0 → coeffElt f k = 0)
    (hup : ∀ k : ℤ, (d : ℤ) < k → coeffElt f k = 0) :
    f * skewLaurentT = ∑ k : Fin (d + 1),
      SkewMonoidAlgebra.single (Multiplicative.ofAdd ((k : ℤ) + 1)) (coeffElt f (k : ℤ)) := by
  conv_lhs => rw [lacelt_eq_sum_single f d hneg hup]
  exact lacsum_single_mul_skewLaurentT (fun m : ℕ => coeffElt f (m : ℤ)) d

/-! ## The target identity -/

theorem lacMDiag_eq_target {R : Type*} [Ring R] [MulSemiringAction (Multiplicative ℤ) R]
    {n : ℕ} (B : Matrix (Fin n) (Fin n) (SkewL R))
    (hB : ∀ i j, ∀ k : ℤ, k < 0 → coeffElt (B i j) k = 0) (d : ℕ) (hd : upperDeg B ≤ d) :
    lacMDiag B (d + 1) = 1 + B * Matrix.diagonal (fun _ => skewLaurentT) := by
  -- every entry of `B` has all its coefficients outside `[0,d]` equal to zero
  have hup : ∀ (i j : Fin n), ∀ k : ℤ, (d : ℤ) < k → coeffElt (B i j) k = 0 := by
    intro i j k hk
    refine coeffElt_eq_zero_of_gt_upperDeg B i j ?_
    have h1 : (upperDeg B : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    omega
  -- the sum of the `d+1` lowest terms of `B` is `B * diag t`, entrywise
  have hsum : (∑ k : Fin (d + 1), lacAtC (lacCcoef B (k : ℕ)) *
        Matrix.diagonal (fun _ : Fin n => (skewLaurentT : SkewL R) ^ (k : ℕ))) =
      B * Matrix.diagonal (fun _ : Fin n => (skewLaurentT : SkewL R)) := by
    apply Matrix.ext
    intro i j
    calc (∑ k : Fin (d + 1), lacAtC (lacCcoef B (k : ℕ)) *
              Matrix.diagonal (fun _ : Fin n => (skewLaurentT : SkewL R) ^ (k : ℕ))) i j
        = ∑ k : Fin (d + 1),
            SkewMonoidAlgebra.single (Multiplicative.ofAdd ((k : ℤ) + 1))
              ((lacCcoef B (k : ℕ)) i j) := lacsum_AtC_diag_apply B d i j
      _ = ∑ k : Fin (d + 1),
            SkewMonoidAlgebra.single (Multiplicative.ofAdd ((k : ℤ) + 1))
              (coeffElt (B i j) (k : ℤ)) := by
            refine Finset.sum_congr rfl (fun k _ => ?_)
            simp only [lacCcoef, coeffMat_apply]
      _ = (B i j) * skewLaurentT := (lacMDiagEq_elt_mul_t (B i j) d (hB i j) (hup i j)).symm
      _ = (B * Matrix.diagonal (fun _ : Fin n => (skewLaurentT : SkewL R))) i j := by
            rw [Matrix.mul_diagonal]
  show 1 + (∑ k : Fin (d + 1), lacAtC (lacCcoef B (k : ℕ)) *
        Matrix.diagonal (fun _ : Fin n => (skewLaurentT : SkewL R) ^ (k : ℕ))) =
      1 + B * Matrix.diagonal (fun _ : Fin n => (skewLaurentT : SkewL R))
  rw [hsum]

end Work.ORHughesFree.NaturalExtension
