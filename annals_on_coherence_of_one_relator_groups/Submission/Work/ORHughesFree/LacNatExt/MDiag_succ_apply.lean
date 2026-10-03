import Mathlib
import Submission.Work.ORHughesFree.LacNatExt.PolyTDefs

namespace Work.ORHughesFree.NaturalExtension

open Matrix

noncomputable section

/-! ## The entries of `lacMDiag B (d + 1)`

`lacMDiag B D = 1 + ∑_{k < D} C_k·t·t^k` (where `C_k` is the `k`-th coefficient matrix of `B`), so
its `(p,q)` entry is `δ_{pq} + ∑_{k<D} (C_k)_{pq}·t^{k+1}`.  This file computes the case `D = d+1`
explicitly, splitting off the `k = 0` term.

The three ingredients are:
* `lacMDiag_succ_t_pow` : `t^k = single (ofAdd k) 1`;
* `lacMDiag_succ_single_mul_pow` : `single (ofAdd 1) r * t^k = single (ofAdd (k+1)) r`;
* `lacMDiag_succ_AtC_diag` : the `(p,q)` entry of `lacAtC C * diag (t^k)` is `single (ofAdd (k+1)) (C p q)`.
-/

variable {R : Type*} [Ring R] [MulSemiringAction (Multiplicative ℤ) R]

/-- The powers of the variable `t` of `R[t^{±1};τ]`: `t ^ k = single (ofAdd k) 1`. -/
theorem lacMDiag_succ_t_pow (k : ℕ) :
    (skewLaurentT : SkewL R) ^ k
      = SkewMonoidAlgebra.single (Multiplicative.ofAdd (k : ℤ)) (1 : R) := by
  induction k with
  | zero =>
    rw [pow_zero, SkewMonoidAlgebra.one_def]
    simp only [Nat.cast_zero, ofAdd_zero]
  | succ k ih =>
    rw [pow_succ, ih, skewLaurentT, SkewMonoidAlgebra.single_mul_single]
    simp

/-- Multiplication of `r·t` by a power of the variable: `(single (ofAdd 1) r) * t^k`
is `single (ofAdd (k+1)) r`.  (The twist of `τ` does not enter because it acts on the scalar `1`.) -/
theorem lacMDiag_succ_single_mul_pow (r : R) (k : ℕ) :
    SkewMonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) r * (skewLaurentT : SkewL R) ^ k
      = SkewMonoidAlgebra.single (Multiplicative.ofAdd ((k : ℤ) + 1)) r := by
  rw [lacMDiag_succ_t_pow, SkewMonoidAlgebra.single_mul_single, ← ofAdd_add]
  have h : (1 : ℤ) + (k : ℤ) = (k : ℤ) + 1 := by ring
  rw [h]
  simp

/-- The `(p,q)` entry of `lacAtC C * diag (t^k)` is `single (ofAdd (k+1)) (C p q)`. -/
theorem lacMDiag_succ_AtC_diag {n : ℕ} (C : Matrix (Fin n) (Fin n) R) (k : ℕ) (p q : Fin n) :
    (lacAtC C * Matrix.diagonal (fun _ : Fin n => (skewLaurentT : SkewL R) ^ k)) p q
      = SkewMonoidAlgebra.single (Multiplicative.ofAdd ((k : ℤ) + 1)) (C p q) := by
  rw [Matrix.mul_diagonal]
  simp [lacAtC, lacmulTElt, lacMDiag_succ_single_mul_pow]

/-- The sum over `Fin (d+1)` of the entries of the `t`-terms, with the `k = 0` term split off. -/
theorem lacMDiag_succ_sum {n : ℕ} (B : Matrix (Fin n) (Fin n) (SkewL R)) (d : ℕ) (p q : Fin n) :
    (∑ k : Fin (d + 1), (lacAtC (lacCcoef B (k : ℕ)) *
        Matrix.diagonal (fun _ : Fin n => (skewLaurentT : SkewL R) ^ (k : ℕ))) p q)
      = SkewMonoidAlgebra.single (Multiplicative.ofAdd 1) (lacCcoef B 0 p q)
        + ∑ i : Fin d, SkewMonoidAlgebra.single (Multiplicative.ofAdd ((i : ℤ) + 2))
            (lacCcoef B ((i : ℕ) + 1) p q) := by
  rw [Fin.sum_univ_succ]
  congr 1
  · rw [lacMDiag_succ_AtC_diag]
    simp
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [lacMDiag_succ_AtC_diag]
    have h : (((i : ℕ) + 1 : ℕ) : ℤ) + 1 = (i : ℤ) + 2 := by push_cast; ring
    simp only [Fin.val_succ, h]

theorem lacMDiag_succ_apply {R : Type*} [Ring R] [MulSemiringAction (Multiplicative ℤ) R] {n : ℕ}
    (B : Matrix (Fin n) (Fin n) (SkewL R)) (d : ℕ) (p q : Fin n) :
    lacMDiag B (d + 1) p q
      = (1 : Matrix (Fin n) (Fin n) (SkewL R)) p q
        + SkewMonoidAlgebra.single (Multiplicative.ofAdd 1) (lacCcoef B 0 p q)
        + ∑ i : Fin d, SkewMonoidAlgebra.single (Multiplicative.ofAdd ((i : ℤ) + 2))
            (lacCcoef B ((i : ℕ) + 1) p q) := by
  unfold lacMDiag
  rw [Matrix.add_apply, Matrix.sum_apply, lacMDiag_succ_sum, add_assoc]

end

end Work.ORHughesFree.NaturalExtension
