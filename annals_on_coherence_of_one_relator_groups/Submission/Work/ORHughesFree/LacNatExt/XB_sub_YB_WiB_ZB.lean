import Mathlib
import Submission.Work.ORHughesFree.LacNatExt.PolyTDefs
import Submission.Work.ORHughesFree.LacNatExt.MDiag_succ_apply
import Submission.Work.ORHughesFree.LacNatExt.YB_mul_WiB_ZB

namespace Work.ORHughesFree.NaturalExtension

open Matrix

/-- Powers of the variable `t` of the skew Laurent polynomial ring, in normal form. -/
lemma lacskewLaurentT_pow {R : Type*} [Ring R] [MulSemiringAction (Multiplicative ℤ) R] (k : ℕ) :
    (skewLaurentT (R := R)) ^ k = SkewMonoidAlgebra.single (Multiplicative.ofAdd (k:ℤ)) (1:R) := by
  rw [skewLaurentT]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, SkewMonoidAlgebra.single_mul_single]
    simp

lemma lacofAdd_one_mul (k : ℕ) :
    (Multiplicative.ofAdd (1:ℤ) : Multiplicative ℤ) * Multiplicative.ofAdd (k:ℤ)
      = Multiplicative.ofAdd ((k:ℤ)+1) := by
  rw [← ofAdd_add]
  congr 1
  omega

/-- Entry of `lacAtC C * diag(t^k)`. -/
lemma lacAtC_mul_diag_apply {R : Type*} [Ring R] [MulSemiringAction (Multiplicative ℤ) R] {n : ℕ}
    (C : Matrix (Fin n) (Fin n) R) (k : ℕ) (p q : Fin n) :
    ((lacAtC C) * (Matrix.diagonal (fun _ : Fin n => (skewLaurentT (R:=R))^k))) p q
      = SkewMonoidAlgebra.single (Multiplicative.ofAdd ((k:ℤ)+1)) (C p q) := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single q]
  · simp only [Matrix.diagonal_apply_eq, lacAtC, Matrix.map_apply, lacmulTElt]
    rw [lacskewLaurentT_pow, SkewMonoidAlgebra.single_mul_single, lacofAdd_one_mul, smul_one, mul_one]
  · intro b _ hb
    rw [Matrix.diagonal_apply]
    simp [hb]
  · intro h; exact absurd (Finset.mem_univ q) h

/-- Entry of the `(0,0)` block `lacXB B = 1 + C_0 t`. -/
lemma lacXB_apply {R : Type*} [Ring R] [MulSemiringAction (Multiplicative ℤ) R] {n : ℕ}
    (B : Matrix (Fin n) (Fin n) (SkewL R)) (p q : Fin n) :
    lacXB B p q = (1 : Matrix (Fin n) (Fin n) (SkewL R)) p q
      + SkewMonoidAlgebra.single (Multiplicative.ofAdd 1) (lacCcoef B 0 p q) := by
  simp only [lacXB, onePlusAt, Matrix.add_apply, Matrix.map_apply]

/-- **Schur-complement identity for the companion matrix.**  The `(0,0)` block of the companion,
`lacXB B = 1 + C_0 t`, minus the block row `lacYB B d = (C_1 t, …, C_d t)` times the block column
`lacWiB d n * lacZB d n = -(t, t^2, …, t^d)^T` is the linearization target `lacMDiag B (d+1)`. -/
theorem lacXB_sub_YB_WiB_ZB {R : Type*} [Ring R] [MulSemiringAction (Multiplicative ℤ) R]
    {n : ℕ} (B : Matrix (Fin n) (Fin n) (SkewL R)) (d : ℕ) :
    lacXB B - lacYB B d * (lacWiB (R := R) d n * lacZB (R := R) d n) = lacMDiag B (d + 1) := by
  ext p q
  rw [Matrix.sub_apply, lacXB_apply B p q, lacYB_mul_WiB_ZB B d p q, lacMDiag_succ_apply B d p q,
    sub_neg_eq_add]

end Work.ORHughesFree.NaturalExtension
