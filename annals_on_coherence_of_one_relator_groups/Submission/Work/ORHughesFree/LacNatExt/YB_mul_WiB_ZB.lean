import Mathlib
import Submission.Work.ORHughesFree.LacNatExt.PolyTDefs
import Submission.Work.ORHughesFree.LacNatExt.WiB_mul_ZB
import Submission.Work.ORHughesFree.LacNatExt.singleOne_mul_skewLaurentT_pow

namespace Work.ORHughesFree.NaturalExtension

open Matrix

theorem lacYB_mul_WiB_ZB {R : Type*} [Ring R] [MulSemiringAction (Multiplicative ℤ) R] {n : ℕ}
    (B : Matrix (Fin n) (Fin n) (SkewL R)) (d : ℕ) (p q : Fin n) :
    (lacYB B d * (lacWiB (R := R) d n * lacZB (R := R) d n)) p q
      = - ∑ i : Fin d, SkewMonoidAlgebra.single (Multiplicative.ofAdd ((i : ℤ) + 2))
          (lacCcoef B ((i : ℕ) + 1) p q) := by
  rw [Matrix.mul_apply]
  have step3 : ∀ i : Fin d,
      (∑ j : Fin n, lacAtC (lacCcoef B ((i : ℕ) + 1)) p j *
          (if j = q then -(skewLaurentT ^ ((i : ℕ) + 1)) else 0))
        = - SkewMonoidAlgebra.single (Multiplicative.ofAdd ((i : ℤ) + 2))
            (lacCcoef B ((i : ℕ) + 1) p q) := by
    intro i
    simp only [mul_ite, mul_zero]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true]
    rw [lacAtC, Matrix.map_apply, lacmulTElt, mul_neg, lacsingleOne_mul_skewLaurentT_pow]
    have hidx : ((↑((i : ℕ) + 1) : ℤ) + 1) = ((i : ℕ) : ℤ) + 2 := by
      push_cast; ring
    rw [hidx]
  trans ∑ r : Fin (d * n),
      lacAtC (lacCcoef B ((r.divNat : ℕ) + 1)) p r.modNat *
        (if r.modNat = q then -(skewLaurentT ^ ((r.divNat : ℕ) + 1)) else 0)
  · refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [lacWiB_mul_ZB]
    rfl
  trans ∑ i : Fin d, ∑ j : Fin n,
      lacAtC (lacCcoef B ((i : ℕ) + 1)) p j *
        (if j = q then -(skewLaurentT ^ ((i : ℕ) + 1)) else 0)
  · exact Work.ORHughesFree.MatrixBlocks.sum_finProdFin
      (f := fun (i : Fin d) (j : Fin n) => lacAtC (lacCcoef B ((i : ℕ) + 1)) p j *
        (if j = q then -(skewLaurentT ^ ((i : ℕ) + 1)) else 0))
  trans ∑ i : Fin d, (- SkewMonoidAlgebra.single (Multiplicative.ofAdd ((i : ℤ) + 2))
      (lacCcoef B ((i : ℕ) + 1) p q))
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    exact step3 i
  · exact Finset.sum_neg_distrib (f := fun i : Fin d =>
      SkewMonoidAlgebra.single (Multiplicative.ofAdd ((i : ℤ) + 2))
        (lacCcoef B ((i : ℕ) + 1) p q))

end Work.ORHughesFree.NaturalExtension
