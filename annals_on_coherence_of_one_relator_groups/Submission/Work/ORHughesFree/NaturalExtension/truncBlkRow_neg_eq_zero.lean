import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.TruncDefect

namespace Work.ORHughesFree.NaturalExtension

theorem truncBlkRow_neg_eq_zero {U : Type} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    {n m : ℕ} (A : Matrix (Fin n) (Fin m) (SkewL U)) (i : ℕ) {u : ℤ} (hu : u < 0)
    {q : Fin (n * i)} (hq : lowerDeg A ≤ (q.modNat : ℕ)) (j : Fin m) :
    truncBlkRow A i u q j = 0 := by
  simp only [truncBlkRow, coeffMat_apply]
  have h : u - (q.modNat : ℤ) < -(lowerDeg A : ℤ) := by
    have h1 : (lowerDeg A : ℤ) ≤ (q.modNat : ℤ) := by exact_mod_cast hq
    omega
  rw [coeffElt_eq_zero_of_lt_lowerDeg A _ _ h, smul_zero]

end Work.ORHughesFree.NaturalExtension
