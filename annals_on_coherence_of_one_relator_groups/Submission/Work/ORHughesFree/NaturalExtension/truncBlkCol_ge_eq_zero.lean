import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.TruncDefect

namespace Work.ORHughesFree.NaturalExtension

theorem truncBlkCol_ge_eq_zero {U : Type} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    {m k : ℕ} (B : Matrix (Fin m) (Fin k) (SkewL U)) (i : ℕ) {u : ℤ} (hu : (i : ℤ) ≤ u)
    {p : Fin (k * i)} (hp : lowerDeg B + (p.modNat : ℕ) < i) (j : Fin m) :
    truncBlkCol B i u j p = 0 := by
  rw [truncBlkCol]
  -- The relevant coefficient degree `p.modNat - u` lies below `-lowerDeg B`, hence vanishes.
  have hk : ((p.modNat : ℤ) - u) < -(lowerDeg B : ℤ) := by
    have h2 : (lowerDeg B : ℤ) + (p.modNat : ℤ) < (i : ℤ) := by
      omega
    omega
  rw [coeffMat_apply, coeffElt_eq_zero_of_lt_lowerDeg B j p.divNat hk, smul_zero]

end Work.ORHughesFree.NaturalExtension
