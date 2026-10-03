import Mathlib
import Submission.Work.ORHughesFree.LacNatExt.ShiftDefs

namespace Work.ORHughesFree.NaturalExtension

open Matrix

/-- Injectivity of the decomposition `q ↦ (q.divNat, q.modNat)` of `Fin (m * n)`: two indices
with the same block index and the same inner index are equal. -/
lemma lacfin_eq_of_divNat_modNat {m n : ℕ} {q q' : Fin (m * n)}
    (h1 : (q.divNat : ℕ) = (q'.divNat : ℕ)) (h2 : q.modNat = q'.modNat) : q = q' := by
  have h : (finProdFinEquiv.symm q) = (finProdFinEquiv.symm q') := by
    rw [finProdFinEquiv_symm_apply, finProdFinEquiv_symm_apply, Prod.mk.injEq]
    exact ⟨Fin.ext h1, h2⟩
  exact finProdFinEquiv.symm.injective h

theorem lacWB_eq_SB {R : Type*} [Ring R] [MulSemiringAction (Multiplicative ℤ) R] (d n : ℕ) :
    lacWB (R := R) d n = -1 + lacSB (R := R) d n := by
  ext q q'
  have hWB : lacWB (R := R) d n q q' =
      (if (q.divNat : ℕ) = (q'.divNat : ℕ) then
        (if q.modNat = q'.modNat then (-1 : SkewL R) else 0) else 0) +
      (if (q.divNat : ℕ) = (q'.divNat : ℕ) + 1 then
        (if q.modNat = q'.modNat then (skewLaurentT : SkewL R) else 0) else 0) := rfl
  have hneg : (-1 : Matrix (Fin (d * n)) (Fin (d * n)) (SkewL R)) q q' =
      (if (q.divNat : ℕ) = (q'.divNat : ℕ) then
        (if q.modNat = q'.modNat then (-1 : SkewL R) else 0) else 0) := by
    rw [Matrix.neg_apply, Matrix.one_apply]
    by_cases hd : (q.divNat : ℕ) = (q'.divNat : ℕ)
    · by_cases hm : q.modNat = q'.modNat
      · rw [if_pos (lacfin_eq_of_divNat_modNat hd hm), if_pos hd, if_pos hm]
      · rw [if_neg (fun h => hm (by rw [h])), if_pos hd, if_neg hm]; simp
    · rw [if_neg (fun h => hd (by rw [h])), if_neg hd]; simp
  have hSB : lacSB (R := R) d n q q' =
      (if (q.divNat : ℕ) = (q'.divNat : ℕ) + 1 then
        (if q.modNat = q'.modNat then (skewLaurentT : SkewL R) else 0) else 0) := by
    rw [lacSB]
    by_cases hP : (q.divNat : ℕ) = (q'.divNat : ℕ) + 1
    · by_cases hQ : q.modNat = q'.modNat
      · rw [if_pos ⟨hP, hQ⟩, if_pos hP, if_pos hQ]
      · rw [if_neg (fun h => hQ h.2), if_pos hP, if_neg hQ]
    · rw [if_neg (fun h => hP h.1), if_neg hP]
  rw [hWB, Matrix.add_apply, hneg, hSB]

end Work.ORHughesFree.NaturalExtension
