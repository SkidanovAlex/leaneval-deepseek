import Mathlib
import Submission.Work.ORHughesFree.LacNatExt.ShiftDefs

namespace Work.ORHughesFree.NaturalExtension

/-- `lacWiB` is the inverse of `lacWB = -1 + lacSB`, and since `lacSB` is nilpotent with `lacSB ^ d = 0`,
this inverse is the finite geometric series `-(∑_{k<d} lacSB^k)`. -/
theorem lacWiB_eq {R : Type*} [Ring R] [MulSemiringAction (Multiplicative ℤ) R] (d n : ℕ) :
    lacWiB (R := R) d n = -(∑ k ∈ Finset.range d, (lacSB (R := R) d n) ^ k) := by
  apply Matrix.ext
  intro q q'
  simp only [lacWiB, Matrix.neg_apply, Matrix.sum_apply, lacSB_pow_apply]
  by_cases hM : q.modNat = q'.modNat
  · have hsum : (∑ x ∈ Finset.range d,
        (if (q.divNat : ℕ) = (q'.divNat : ℕ) + x ∧ q.modNat = q'.modNat
          then (skewLaurentT : SkewL R) ^ x else 0))
        = (if (q'.divNat : ℕ) ≤ (q.divNat : ℕ)
            then (skewLaurentT : SkewL R) ^ ((q.divNat : ℕ) - (q'.divNat : ℕ)) else 0) := by
      by_cases hle : (q'.divNat : ℕ) ≤ (q.divNat : ℕ)
      · rw [if_pos hle, Finset.sum_eq_single ((q.divNat : ℕ) - (q'.divNat : ℕ))]
        · rw [if_pos ⟨by omega, hM⟩]
        · intro b hb hbne
          rw [if_neg]
          rintro ⟨h, -⟩
          omega
        · intro hmem
          exfalso
          rw [Finset.mem_range] at hmem
          have hq : (q.divNat : ℕ) < d := q.divNat.isLt
          omega
      · rw [if_neg hle, Finset.sum_eq_zero]
        · intro x hx
          rw [if_neg]
          rintro ⟨h, -⟩
          omega
    rw [hsum]
    by_cases hle : (q'.divNat : ℕ) ≤ (q.divNat : ℕ)
    · rw [if_pos hle, if_pos hM, if_pos hle]
    · rw [if_neg hle, if_neg hle, neg_zero]
  · have hzero : (∑ x ∈ Finset.range d,
        (if (q.divNat : ℕ) = (q'.divNat : ℕ) + x ∧ q.modNat = q'.modNat
          then (skewLaurentT : SkewL R) ^ x else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      rw [if_neg]
      rintro ⟨-, h⟩
      exact hM h
    rw [hzero, neg_zero]
    by_cases hle : (q'.divNat : ℕ) ≤ (q.divNat : ℕ)
    · rw [if_pos hle, if_neg hM]
    · rw [if_neg hle]

end Work.ORHughesFree.NaturalExtension
