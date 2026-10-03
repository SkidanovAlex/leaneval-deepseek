import Mathlib

namespace Work.FIArea6.S16ErrTwo

/-- The integer interval `[-K-1, K+1]` consists of the two new endpoints `±(K+1)`
together with the previous interval `[-K, K]`. -/
lemma Icc_neg_succ (K : ℕ) :
    Finset.Icc (-(((K + 1 : ℕ)) : ℤ)) (((K + 1 : ℕ)) : ℤ)
      = insert (-(((K + 1 : ℕ)) : ℤ))
          (insert (((K + 1 : ℕ)) : ℤ) (Finset.Icc (-(K : ℤ)) (K : ℤ))) := by
  ext n
  simp only [Finset.mem_Icc, Finset.mem_insert]
  omega

/-- `natAbs` of `(K : ℤ) + 1`. -/
lemma natAbs_cast_add_one (K : ℕ) : (((K : ℤ) + 1).natAbs) = K + 1 := by
  rw [show (K : ℤ) + 1 = ((K + 1 : ℕ) : ℤ) by simp, Int.natAbs_natCast]

/-- The symmetric reciprocal sum over the integer interval `[-K, K]` equals twice the
`K`-th harmonic number. -/
lemma sum_Icc_natAbs_inv_eq (K : ℕ) :
    (∑ n ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), (((n.natAbs : ℕ) : ℝ))⁻¹)
      = 2 * (harmonic K : ℝ) := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hm1 : -(((K + 1 : ℕ)) : ℤ) ∉
        insert (((K + 1 : ℕ)) : ℤ) (Finset.Icc (-(K : ℤ)) (K : ℤ)) := by
      intro h
      rw [Finset.mem_insert, Finset.mem_Icc] at h
      omega
    have hm2 : (((K + 1 : ℕ)) : ℤ) ∉ Finset.Icc (-(K : ℤ)) (K : ℤ) := by
      intro h
      rw [Finset.mem_Icc] at h
      omega
    rw [Icc_neg_succ K, Finset.sum_insert hm1, Finset.sum_insert hm2]
    rw [ih, harmonic_succ]
    push_cast
    rw [Int.natAbs_neg, natAbs_cast_add_one]
    push_cast
    ring

theorem sum_natAbs_inv_le (K : ℕ) (hK : 1 ≤ K) :
    (∑ n ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), (((n.natAbs : ℕ) : ℝ))⁻¹)
      ≤ 2 * (1 + Real.log (K : ℝ)) := by
  have _ := hK
  rw [sum_Icc_natAbs_inv_eq K]
  have h := harmonic_le_one_add_log K
  linarith

end Work.FIArea6.S16ErrTwo
