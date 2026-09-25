import Mathlib

namespace Work.LT

/-- For an integer `a`, the real number `a.natAbs` equals the absolute value of `a`. -/
lemma int_natAbs_cast_real (a : ℤ) : ((a.natAbs : ℕ) : ℝ) = |(a : ℝ)| := by
  rw [← Int.cast_abs (R := ℝ) (a := a), ← Int.natCast_natAbs a]
  simp

/-- `Real.sin (π · A / p) ^ 2` depends on `A` only through `|A|`. -/
lemma sin_sq_pi_abs (p : ℕ) (A : ℝ) :
    Real.sin (Real.pi * A / p) ^ 2 = Real.sin (Real.pi * |A| / p) ^ 2 := by
  rcases abs_cases A with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]
  · rw [h]
    have h2 : Real.pi * (-A) / p = -(Real.pi * A / p) := by ring
    rw [h2, Real.sin_neg, neg_sq]

theorem sin_sq_even_natAbs (p : ℕ) [NeZero p] (t : ZMod p) :
    Real.sin (Real.pi * ((ZMod.valMinAbs t : ℤ) : ℝ) / p) ^ 2
      = Real.sin (Real.pi * ((ZMod.valMinAbs t).natAbs : ℝ) / p) ^ 2 := by
  have hc := int_natAbs_cast_real (ZMod.valMinAbs t)
  rw [hc]
  exact sin_sq_pi_abs p _

end Work.LT
