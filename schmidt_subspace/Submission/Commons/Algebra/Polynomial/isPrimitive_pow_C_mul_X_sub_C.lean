import Mathlib.RingTheory.Polynomial.Content

namespace Commons.Algebra.Polynomial

open Polynomial

/-- If `a b : ℤ` are coprime, then `(b·X - a)^l` is a primitive integer polynomial. -/
theorem isPrimitive_pow_C_mul_X_sub_C (a b : ℤ) (h : IsCoprime a b) (l : ℕ) :
    ((Polynomial.C b * Polynomial.X - Polynomial.C a) ^ l).IsPrimitive := by
  -- The linear polynomial `b·X - a` is primitive: any constant `C r` dividing it
  -- must divide both `b` (coefficient of `X`) and `a` (negative of the constant
  -- coefficient), hence is a unit since `a` and `b` are coprime.
  have hf : (Polynomial.C b * Polynomial.X - Polynomial.C a).IsPrimitive := by
    intro r hr
    obtain ⟨g, hg⟩ := hr
    have hb : r ∣ b := by
      have hc := congrArg (fun p : Polynomial ℤ => p.coeff 1) hg
      rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_C, Polynomial.coeff_X,
        Polynomial.coeff_C_mul] at hc
      norm_num at hc
      exact ⟨g.coeff 1, hc⟩
    have ha : r ∣ a := by
      have hc := congrArg (fun p : Polynomial ℤ => p.coeff 0) hg
      rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_C, Polynomial.coeff_X,
        Polynomial.coeff_C_mul] at hc
      norm_num at hc
      exact dvd_neg.mp ⟨g.coeff 0, hc⟩
    exact h.isUnit_of_dvd' ha hb
  -- Primitiveness is preserved by products, hence by powers.
  induction l with
  | zero =>
      rw [pow_zero]
      intro r hr
      exact Polynomial.isUnit_C.mp (isUnit_iff_dvd_one.mpr hr)
  | succ n ih =>
      rw [pow_succ]
      exact ih.mul hf

end Commons.Algebra.Polynomial