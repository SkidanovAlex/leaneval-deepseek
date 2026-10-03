import Mathlib
import Submission.Work.ORHughesFree.SkewLaurentSeries.VanishesBelow

namespace Work.ORHughesFree.SkewLaurentSeries

/-- The monomial `a·t⁰` is the coefficient embedding `coeff a`. -/
theorem mono_zero_eq_coeff {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A]
    (a : A) : mono (0 : ℤ) a = coeff a := Subtype.ext rfl

theorem isUnit_mono_of_isUnit {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A] (m : ℤ) {a : A} (ha : IsUnit a) : IsUnit (mono m a) := by
  -- `mono m a = (coeff a) · (tᵐ)`, a product of two units.
  have ht : IsUnit (mono m (1 : A)) := by
    -- `tᵐ = mono m 1` is a unit with inverse `mono (-m) 1 = t⁻ᵐ`.
    refine ⟨⟨mono m 1, mono (-m) 1, ?_, ?_⟩, rfl⟩
    · rw [mono_mul, show m + -m = 0 from by ring]
      simp only [MulSemiringAction.smul_one, _root_.mul_one]
      exact mono_zero_one
    · rw [mono_mul, show -m + m = 0 from by ring]
      simp only [MulSemiringAction.smul_one, _root_.mul_one]
      exact mono_zero_one
  have hmul : coeff a * mono m 1 = mono m a := by
    rw [← mono_zero_eq_coeff a, mono_mul]
    simp only [_root_.zero_add, MulSemiringAction.smul_one, _root_.mul_one]
  rw [← hmul]
  -- `coeff a` is a unit since `coeff` is a ring homomorphism and `a` is a unit.
  exact (ha.map (skewLaurentCoeff A)).mul ht

end Work.ORHughesFree.SkewLaurentSeries
