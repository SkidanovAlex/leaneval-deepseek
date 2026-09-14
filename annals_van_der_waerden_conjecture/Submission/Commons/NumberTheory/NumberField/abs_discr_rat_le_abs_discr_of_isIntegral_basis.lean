import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Rat.Star
import Submission.Commons.NumberTheory.NumberField.discr_dvd_of_isIntegral_basis

namespace Commons.NumberTheory.NumberField

open Module in
/-- **The field discriminant is bounded by the discriminant of any integral `ℚ`-basis.**

If `b` is a `ℚ`-basis of a number field `K` all of whose elements are algebraic integers, then
`b` spans a `ℤ`-order `ℤ b ⊆ 𝓞 K` and `Algebra.discr ℚ b = [𝓞 K : ℤ b]^2 · discr K`, so
`|discr K| ≤ |Algebra.discr ℚ b|` (as rational numbers).

Proof: `Commons.NumberTheory.NumberField.discr_dvd_of_isIntegral_basis` gives
`Algebra.discr ℚ b = (NumberField.discr K : ℚ) * m` for some `m : ℤ`; `m ≠ 0` because
`Algebra.discr ℚ b ≠ 0` (`Algebra.discr_not_zero_of_basis`, using `Algebra.IsSeparable ℚ K`,
automatic in characteristic `0`) and `NumberField.discr K ≠ 0` (`NumberField.discr_ne_zero`);
then `|m| ≥ 1` (`Int.one_le_abs`) and `abs_mul` finish. -/
theorem abs_discr_rat_le_abs_discr_of_isIntegral_basis {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ K)
    (hb : ∀ i : ι, IsIntegral ℤ (b i)) :
    |(NumberField.discr K : ℚ)| ≤ |Algebra.discr ℚ b| := by
  classical
  obtain ⟨m, hm⟩ := discr_dvd_of_isIntegral_basis b hb
  have hb0 : Algebra.discr ℚ b ≠ 0 := Algebra.discr_not_zero_of_basis ℚ b
  have hm0 : m ≠ 0 := by
    intro h
    apply hb0
    rw [hm, h, Int.cast_zero, mul_zero]
  have hm1 : (1 : ℚ) ≤ |(m : ℚ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hm0
  rw [hm, abs_mul]
  exact le_mul_of_one_le_right (abs_nonneg _) hm1

end Commons.NumberTheory.NumberField