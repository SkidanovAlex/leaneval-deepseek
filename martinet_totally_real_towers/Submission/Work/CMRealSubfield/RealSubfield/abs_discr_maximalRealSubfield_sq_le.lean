import Mathlib

namespace Work.CMRealSubfield.RealSubfield

open NumberField

/-- For a CM field `K` with maximal real subfield `K⁺`, the square of the absolute value of the
discriminant of `K⁺` is bounded by the absolute value of the discriminant of `K`.

This is the standard discriminant inequality for a CM field. Since `K/K⁺` is a quadratic
extension, the tower formula for discriminants
`NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow` gives

  `(disc K).natAbs = (absNorm (differentIdeal (𝓞 K⁺) (𝓞 K))).natAbs * ((disc K⁺).natAbs) ^ 2`,

so `((disc K⁺).natAbs) ^ 2` divides `(disc K).natAbs`. As `disc K ≠ 0`, `Nat.le_of_dvd` yields
the corresponding inequality of natural numbers, which is transported to `ℝ` along
`|(z : ℝ)| = (z.natAbs : ℝ)`. -/
theorem abs_discr_maximalRealSubfield_sq_le (K : Type*) [Field K] [NumberField K]
    [NumberField.IsCMField K] :
    |(NumberField.discr (NumberField.maximalRealSubfield K) : ℝ)| ^ 2 ≤
      |(NumberField.discr K : ℝ)| := by
  -- The square of the absolute discriminant of `K⁺` divides the absolute discriminant of `K`.
  have hdvd : ((NumberField.discr (NumberField.maximalRealSubfield K)).natAbs) ^ 2 ∣
      (NumberField.discr K).natAbs := by
    have h := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
      (K := NumberField.maximalRealSubfield K) (𝒪 := 𝓞 (NumberField.maximalRealSubfield K))
      (L := K) (𝒪' := 𝓞 K)
    rw [h, Algebra.IsQuadraticExtension.finrank_eq_two (NumberField.maximalRealSubfield K) K]
    exact dvd_mul_left _ _
  -- A number field has nonzero discriminant, so `Nat.le_of_dvd` applies.
  have hpos : 0 < (NumberField.discr K).natAbs :=
    Int.natAbs_pos.mpr (NumberField.discr_ne_zero K)
  have hle := Nat.le_of_dvd hpos hdvd
  have hcast : ((NumberField.discr (NumberField.maximalRealSubfield K)).natAbs : ℝ) ^ 2 ≤
      ((NumberField.discr K).natAbs : ℝ) := by exact_mod_cast hle
  have h1 : ∀ z : ℤ, |(z : ℝ)| = (z.natAbs : ℝ) := fun z => by simp
  rw [h1, h1]
  exact hcast

namespace Work.CMRealSubfield.RealSubfield

-- Alias: the same statement under the (doubly nested) namespace in which this file's template
-- declared it, so that either fully qualified name resolves.
/-- For a CM field `K`, `|disc K⁺| ^ 2 ≤ |disc K|` (alias). -/
theorem abs_discr_maximalRealSubfield_sq_le (K : Type*) [Field K] [NumberField K]
    [NumberField.IsCMField K] :
    |(NumberField.discr (NumberField.maximalRealSubfield K) : ℝ)| ^ 2 ≤
      |(NumberField.discr K : ℝ)| :=
  _root_.Work.CMRealSubfield.RealSubfield.abs_discr_maximalRealSubfield_sq_le K

end Work.CMRealSubfield.RealSubfield

end Work.CMRealSubfield.RealSubfield
