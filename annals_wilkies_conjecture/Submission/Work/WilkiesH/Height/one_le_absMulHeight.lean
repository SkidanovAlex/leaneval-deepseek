import Mathlib
import Submission.Work.WilkiesH.Defs

open Classical IntermediateField NumberField

set_option linter.style.haveILetI false

namespace Work.WilkiesH.Height

/-- The absolute multiplicative height of a real number is at least `1`.  For a non-algebraic
number `absMulHeight₁` is defined to be `1`; for an algebraic number it is the
`[ℚ⟮x⟯ : ℚ]`-th root of `mulHeight₁` of the generator, and `mulHeight₁` is always `≥ 1`, so a
nonnegative root of it is again `≥ 1`. -/
theorem one_le_absMulHeight (x : ℝ) : 1 ≤ NumberField.absMulHeight₁ x := by
  rw [NumberField.absMulHeight₁]
  split_ifs with hx
  · haveI : FiniteDimensional ℚ ℚ⟮x⟯ := adjoin.finiteDimensional hx
    haveI : NumberField ℚ⟮x⟯ := {}
    exact Real.one_le_rpow (Height.one_le_mulHeight₁ _)
      (inv_nonneg.mpr (Nat.cast_nonneg _))
  · exact le_refl 1

end Work.WilkiesH.Height
