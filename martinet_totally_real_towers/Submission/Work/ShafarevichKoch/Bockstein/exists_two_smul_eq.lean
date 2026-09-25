import Mathlib
import Submission.Work.ShafarevichKoch.RatCoeff

/-!
# `ℚ/ℤ` is 2-divisible

`Work.ShafarevichKoch.QZ` is the coefficient group `ℚ/ℤ` of the Bockstein machinery.  As a
quotient of the divisible group `ℚ`, it is divisible, so in particular the map `x ↦ 2 • x` is
surjective.
-/

namespace Work.ShafarevichKoch.Bockstein

set_option linter.style.haveILetI false

/-- **Every element of `ℚ/ℤ` is twice an element of `ℚ/ℤ`** (divisibility of the quotient of the
divisible group `ℚ` by `ℤ`). -/
theorem exists_two_smul_eq (y : Work.ShafarevichKoch.QZ) :
    ∃ x : Work.ShafarevichKoch.QZ, (2 : ℕ) • x = y := by
  -- `ℚ` is `ℕ`-divisible, hence so is its quotient `ℚ/ℤ`.
  letI hQ : DivisibleBy ℚ ℕ := AddGroup.divisibleByNatOfDivisibleByInt ℚ
  letI hQZ : DivisibleBy Work.ShafarevichKoch.QZ ℕ :=
    QuotientAddGroup.divisibleBy (AddSubgroup.zmultiples (1 : ℚ))
  exact DivisibleBy.surjective_smul (A := Work.ShafarevichKoch.QZ) (α := ℕ) (by norm_num) y

end Work.ShafarevichKoch.Bockstein
