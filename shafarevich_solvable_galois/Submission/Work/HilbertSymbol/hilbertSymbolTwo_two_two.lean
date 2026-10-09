import Mathlib
import Submission.Work.HilbertSymbol.Places
import Submission.Work.HilbertSymbol.Symbol
import Submission.Work.HilbertSymbol.hilbertSymbolOdd_primeUnit_self
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

/-!
# The Hilbert symbol `(2, 2)_2 = 1`

At the place `2`, both arguments are the prime `2`, whose `2`-adic valuation is `1` and whose
`2`-adic unit part is `1`.  The explicit formula for `(·,·)_2` therefore reduces to
`signOf (ε(1)ε(1) + 1·ω(1) + 1·ω(1))`, and both `ε(1)` and `ω(1)` vanish, giving the value `1`.
-/

/-- `ε(1) = 0`, i.e. the unit `1 ∈ ℤ_[2]ˣ` is `1 + 2·0` modulo `4`. -/
lemma epsZ_one : epsZ (1 : ℤ_[2]ˣ) = 0 := by
  simp only [epsZ, Units.val_one, map_one]
  rw [ZMod.val_one'']
  · norm_num
  · norm_num

/-- `ω(1) = 0`, i.e. the unit `1 ∈ ℤ_[2]ˣ` is `±1` modulo `8`. -/
lemma omegaZ_one : omegaZ (1 : ℤ_[2]ˣ) = 0 := by
  simp only [omegaZ, Units.val_one, map_one]
  rw [ZMod.val_one'']
  · norm_num
  · norm_num

theorem hilbertSymbolTwo_two_two : hilbertSymbolTwo (primeUnit 2) (primeUnit 2) = 1 := by
  simp only [hilbertSymbolTwo, padicVal_primeUnit 2, unitPart_primeUnit 2, epsZ_one, omegaZ_one]
  norm_num [signOf]

end Work.HilbertSymbol
