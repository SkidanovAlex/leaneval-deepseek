import Mathlib
import Submission.Work.HilbertSymbol.Places
import Submission.Work.HilbertSymbol.Symbol
import Submission.Work.HilbertSymbol.hilbertSymbolOdd_primeUnit_self

namespace Work.HilbertSymbol

/-!
# The Hilbert symbol `(-1, 2)_2 = 1`

We evaluate the explicit `2`-adic Hilbert symbol of `Submission.Work.HilbertSymbol.Basic` at
`a = -1` and `b = 2`:

`(a,b)_2 = signOf (ε(u) ε(v) + α ω(v) + β ω(u))` with `u = unitPart 2 a`, `v = unitPart 2 b`,
`α = v₂(a)`, `β = v₂(b)`, `ε = epsZ`, `ω = omegaZ`.

Here `a = -1` has valuation `0` and unit part `-1` (with `ε(-1) = 1`, `ω(-1) = 0`), while
`b = 2` has valuation `1` and unit part `1` (with `ε(1) = ω(1) = 0`).  The exponent is therefore
`1·0 + 0·0 + 1·0 = 0`, so `(-1, 2)_2 = signOf 0 = 1`.
-/

/-- `ε(1) = 0`, i.e. the unit `1 ∈ ℤ_[2]ˣ` is `1 + 2·0` modulo `4`. -/
private theorem epsZ_one_local : epsZ (1 : ℤ_[2]ˣ) = 0 := by
  simp only [epsZ, Units.val_one, map_one]
  rw [show (1 : ZMod (2 ^ 2)) = ((1 : ℕ) : ZMod (2 ^ 2)) by norm_num, ZMod.val_natCast]
  norm_num

/-- `ω(1) = 0`, i.e. the unit `1 ∈ ℤ_[2]ˣ` is `±1` modulo `8`. -/
private theorem omegaZ_one_local : omegaZ (1 : ℤ_[2]ˣ) = 0 := by
  simp only [omegaZ, Units.val_one, map_one]
  rw [show (1 : ZMod (2 ^ 3)) = ((1 : ℕ) : ZMod (2 ^ 3)) by norm_num, ZMod.val_natCast]
  norm_num

/-- The `2`-adic unit part of `-1` is `-1`. -/
private theorem unitPart_two_neg_one_local : unitPart 2 (-1 : ℚˣ) = -1 := by
  apply Units.ext
  apply PadicInt.ext
  rw [unitPart_coe, unitVal, padicVal_neg, padicVal_one, neg_zero, zpow_zero, one_mul]
  norm_num

theorem hilbertSymbolTwo_neg_one_two :
    hilbertSymbolTwo (-1 : ℚˣ) (primeUnit 2) = 1 := by
  have hval : padicVal 2 (-1 : ℚˣ) = 0 := by
    simpa using padicVal_neg 2 (1 : ℚˣ)
  have heps : epsZ (-1 : ℤ_[2]ˣ) = 1 := by simp [epsZ]
  have homega : omegaZ (-1 : ℤ_[2]ˣ) = 0 := by simp [omegaZ]
  rw [hilbertSymbolTwo, unitPart_two_neg_one_local, unitPart_primeUnit 2, hval,
    padicVal_primeUnit 2, heps, epsZ_one_local, homega, omegaZ_one_local]
  norm_num [signOf]

end Work.HilbertSymbol
