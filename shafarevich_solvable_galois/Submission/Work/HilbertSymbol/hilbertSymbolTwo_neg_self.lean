import Mathlib
import Submission.Work.HilbertSymbol.Basic
import Submission.Work.HilbertSymbol.epsZ_mul
import Submission.Work.HilbertSymbol.omegaZ_mul

namespace Work.HilbertSymbol

/-!
# The `2`-adic Hilbert symbol of `a` and `-a` is trivial

We prove `(a, -a)_2 = 1` for every `a : ℚˣ`, where `(·,·)_2` is the explicit `2`-adic Hilbert
symbol of `Submission.Work.HilbertSymbol.Basic`:

`(a,b)_2 = signOf (ε(u) ε(v) + α ω(v) + β ω(u))`, with `u = unitPart 2 a`, `v = unitPart 2 b`,
`α = v₂(a)`, `β = v₂(b)`, `ε = epsZ` and `ω = omegaZ`.

For `b = -a` we have `-a = a * (-1)`, hence

* `v₂(-a) = v₂(a)`,
* `unitPart 2 (-a) = -unitPart 2 a`  (since `unitPart 2 (-1) = -1`),
* `epsZ (-u) = epsZ u + 1`  (as `-u ≡ 3u ≡ 1 + 2(ε(u)+1) (mod 4)`),
* `omegaZ (-u) = omegaZ u`  (as `ω` only sees `u²`).

So the exponent becomes
`ε (ε + 1) + α ω + α ω = (ε² + ε) + 2αω = 0` in `ZMod 2`
(using `ε² = ε` and `2 = 0`), whence `(a,-a)_2 = signOf 0 = 1`.
-/

/-- The `2`-adic unit part of `-1` is `-1`. -/
private theorem unitPart_two_neg_one : unitPart 2 (-1 : ℚˣ) = -1 := by
  apply Units.ext
  apply PadicInt.ext
  rw [unitPart_coe, unitVal, padicVal_neg, padicVal_one, neg_zero, zpow_zero, one_mul]
  norm_num

/-- `epsZ (-1) = 1`, i.e. `-1 ≡ 3 (mod 4)`. -/
private theorem epsZ_neg_one : epsZ (-1 : ℤ_[2]ˣ) = 1 := by simp [epsZ]

/-- `omegaZ (-1) = 0`, i.e. `-1 ≡ 7 (mod 8)`. -/
private theorem omegaZ_neg_one : omegaZ (-1 : ℤ_[2]ˣ) = 0 := by simp [omegaZ]

/-- `epsZ` of the negative of a unit: `epsZ (-u) = epsZ u + 1`, because `-u ≡ 1 + 2(ε+1) (mod 4)`
when `u ≡ 1 + 2ε (mod 4)`. -/
private theorem epsZ_neg (u : ℤ_[2]ˣ) : epsZ (-u) = epsZ u + 1 := by
  rw [show (-u : ℤ_[2]ˣ) = (-1 : ℤ_[2]ˣ) * u from (neg_one_mul u).symm, epsZ_mul, epsZ_neg_one]
  ring

/-- `omegaZ` of the negative of a unit: `omegaZ (-u) = omegaZ u`, because `omegaZ` only depends
on the square of `u`. -/
private theorem omegaZ_neg (u : ℤ_[2]ˣ) : omegaZ (-u) = omegaZ u := by
  rw [show (-u : ℤ_[2]ˣ) = (-1 : ℤ_[2]ˣ) * u from (neg_one_mul u).symm, omegaZ_mul,
    omegaZ_neg_one, zero_add]

/-- The `ZMod 2`-valued exponent of `hilbertSymbolTwo a (-a)` vanishes identically:
for all `E W A : ZMod 2` we have `signOf (E (E+1) + A W + A W) = 1`
(`E (E+1) = E² + E = E + E = 0` and `A W + A W = 0` in characteristic `2`). -/
private theorem signOf_two_exponent (E W A : ZMod 2) :
    signOf (E * (E + 1) + A * W + A * W) = 1 := by
  revert E W A
  decide

theorem hilbertSymbolTwo_neg_self (a : ℚˣ) : hilbertSymbolTwo a (-a) = 1 := by
  have hu : unitPart 2 (-a) = -unitPart 2 a := by
    rw [show (-a : ℚˣ) = a * (-1) from (mul_neg_one a).symm, unitPart_mul, unitPart_two_neg_one,
      mul_neg_one]
  have hval : padicVal 2 (-a) = padicVal 2 a := padicVal_neg 2 a
  have heps : epsZ (unitPart 2 (-a)) = epsZ (unitPart 2 a) + 1 := by rw [hu, epsZ_neg]
  have homega : omegaZ (unitPart 2 (-a)) = omegaZ (unitPart 2 a) := by rw [hu, omegaZ_neg]
  rw [hilbertSymbolTwo, heps, homega, hval]
  exact signOf_two_exponent _ _ _

end Work.HilbertSymbol
