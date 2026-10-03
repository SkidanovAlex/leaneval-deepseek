/-
# Twist of a character by a character of `U/K₄` (session work, H1166)

For the `unitSum χ m = 0` case of `thetaHol_law_primitive` we twist `χ` by a character `ν` of the
unit group `(ℤ[i]/4d)∗` which is **trivial on the primary coset** `1 + (1+i)³ℤ[i]`.  Such a twist
does not change the primary-coset theta series (`thetaHol`), but it *does* change the "unit sum"
`unitSum χ m = Σ_{u ∈ μ₄} χ(u)u^m`, and exactly one of the four twists has a non-zero unit sum.

`primaryUnit z` is the unit `u ∈ μ₄ = {1,-1,i,-i}` congruent to an odd `z` modulo `(1+i)³`
(there is exactly one); it is `0` on the even elements.  `twistExp χ m` is the exponent `j` with
`χ(i)·i^m = i^j`; `twistChar χ m` is `z ↦ (primaryUnit z)^{-j}`.  Then

  `unitSum (twistChar χ m) m = Σ_k (χ(i)i^m i^{-j})^k = Σ_k 1 = 4 ≠ 0`.
-/
import Mathlib
import Submission.Work.FIArea5.S16Hecke.ThetaDefs

set_option autoImplicit false

namespace Work.FIArea5.S16Hecke

open Work.FIPlan

noncomputable section

attribute [local instance] Classical.propDecidable

/-- `(1+i)³ = -2 + 2i`. -/
def c3 : GaussianInt := (1 + (⟨0,1⟩ : GaussianInt)) ^ 3

/-- **The unit `u ∈ μ₄` congruent to `z` modulo `(1+i)³`** (for odd `z`), and `0` for even `z`.
There is exactly one such unit because the four units are pairwise incongruent modulo `(1+i)³`
(`(1+i)³ = -2+2i` has norm `8 > 4`). -/
def primaryUnit (z : GaussianInt) : GaussianInt :=
  if c3 ∣ z - 1 then 1
  else if c3 ∣ z + 1 then -1
  else if c3 ∣ z - (⟨0,1⟩ : GaussianInt) then (⟨0,1⟩ : GaussianInt)
  else if c3 ∣ z + (⟨0,1⟩ : GaussianInt) then -(⟨0,1⟩ : GaussianInt)
  else 0

/-- The exponent `j ∈ {0,1,2,3}` with `χ(i)·i^m = i^j` (with the convention `j = m + 3` when
`χ(i) = -i`, which is the remaining possibility when `χ(i) ∈ μ₄`). -/
def twistExp (chi : GaussianInt → ℂ) (m : ℕ) : ℕ :=
  if chi ⟨0,1⟩ = 1 then m % 4
  else if chi ⟨0,1⟩ = Complex.I then (m + 1) % 4
  else if chi ⟨0,1⟩ = -1 then (m + 2) % 4
  else (m + 3) % 4

/-- The twisting character `ν(z) = (primaryUnit z)^{-j}`, `j = twistExp χ m`; zero on the even
elements.  It is a character of `(ℤ[i]/4d)∗` which is trivial on the primary coset `1+(1+i)³ℤ[i]`
(where `primaryUnit = 1`). -/
def twistChar (chi : GaussianInt → ℂ) (m : ℕ) : GaussianInt → ℂ :=
  fun z => if isOddG z then (((primaryUnit z).toComplex) ^ (-(twistExp chi m : ℤ))) else 0

/-- **The twisted character** `χ·ν`.  Since `χ` vanishes off the units, so does `χ·ν`, and the
twist is trivial on the primary coset, so `thetaHol` and its conjugate are unaffected. -/
def twist (chi : GaussianInt → ℂ) (m : ℕ) : GaussianInt → ℂ :=
  fun z => chi z * twistChar chi m z

end

end Work.FIArea5.S16Hecke
