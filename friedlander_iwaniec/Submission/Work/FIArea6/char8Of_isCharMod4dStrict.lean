/-
# `Submission.Work.FIArea6.char8Of_isCharMod4dStrict`

The character `char8Of ψ` attached (through the duality `Work.FIArea7.chiEquivAddChar` at modulus
`4·2 = 8`) to an additive character of the Gaussian unit group `G8 = (ℤ[i]/8ℤ[i])^*` is a **strict**
character modulo four: it is a character of `(ℤ[i]/4·2ℤ[i])^*` extended by zero off the units
(`Work.FIArea5.S16Hecke.IsCharMod4dStrict 2`).

The whole content of the statement is already in the codomain of the duality:
`Work.FIArea7.chiEquivAddChar` identifies the dual of `G8` with the set of characters modulo `8`
that vanish off the classes of *norm coprime to* `8`; the only thing to be checked is that
"norm coprime to `8`" is the same as "invertible modulo `8`", which is the unit criterion
`Work.FIArea6Hecke.GaussUnit.isUnitMod4d_iff_coprime` (proved from the residue-ring model
`(ZMod (4d))²` with the Gaussian multiplication).

Nothing here depends on the specific additive character `ψ`: the statement holds for the image of
every element of the dual under the duality.
-/
import Mathlib
import Submission.Work.FIArea6.ClassDetectDefs
import Submission.Work.FIArea6Hecke.area5_6_of_S16Core

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Work.FIArea6

open Work.FIArea5.S16Hecke

/-- **The unit criterion at modulus four**, in the direction used below: an element of `ℤ[i]`
which is *not* invertible modulo `4·2 = 8` has norm sharing a factor with `8`.  Equivalently: a
Gaussian integer whose norm is coprime to `8` is invertible modulo `8` (its inverse being
`z̄·|z|²`, since `|z|⁴ ≡ 1 (mod 8)` for odd `|z|²`). -/
lemma not_coprime_eight_of_not_isUnitMod4d (z : GaussianInt) :
    ¬ IsUnitMod4d 2 z → ¬ Nat.Coprime (Work.FIPlan.gnorm z) 8 := by
  intro hz hc
  exact hz ((Work.FIArea6Hecke.GaussUnit.isUnitMod4d_iff_coprime (d := 2) z).mpr hc)

/-- **`char8Of ψ` is a strict character modulo four.**  This is the character-vocabulary half of
the modulus-eight detection of *FI* §16: the additive characters of `(ℤ[i]/8ℤ[i])^*` are exactly
the characters modulo `8` vanishing off the units, since for Gaussian integers "invertible
modulo `8`" and "norm coprime to `8`" agree (`isUnitMod4d_iff_coprime`). -/
theorem char8Of_isCharMod4dStrict (ψ : AddChar (Additive Work.FIArea6.G8) ℂ) :
    Work.FIArea5.S16Hecke.IsCharMod4dStrict 2 (Work.FIArea6.char8Of ψ) := by
  have h := ((Work.FIArea7.chiEquivAddChar 2 (by norm_num)).symm ψ).2
  exact ⟨h.1, fun z hz => h.2 z (not_coprime_eight_of_not_isUnitMod4d z hz)⟩

end Work.FIArea6
