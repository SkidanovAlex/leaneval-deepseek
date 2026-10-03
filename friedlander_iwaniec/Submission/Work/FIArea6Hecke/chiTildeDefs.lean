/-
# `Submission.Work.FIArea6Hecke.chiTildeDefs`

The auxiliary character `χ̃(z) = χ(z)/χ(z̄)` of the Hecke `L`-function of weight `2m` in *FI* §16.

For a character `χ` of `(ℤ[i]/4dℤ[i])^*` extended by zero off the units (`IsCharMod4dStrict d χ`),
the Größencharacter whose Hecke `L`-function the assembly of *FI* (16.17) consumes is
`ψ(z) = χ̃(z)·(z/|z|)^{2m}` with `χ̃(z) = χ(z)/χ(z̄)`; on the ideals `(z)` of `ℚ(i)` the
conjugation `z ↦ z̄` inverts the class, so `χ̃` is the character `χ·χ̄`.

This module only fixes the `Def`s (so that several files can state lemmas about `chiTilde` without
importing each other); the basic API (`chiTilde_one`, `chiTilde_mul`, `chiTilde_norm_le_one`) is
proved in the sibling modules.
-/
import Mathlib
import Submission.Work.FIArea5.S16Hecke.ThetaDefs

set_option autoImplicit false

namespace Work.FIArea6Hecke

open Work.FIArea5.S16Hecke

noncomputable section

/-- `χ̃(z) = χ(z)/χ(z̄)`.  Since `χ` vanishes off the units of `ℤ[i]/4dℤ[i]` and `z` is a unit
modulo `4d` exactly when `z̄` is, the quotient is `0` off the units and of modulus `1` on them; in
particular `z ↦ χ̃(z)` is again a character of modulus `4d` bounded by `1`. -/
def chiTilde (chi : GaussianInt → ℂ) : GaussianInt → ℂ := fun z => chi z / chi (star z)

@[simp] lemma chiTilde_apply (chi : GaussianInt → ℂ) (z : GaussianInt) :
    chiTilde chi z = chi z / chi (star z) := rfl

end

end Work.FIArea6Hecke
