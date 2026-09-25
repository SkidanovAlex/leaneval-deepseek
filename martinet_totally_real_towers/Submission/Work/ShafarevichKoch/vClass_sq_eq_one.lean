import Mathlib
import Submission.Work.ShafarevichKoch.Defs
import Submission.Work.ShafarevichKoch.SquareRoot

/-!
# `Work.ShafarevichKoch.vClass_sq_eq_one`

The Kummer two-descent class `vClass F x ∈ Cl(𝓞 F)` of an element `x` of Koch's group `V_∅`
(those `x ∈ Fˣ` whose principal fractional ideal `(x)` is the square of a fractional ideal) is a
`2`-torsion class: `vClass F x ^ 2 = 1`.

Indeed, if `J` is the (unique) square root of `(x)`, then `vClass F x = [J]`, so
`vClass F x ^ 2 = [J] ^ 2 = [J * J] = [(x)] = 1`, the last class being trivial because `(x)` is
principal.  Concretely, `ClassGroup.mk F I = 1` for `I` principal
(`ClassGroup.mk_eq_one_iff` reduces this to principality of the submodule, and the principal
fractional ideal `toPrincipalIdeal (𝓞 F) F y` has underlying module `𝓞 F ∙ y`).

This is the well-definedness/injectivity statement making `vClass` factor through the quotient
`V_∅/Fˣ² → Cl(F)[2]` of the Kummer two-descent exact sequence
`0 → 𝓞_Fˣ/(𝓞_Fˣ)² → V_∅/Fˣ² → Cl(F)[2]`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Classical
open scoped nonZeroDivisors
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ShafarevichKoch

/-- The ideal class of a **principal** fractional ideal is trivial. -/
theorem mk_toPrincipalIdeal_eq_one (F : Type*) [Field F] [NumberField F] (y : Fˣ) :
    ClassGroup.mk F (toPrincipalIdeal (𝓞 F) F y) = 1 := by
  rw [ClassGroup.mk_eq_one_iff, coe_toPrincipalIdeal]
  exact (FractionalIdeal.isPrincipal_iff _).mpr ⟨(y : F), rfl⟩

/-- **The Kummer two-descent class is `2`-torsion**: for `x ∈ V_∅` the class `vClass F x` of a
square root of `(x)` satisfies `vClass F x ^ 2 = 1` in `Cl(𝓞 F)`. -/
theorem vClass_sq_eq_one (F : Type*) [Field F] [NumberField F]
    (x : Work.ShafarevichKoch.VTwo F) : Work.ShafarevichKoch.vClass F x ^ 2 = 1 := by
  simp only [Work.ShafarevichKoch.vClass]
  rw [sq, ← map_mul, vClass_spec, FracIdealOf]
  exact mk_toPrincipalIdeal_eq_one F x.1

end Work.ShafarevichKoch
