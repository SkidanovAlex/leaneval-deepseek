import Mathlib
import Submission.Work.ShafarevichKoch.SquareRoot

/-!
# `Work.ShafarevichKoch.FracIdealOfUnit` -- units generate the unit ideal

The Kummer two-descent `vClass` (`Defs.lean`) has kernel the image of `𝓞_Fˣ → Fˣ`; the
computation rests on the elementary fact that a *unit* of `𝓞 F` generates the unit fractional
ideal, proved here as `fracIdealOf_unitEmbed`.
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

/-- **A unit of `𝓞 F` generates the unit fractional ideal.** -/
theorem fracIdealOf_unitEmbed (F : Type*) [Field F] [NumberField F] (u : RingUnit F) :
    FracIdealOf F (unitEmbed F u) = 1 := by
  apply Units.ext
  rw [FracIdealOf, coe_toPrincipalIdeal, unitEmbed_coe, Units.val_one,
    ← FractionalIdeal.coeIdeal_span_singleton (S := nonZeroDivisors (𝓞 F)) (P := F)
      (x := (u : 𝓞 F))]
  rw [show Ideal.span {(u : 𝓞 F)} = ⊤ from Ideal.span_singleton_eq_top.mpr u.isUnit,
    FractionalIdeal.coeIdeal_top]

end Work.ShafarevichKoch
