/-
Copyright: subproject `Submission/Work/PARIMPL/` of `mandelbar_not_path_connected`.

# `Work.PARIMPL.flowerFix_of_fatouCoordFix`

The repaired Leau–Fatou flower `Work.FatouCoordFix.ParabolicFlowerFix F g z₀` of the second
return map `F = Ft c₀ = (T_{c₀})^10` and its antiholomorphic square root `g = gtc c₀ = (T_{c₀})^5`
*is* a `Work.PARIMPL.FlowerFix` for the root-arc data `d`: the residual note
(`NOTES_LEAD_mandelbar_residuals.md` §3.1) asks the flower to provide the Abel equation
`φa ∘ F = φa + 1` on the wide petal `Pa` together with a `g`-invariant open sub-petal `Pg`, and
exactly those two items are the content of the `FatouCoordFix` fields `φa_shift`, `Pg`, `Pg_sub`,
`isOpen_Pg`, `mapsTo_F_Pg`, `mapsTo_g_Pg`.  The remaining `FlowerFix` fields are therefore filled
by `fl` verbatim; nothing but the structure projections is used, so the statement is a genuine
*interface conversion* and carries no mathematical content beyond the one already packaged in
`ParabolicFlowerFix` (whose `φa_shift` is derived there by the identity-theorem engine
`Work.FatouCoordFix.φa_shift_of_halfPetal`).

## Main result

* `Work.PARIMPL.flowerFix_of_fatouCoordFix` — the conversion.
-/
import Mathlib
import Submission.Work.PARIMPL.Match
import Submission.Work.FatouCoordFix.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

namespace Work.PARIMPL

/-- A `ParabolicFlowerFix` of the return map `F` and its root `g` on the petal `Pa` with coordinate
`φa` yields a `FlowerFix`: the Abel equation is `φa_shift`, and the invariant `g`-petal `Pg` is
transported unchanged.  The hypotheses `Pg ⊆ Pa`, openness and the two invariance statements are
the corresponding fields of `ParabolicFlowerFix`. -/
theorem flowerFix_of_fatouCoordFix {c₀ : ℂ} (d : Work.EL.RootParabolic c₀)
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.PARIMPL.Ft c₀) (Work.PARIMPL.gtc c₀) d.z₁) :
    Nonempty (Work.PARIMPL.FlowerFix d (Work.PARIMPL.Ft c₀) (Work.PARIMPL.gtc c₀) d.z₁ fl.Pa
      fl.φa) :=
  ⟨{ shift := fl.φa_shift
     Pg := fl.Pg
     Pg_sub := fl.Pg_sub
     isOpen_Pg := fl.isOpen_Pg
     mapsTo_F_Pg := fun _ hz => fl.mapsTo_F_Pg hz
     mapsTo_G_Pg := fun _ hz => fl.mapsTo_g_Pg hz }⟩

end Work.PARIMPL
