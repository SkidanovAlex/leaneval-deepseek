/-
# GATE2 / PL — the `FatouCoord` fix of the `c₀`-flower *with* the half-plane saturation

`Work.PARIMPL.exists_flowerFix` returns an **opaque** `FlowerFix`; the saturation proved in
`Submission/Work/GATE2/PL/parabolicFlowerFix_saturating.lean` cannot be read off it.  This module
rebuilds the fix from the *saturating* flower so that a consumer gets both the fix and the
saturation — i.e. `hHalf` of `Work.GATE2.PL.principal_param` as a **theorem**, under the single
numeric condition `Re((2/3)·F'''/F''²) < 1` of §17 of `NOTES.md`.
-/
import Submission.Work.GATE2.PL.parabolicFlowerFix_saturating
import Submission.Work.PARIMPL.flowerFix_of_fatouCoordFix
import Submission.Work.PARIMPL.exists_flowerFix
import Submission.Work.Final.RootArc

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set Metric
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.GATE2.PL

open LeanEval.ComplexAnalysis (Mandelbar Tantibar)

/-- **The `c₀`-flower's `FatouCoord` fix with the half-plane saturation.**  The analogue of
`Work.PARIMPL.exists_flowerFix` in which the flower is the *saturating* one: `FF.Pg = fl.Pg` and
`fl.φa` maps `Pg` onto a right half-plane — which is exactly the `hHalf` hypothesis of
`Work.GATE2.PL.principal_param`. -/
theorem exists_flowerFix_saturating {c₀ : ℂ} (d : Work.EL.RootParabolic c₀)
    (ha1 : ((2 / 3 : ℝ) * iteratedDeriv 3 (Work.PARIMPL.Ft c₀) d.z₁
      / (iteratedDeriv 2 (Work.PARIMPL.Ft c₀) d.z₁) ^ 2).re < 1) :
    ∃ fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.PARIMPL.Ft c₀) (Work.PARIMPL.gtc c₀) d.z₁,
      ∃ FF : Work.PARIMPL.FlowerFix d (Work.PARIMPL.Ft c₀) (Work.PARIMPL.gtc c₀) d.z₁ fl.Pa fl.φa,
        FF.Pg = fl.Pg ∧ ∃ X : ℝ, ∀ w : ℂ, X < w.re → ∃ z ∈ FF.Pg, fl.φa z = w := by
  obtain ⟨fl, -, -, hX⟩ :=
    parabolicFlowerFix_saturating (Work.Final.differentiable_F c₀)
      (fun z => (Work.Final.differentiable_star_Tantibar_five c₀).differentiableAt)
      (Work.Final.Tantibar_five_comp_self c₀) (Work.Final.Tantibar_five_fix d.per_half)
      d.mult d.simple d.per_half one_pos ha1
  let FF : Work.PARIMPL.FlowerFix d (Work.PARIMPL.Ft c₀) (Work.PARIMPL.gtc c₀) d.z₁ fl.Pa fl.φa :=
    { shift := fl.φa_shift
      Pg := fl.Pg
      Pg_sub := fl.Pg_sub
      isOpen_Pg := fl.isOpen_Pg
      mapsTo_F_Pg := fun _ hz => fl.mapsTo_F_Pg hz
      mapsTo_G_Pg := fun _ hz => fl.mapsTo_g_Pg hz }
  exact ⟨fl, FF, rfl, hX⟩

end Work.GATE2.PL
