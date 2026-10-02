/-
Copyright: subproject `Submission/Work/PARIMPL2/` of `mandelbar_not_path_connected`.

# `Work.PARIMPL2.Lavaurs.MandelWireExport` — the single analytic export for an arbitrary flower

The wiring `Submission/Work/NOTES_LEAD_mandelbar_wire.md` §A.3 calls this as

```lean
hLav : ∀ d P fl, LavaursPhase d P fl.Pa fl.φa fl.Ψ (nEnter d fl.toParabolicFlower)
```

with `fl` an **arbitrary** `ParabolicFlowerFix` (SatFree's wide, saturating flower included).  The
assembly is

* `lockstep_complex P fl A hrn hdeep (nEnter d fl) hentry`  (this area, L4), then
* `lavaursPhase_of_lockstep` (this area, L4: the phase is real, by `phase_im_zero`),

with the sibling inputs produced by FlowerGlue2:

* `A := Work.FlowerGlue2.exists_attrCompare P hτ fl` (N1, `AttrNorm.lean`);
* `hrn := Work.FlowerGlue2.repNorm_any_flower P hτ fl` (N2, *unconditional for every flower*,
  `RepNormUncond.lean` — in this area's vocabulary `Work.PARIMPL2.Lavaurs.RepNorm`);
* `hentry := Work.PARIMPL.nEnter_spec d fl.toParabolicFlower`;
* `hdeep` is the **hypothesis** of this file: it is copied verbatim from the conclusion of
  `Work.FlowerGlue2.box_deep_of_transient_bound P A hLB X₁ W H`, that area's uniform transient
  bound `hLB` (see `NOTES_LEAD_mandelbar_wire.md` §A.4 R1 for the `|Im φa| ≤ H`-restricted form
  that a *wide* petal requires).

*(Status: **complete and axiom-clean**.  `lockstep_complex`, `transit_exit_direct`, `hLB_H`,
`box_deep_H` and this export all build with `#print axioms = [propext, Classical.choice,
Quot.sound]`.)*-/
import Submission.Work.PARIMPL2.Lavaurs.Defs
import Submission.Work.PARIMPL2.Lavaurs.L0_symmetry
import Submission.Work.PARIMPL2.Lavaurs.lockstep_complex
import Submission.Work.PARIMPL2.Lavaurs.lavaursPhase
import Submission.Work.PARIMPL2.Lavaurs.hLB_H
import Submission.Work.PARIMPL2.Lavaurs.box_deep_H
import Submission.Work.FlowerGlue2.AttrNorm
import Submission.Work.FlowerGlue2.RepNormUncond

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL2.Lavaurs

open Work.PARIMPL (ParNormal entryPt Ft gtc)

variable {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}

/-- **The single analytic export of the implosion endgame, for an arbitrary flower** — the
`hLav` that `Work.MandelWire` feeds to
`mandelbar_not_path_connected_of_lav_sat`.  Fully unconditional: the attracting comparison comes
from `Work.FlowerGlue2.exists_attrCompare` (N1), the repelling normalisation from
`Work.FlowerGlue2.repNorm_any_flower` (N2, unconditional for every flower), and the deepening
`hdeep` from `Work.PARIMPL2.Lavaurs.box_deep_H` with the restricted transient bound
`Work.PARIMPL2.Lavaurs.hLB_H` at each height `H`; `hτ` is `Work.PARIMPL2.Lavaurs.L0_symmetry`'s
`τ_{c₀} = 1`, and the entry point is `Work.PARIMPL.nEnter_spec`. -/
theorem lavaursPhase {c₀ : ℂ} (d : Work.EL.RootParabolic c₀) (P : ParNormal d)
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Ft c₀) (gtc c₀) d.z₁) :
    LavaursPhase d P fl.Pa fl.φa fl.Ψ (Work.PARIMPL.nEnter d fl.toParabolicFlower) := by
  have hτ : P.h c₀ 0 = 1 := (L0_symmetry d P).2.2.1
  obtain ⟨A⟩ := Work.FlowerGlue2.exists_attrCompare P hτ fl
  refine lavaursPhase_of_lockstep P fl (Work.PARIMPL.nEnter d fl.toParabolicFlower)
    (lockstep_complex P fl A (Work.FlowerGlue2.repNorm_any_flower P hτ fl) ?_
      (Work.PARIMPL.nEnter d fl.toParabolicFlower)
      (Work.PARIMPL.nEnter_spec d fl.toParabolicFlower))
  intro X₁ W H
  exact ⟨A.sa, fun X => box_deep_H P fl A X₁ W H (hLB_H P fl A H) X⟩

end Work.PARIMPL2.Lavaurs

end
