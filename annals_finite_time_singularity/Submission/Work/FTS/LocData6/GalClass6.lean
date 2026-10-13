/-
# `Work.FTS.LocData6.GalClass6` — the localised datum in the class `GalClass` (order `6`)

`Work.FTS.Nonlin.GalClass α g` is the datum class of the strong-solution route
(`Submission/Work/FTS/StrongGlobal/Defs.lean` §2): it bundles `RegQ α 6 g`, the vanishing of `g`
on the two angular boundaries, the vanishing of `g` and `∂_z g` on the axis, the decay
`DecayAll 6 g` and the `L₁₂`-orthogonality at `z = 0`.  This module assembles the class for the
localised datum `locG α L β (hLoc α)` from its parts: the regularity `RegQ α 6` (delivered at
order `6` in `LocData6.LocG6Aux`), the decay `DecayAll 6` (delivered by `LocData6.decayAll_locG6`)
and the `L₁₂`-relation (`LocData.L12_locG`), with the two vanishing clauses taken from the
delivered `LocData.vanishTheta_locG` and `LocData.zero_slice_locG`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.LocData6.Defs
import Submission.Work.FTS.LocData.vanishTheta_locG
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.LocData.L12_locG

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData6

set_option autoImplicit false

/-- **The localised datum lies in `GalClass α`**, from its `RegQ α 6`-regularity, its decay
`DecayAll 6` and the vanishing of `L₁₂(·)(0)`. -/
theorem galClass_locG6_of (α L β : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hL : 1 ≤ L)
    (hreg : Work.FTS.Nonlin.RegQ α 6 (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)))
    (hdec : Work.Spaces.DecayAll 6 (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)))
    (hl12 : Work.Construction.L12 (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)) 0 = 0) :
    Work.FTS.Nonlin.GalClass α (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)) := by
  have hv : Work.Spaces.VanishTheta (Work.FTS.LocData.hLoc α) :=
    (Work.FTS.LocData.hLoc_vanishing α hα).1
  refine ⟨hreg, ?_, ?_, hdec, hl12⟩
  · exact Work.FTS.LocData.vanishTheta_locG α L β hα hα1
      (fun z => ⟨hv.1 z, hv.2 z⟩)
  · exact Work.FTS.LocData.zero_slice_locG α L β hα hα1
      (fun z θ hz => Work.FTS.LocData.hLoc_eq_zero_of_le α hz θ) hL

end Work.FTS.LocData6
