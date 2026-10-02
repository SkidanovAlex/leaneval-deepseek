/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FlowerGlue2 team
-/
import Submission.Work.FlowerGlue2.L0
import Submission.Work.FlowerGlue2.isRepellingCoord_ref
import Submission.Work.FlowerGlue2.repNorm_of_flower

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Work.FlowerGlue2.RepNormUncond` — N2 for **every** flower

The headline of the area: the repelling normalisation `Work.PARIMPL2.Lavaurs.RepNorm P fl.Ψ` holds
for an *arbitrary* `ParabolicFlowerFix`, with no hypothesis on the flower at all.  This is the
"FG-d unconditional" of `Submission/Work/NOTES_LEAD_mandelbar_gaps3.md` §1.

The reference repelling coordinate is the transfer form `Ψ₁ w = d.z₁ + P.s c₀ * (-1/V w)` of the
fine repelling conjugacy `V` (`Work.FlowerGlue2.exists_rep_inverse_stolz`): it is a repelling
coordinate, it surjects the Stolz petal `Dst P R₂` of the `c₀`-chart
(`Work.FlowerGlue2.isRepellingCoord_ref`), and it carries `RepNorm`
(`Work.FlowerGlue2.rep_norm_transfer_stolz`).  The flower's own `Ψ` is then compared to it by the
per-point backward-shift uniqueness `Work.FlowerGlue2.rep_unique_backward`, and `RepNorm` transfers
along a far-left equality (`Work.FlowerGlue2.repNorm_comp_add`,
`Work.FlowerGlue2.repNorm_congr_left`).
-/

open Filter Set Metric
open scoped Topology

namespace Work.FlowerGlue2

open Work.PARIMPL (ParNormal Ft gtc)

noncomputable section

variable {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}

/-- **N2, unconditionally, for any flower**: the repelling normalisation of the outgoing window
holds for the flower's `Ψ` with no hypothesis beyond the root-parabolic data and `hτ`. -/
theorem repNorm_any_flower (P : ParNormal d) (hτ : P.h c₀ 0 = 1)
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Ft c₀) (gtc c₀) d.z₁) :
    Work.PARIMPL2.Lavaurs.RepNorm P fl.Ψ := by
  obtain ⟨R₁, Ψ₁, h₁, hsurj, hrn₁⟩ := isRepellingCoord_ref P hτ
  exact repNorm_of_flower P hτ fl h₁ hsurj hrn₁

/-- The same, with `hτ` supplied by `Work.FlowerGlue2.tau_c₀`. -/
theorem repNorm_any_flower' (P : ParNormal d)
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Ft c₀) (gtc c₀) d.z₁) :
    Work.PARIMPL2.Lavaurs.RepNorm P fl.Ψ :=
  repNorm_any_flower P (tau_c₀ P) fl

end

end Work.FlowerGlue2
