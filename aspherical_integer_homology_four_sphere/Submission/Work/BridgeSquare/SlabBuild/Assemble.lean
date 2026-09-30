/-
# `BridgeSquare/SlabBuild/Assemble.lean` — the collar statement `wall_collar`, cusp by cusp

For each cusp `v` we have the wall chain `wallChain{v}` (whose `slabChain`-image is
`Ψ_M(planeCycleVec v 0)`, `Wall{v}.lean`) and the collar `collarChain{v}` (a sum of cusp-lattice
translate differences, hence in the kernel of `slabChain v 2`, and with boundary
`dLC 1 wallChain{v} - dLC 1 slabBot`, `Collar{v}.lean`).  This module assembles them into the
`∃ s W K` statement consumed by `Work.BridgeSquare.slabWall_of_wallCollar`.
-/
import Mathlib
import Submission.Work.BridgeSquare.SlabCore
import Submission.Work.BridgeSquare.SlabBuild.Wall0
import Submission.Work.BridgeSquare.SlabBuild.Wall1
import Submission.Work.BridgeSquare.SlabBuild.Wall2
import Submission.Work.BridgeSquare.SlabBuild.Wall3
import Submission.Work.BridgeSquare.SlabBuild.Wall4
import Submission.Work.BridgeSquare.SlabBuild.Collar0
import Submission.Work.BridgeSquare.SlabBuild.Collar1
import Submission.Work.BridgeSquare.SlabBuild.Collar2
import Submission.Work.BridgeSquare.SlabBuild.Collar3
import Submission.Work.BridgeSquare.SlabBuild.Collar4

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 0
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Work.BridgeSquare.SlabBuild

open Convexity
open Work.Subdivision
open Work.MbarHomology
open Work.BridgeSquare.WallCollar

noncomputable section


set_option maxHeartbeats 200000 in
theorem wall_collarB (v : Fin 5) :
    ∃ (s : ℤ) (W K : AffC 2), (s = 1 ∨ s = -1) ∧
      slabChain v 2 W = s • ((PsiM.f 2) (planeCycleVec v 0)) ∧
      slabChain v 2 K = 0 ∧
      dLC 1 K = s • dLC 1 W - dLC 1 slabBot := by
  fin_cases v
  · exact ⟨1, wallChain0, collarChain0, Or.inl rfl, by simpa using wall_slab0,
      collar_slab0, by simpa using dLC_collar0⟩
  · exact ⟨1, wallChain1, collarChain1, Or.inl rfl, by simpa using wall_slab1,
      collar_slab1, by simpa using dLC_collar1⟩
  · exact ⟨1, wallChain2, collarChain2, Or.inl rfl, by simpa using wall_slab2,
      collar_slab2, by simpa using dLC_collar2⟩
  · exact ⟨1, wallChain3, collarChain3, Or.inl rfl, by simpa using wall_slab3,
      collar_slab3, by simpa using dLC_collar3⟩
  · exact ⟨1, wallChain4, collarChain4, Or.inl rfl, by simpa using wall_slab4,
      collar_slab4, by simpa using dLC_collar4⟩

end

end Work.BridgeSquare.SlabBuild
