/-
# `BridgeSquare/slabWall_exists.lean` — the wall chain of the sheared slab

**Target.**  For every cusp `v` there is a sign `s ∈ {±1}` and a `2`-cycle `c` of the slab space
with `slabChain v 2 c = singT v - s • Ψ_M(planeCycleVec v 0)`.

**Proof.**  The domain calculus of the slab (the affine cube chart, the chart identity
`cSimp_eq_chiRep'` of a slab triangle in a cube, and the translation invariance
`slabChain_translate_sub` of the pushforward under cusp-lattice translations) is in
`BridgeSquare/SlabCore.lean`.  The wall chain and the collar are constructed cusp by cusp in
`BridgeSquare/SlabBuild/` (`Wall{v}.lean`, `Collar{v}.lean`, `Assemble.lean`), and the final
assembly is `Work.BridgeSquare.slabWall_of_wallCollar`:

  `c := slabBot - wallChain{v} - collarChain{v}`,   `s = 1`.
-/
import Submission.Work.BridgeSquare.SlabCore
import Submission.Work.BridgeSquare.SlabBuild.Assemble

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option maxHeartbeats 0

namespace Work.BridgeSquare

theorem slabWall_exists (v : Fin 5) :
    ∃ (s : ℤ) (c : AffC 2),
      (s = 1 ∨ s = -1) ∧ dLC 1 c = 0 ∧
      slabChain v 2 c
        = Work.BridgeSquare.singT v
          - s • ((Work.BridgeSquare.PsiM.f 2) (Work.BridgeSquare.planeCycleVec v 0)) :=
  slabWall_of_wallCollar v (Work.BridgeSquare.SlabBuild.wall_collarB v)

end Work.BridgeSquare
