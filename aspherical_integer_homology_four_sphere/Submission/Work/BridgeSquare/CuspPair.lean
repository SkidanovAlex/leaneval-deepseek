/-
# `BridgeSquare/CuspPair.lean` — the cusp pair `F_k = (H_k τ, H_k π)`

By `Work.BridgeSquare.mvSplit_eq_mvLift`, `Work.BridgeSquare.compatA` and
`Work.BridgeSquare.compatB`, the Mayer–Vietoris map `mvFhat k` of the cover is conjugate (by the
explicit isos of this area) to the **cusp pair**

```
F_k := cuspPair k := biprod.lift (H_k τ) (H_k π) :
        H_k(⊔_v ∂[-1,1]² × T²_v) → H_k(M̄) ⊞ H_k(⊔_v T²_v)
```

with `τ = cuspMap` (the cusp parametrisation) and `π = projMap` (the projection forgetting the
boundary coordinate).  Consequently surjectivity, injectivity and kernels of `mvFhat k` are those of
`F_k`, and the whole bridge reduces to properties of `F_k` — see
`Submission/Work/NOTES_LEAD_aspherical_bridge.md` §2.

This file provides the two maps and the section that makes the second component `P_k = H_k(π)`
surjective: `secMap p₀ : ⊔_v T²_v → ⊔_v ∂[-1,1]² × T²_v`, `⟨v,y⟩ ↦ ⟨v,(p₀,y)⟩`, with
`π ∘ secMap = id`, for any basepoint `p₀` of the square boundary `∂[-1,1]²`.
-/
import Submission.Work.BridgeSquare.Spaces

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open LeanEval.Topology
open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.BridgeSquare

noncomputable section

variable [rt : Work.Space.RTData]

/-! ## §1  The cusp pair -/

/-- **The cusp pair** `F_k = (H_k τ, H_k π)`. -/
def cuspPair (k : ℕ) : LeanEval.Topology.intHomology k (Cop (rt := rt)) ⟶
    (LeanEval.Topology.intHomology k (Mop (rt := rt)) ⊞
      LeanEval.Topology.intHomology k (Top (rt := rt))) :=
  biprod.lift (homMap (cuspMap (rt := rt)) k) (homMap (projMap (rt := rt)) k)

/-- **`mvFhat` is conjugate to the cusp pair**: there are isomorphisms `α`, `β` with
`mvFhat k ≫ β.hom = α.hom ≫ cuspPair k`.  (The `∃` is a `Prop`, so the *choice* of the isos does
not matter; they are built from `mvSplit_eq_mvLift`, `compatA`, `compatB`, `isoInter_eq` and the
explicit isos of `Explicit.lean`.) -/
def ConjCuspPair (k : ℕ) : Prop :=
  ∃ (α : Work.HomologyIso.HI (rt := rt) k ≅ LeanEval.Topology.intHomology k (Cop (rt := rt)))
    (β : Work.HomologyIso.HB (rt := rt) k ≅
      (LeanEval.Topology.intHomology k (Mop (rt := rt)) ⊞
        LeanEval.Topology.intHomology k (Top (rt := rt)))),
    Work.HomologyIso.mvFhat (rt := rt) k ≫ β.hom = α.hom ≫ cuspPair (rt := rt) k

/-! ## §2  The section of the projection -/

/-- **The section** `⊔_v T²_v → ⊔_v ∂[-1,1]² × T²_v` at a basepoint `p₀` of the square boundary:
`⟨v, y⟩ ↦ ⟨v, (p₀, y)⟩`. -/
def secMap (p₀ : Work.Space.Split.BdryPt) : Top (rt := rt) ⟶ Cop (rt := rt) :=
  TopCat.ofHom ⟨fun y => ⟨y.1, (p₀, y.2)⟩, by
    apply continuous_sigma
    intro v
    exact continuous_sigmaMk.comp (continuous_const.prodMk continuous_id)⟩

/-- The section, evaluated. -/
theorem secMap_apply (p₀ : Work.Space.Split.BdryPt) (y : Top (rt := rt)) :
    secMap (rt := rt) p₀ y = ⟨y.1, (p₀, y.2)⟩ := rfl

end

end Work.BridgeSquare
