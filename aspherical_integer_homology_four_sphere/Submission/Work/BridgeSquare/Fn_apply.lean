/-
# `BridgeSquare/Fn_apply.lean` — the section `F_v` in the cusp coordinates of the chart

`Work.BridgeSquare.Fn (rt := Work.RTOwed.rtData) v y = τ⟨v, (p₀, y)⟩` is the `v`-th subtorus map of
`Submission/Work/BridgeSquare/CuspSection.lean` (the composite `secT v ≫ secMap0 ≫ cuspMap`), with
`p₀ = bndOfU 0` the corner `(1,1)` of the square boundary.

This file computes it in the *cusp coordinates of the chart*: a point `y ∈ (ℝ/ℤ)²` of the cusp torus
`T²_v` is the boundary point of the `v`-th filling piece with perimeter parameter `bndOfU 0` and
torus coordinates `y`, so the gluing sends the ceiling point over `cuspX v 0 y` to it
(`Work.RTOwed.glueData_apply` at `u = 0`), and inverting the gluing gives

  `Fn v y = mbarPtC v (cuspX v 0 y)`,

i.e. **the subtorus map of the section is the `u = 0` slice of the ceiling map of the chart**.  This
is the form in which the subtorus `T²_v` sits inside `M̄`, the input of the statement (a)
(`Work.BridgeSquare.SubtorusNull`) — the slice `y ↦ mbarPtC v (cuspX v 0 y)` is an explicit
parameterisation of the `v`-th cusp torus inside the hyperbolic piece.

The only geometric input is `Work.RTOwed.glueData_apply`; the rest is the fact that the canonical
homeomorphism `homeoBdrySubSig` (the glued boundary of the filling pieces in cusp-major form) is the
identity on underlying points.
-/
import Mathlib
import Submission.Work.BridgeSquare.CuspSection

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open LeanEval.Topology
open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.BridgeSquare

noncomputable section

/-! ## §1  The section, evaluated -/

/-- `secT v`, evaluated: the `v`-th component inclusion `T²_v → ⊔_v T²_v`. -/
theorem secT_apply (v : Work.Space.Cusp) (z : Work.RTInstance.Torus) :
    secT (rt := Work.RTOwed.rtData) v z
      = (⟨v, z⟩ : Top (rt := Work.RTOwed.rtData)) := rfl

/-- `secMap0`, evaluated: the section at the corner `p₀ = bndOfU 0`, `⟨v,y⟩ ↦ ⟨v,(p₀,y)⟩`. -/
theorem secMap0_apply (z : Top (rt := Work.RTOwed.rtData)) :
    secMap0 (rt := Work.RTOwed.rtData) z
      = (⟨z.1, (secPt0, z.2)⟩ : Cop (rt := Work.RTOwed.rtData)) := rfl

/-- The section point of the bridge, in the cusp-major form in which `cuspMap` is written: the
`v`-th torus point `y` is sent to `⟨v, (bndOfU 0, y)⟩`. -/
theorem secMap0_secT_apply (v : Work.Space.Cusp) (y : Work.RTInstance.Torus) :
    secMap0 (rt := Work.RTOwed.rtData) (secT (rt := Work.RTOwed.rtData) v y)
      = (⟨v, (secPt0, y)⟩ : Cop (rt := Work.RTOwed.rtData)) := rfl

/-- The canonical homeomorphism `homeoBdrySubSig` (the glued boundary of the filling pieces in
cusp-major form) is the identity on underlying points. -/
theorem homeoBdrySubSig_symm_apply (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (p : Work.Space.Split.BdryPt) (t : a.Torus v) :
    (Work.Space.Split.homeoBdrySubSig a).symm (⟨v, (p, t)⟩ : Work.Space.Split.BdrySig a)
      = ⟨⟨v, (p.1, t)⟩, p.2⟩ := rfl

/-! ## §2  The ceiling point over the section -/

/-- **The section point in the `v`-th cusp chart**: the ceiling point over `cuspX v 0 y` is glued to
the boundary point of the filling piece with perimeter parameter `bndOfU 0` and torus coordinates
`y`, i.e. to the section point `⟨v, (bndOfU 0, y)⟩` of `⊔_v (∂[-1,1]² × T²_v)`.

This is the coordinate formula `Work.RTOwed.glueData_apply` at `u = 0`, written in the cusp-major
form of `cuspMap`. -/
theorem glue_ceiling_eq_secPt0 (v : Work.Space.Cusp) (y : Work.Cusp.E2) :
    (Work.RTOwed.rtData).core.glue
        ⟨Work.RTOwed.mbarPtC v (Work.Cusp.cuspX v 0 y),
          Work.RTOwed.mbarPtC_mem v (Work.Cusp.cuspX v 0 y)⟩
      = (Work.Space.Split.homeoBdrySubSig (Work.RTOwed.rtData).core).symm
          (⟨v, (secPt0, (fun i => ((y i : ℝ) : AddCircle (1 : ℝ))))⟩ :
            Cop (rt := Work.RTOwed.rtData)) := by
  have hglue := Work.RTOwed.glueData_apply v 0 y
    (Work.RTOwed.mbarPtC_mem v (Work.Cusp.cuspX v 0 y))
  exact hglue.trans rfl

/-! ## §3  The subtorus map -/

/-- **The subtorus map `F_v` in the cusp coordinates of the chart.**  The section point of the
`v`-th filling torus at the corner `bndOfU 0` is the ceiling point over the cusp coordinate
`cuspX v 0 y`; equivalently `H_k(Fn v)` is the `u = 0` slice of the ceiling map. -/
theorem Fn_apply (v : Work.Space.Cusp) (y : Work.Cusp.E2) :
    Work.BridgeSquare.Fn (rt := Work.RTOwed.rtData) v
        (fun i => ((y i : ℝ) : AddCircle (1 : ℝ)))
      = Work.RTOwed.mbarPtC v (Work.Cusp.cuspX v 0 y) := by
  set y' : Work.RTInstance.Torus := fun i => ((y i : ℝ) : AddCircle (1 : ℝ))
  -- `Fn v` is the composite, applied to the section point `⟨v, (p₀, y')⟩` of `cuspMap`
  have hsec : Fn (rt := Work.RTOwed.rtData) v y'
      = cuspMap (rt := Work.RTOwed.rtData)
          (⟨v, (secPt0, y')⟩ : Cop (rt := Work.RTOwed.rtData)) := by
    rw [Fn_eq]
    exact congrArg (cuspMap (rt := Work.RTOwed.rtData)) (secMap0_secT_apply v y')
  rw [hsec]
  -- `cuspMap` is the inverse of the gluing, so it remains to invert `glue` on the ceiling point
  have hsymm : (Work.RTOwed.rtData).core.glue.symm
      ((Work.Space.Split.homeoBdrySubSig (Work.RTOwed.rtData).core).symm
        (⟨v, (secPt0, y')⟩ : Cop (rt := Work.RTOwed.rtData)))
      = ⟨Work.RTOwed.mbarPtC v (Work.Cusp.cuspX v 0 y),
          Work.RTOwed.mbarPtC_mem v (Work.Cusp.cuspX v 0 y)⟩ := by
    rw [Homeomorph.symm_apply_eq]
    exact (glue_ceiling_eq_secPt0 v y).symm
  show ((Work.RTOwed.rtData).core.glue.symm
      ((Work.Space.Split.homeoBdrySubSig (Work.RTOwed.rtData).core).symm
        (⟨v, (secPt0, y')⟩ : Cop (rt := Work.RTOwed.rtData)))).val
    = Work.RTOwed.mbarPtC v (Work.Cusp.cuspX v 0 y)
  rw [hsymm]

end

end Work.BridgeSquare
