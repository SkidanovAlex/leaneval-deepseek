/-
# The concrete gluing `τ_v` of `M̂` and its coordinate formula (item 4)

`Work.RTOwed.glueHomeoOf` turns any explicit boundary homeomorphism
`Ψ v : ℝ³/Λ_v ≃ₜ ∂[-1,1]² × (ℝ/ℤ)²` into the gluing `Work.RTInstance.GlueHomeo`.  This file
instantiates it at the boundary homeomorphism of the area
(`Work.RTOwed.cuspTorus_homeo_boundary_explicit`, whose coordinate formula is given by the cusp
coordinates `(u, y) = (outerU v x, outerY v x)`), producing the concrete gluing

  `Work.RTOwed.glueData : Work.RTInstance.GlueHomeo`

together with its coordinate formula `Work.RTOwed.glueData_apply`: **the ceiling point over the cusp
coordinate `cuspX v u y` is glued to the filling boundary point with perimeter parameter `bndOfU u`
and torus coordinates `y`** — the field `Work.Cusp.CuspGlueData.glue_eq`.
-/
import Mathlib
import Submission.Work.RTOwed.cuspGlue
import Submission.Work.RTOwed.cuspTorus_homeo_boundary_explicit
import Submission.Work.Cusp.outerU_cuspX

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function

namespace Work.RTOwed

open Work.RTInstance

/-- The boundary homeomorphism `ℝ³/Λ_v ≃ₜ ∂[-1,1]² × (ℝ/ℤ)²` of the cusp torus, in cusp
coordinates. -/
noncomputable def Psi (v : Work.Space.Cusp) :
    Work.Cusp.CuspTorus v ≃ₜ
      {p : Work.RTInstance.SquarePt × Work.RTInstance.Torus // Work.Space.sqNorm p.1 = 1} :=
  Classical.choose (cuspTorus_homeo_boundary_explicit v)

/-- **The coordinate formula of `Psi`.** -/
theorem Psi_apply (v : Work.Space.Cusp) (x : CuspE3) :
    (Psi v (Quotient.mk'' x)).1 =
      (⟨Work.Cusp.bndOfU (Work.Cusp.outerU v x),
          Work.Cusp.bndOfU_mem (Work.Cusp.outerU v x)⟩,
        fun i => ((Work.Cusp.outerY v x i : ℝ) : AddCircle (1 : ℝ))) :=
  congrArg Subtype.val (Classical.choose_spec (cuspTorus_homeo_boundary_explicit v) x)

/-- **The concrete gluing `τ_v` of `M̂`** (item 4 of the contract). -/
noncomputable def glueData : Work.RTInstance.GlueHomeo :=
  ⟨glueHomeoOf Psi⟩

/-- **The coordinate formula of the gluing**: the ceiling point over the cusp coordinate
`cuspX v u y` is glued to the boundary point with perimeter parameter `bndOfU u` and torus
coordinates `y`.  This is the field `CuspGlueData.glue_eq` of the datum of the `v`-th cusp. -/
theorem glueData_apply (v : Work.Space.Cusp) (u : ℝ) (y : Work.Cusp.E2)
    (h : mbarPtC v (Work.Cusp.cuspX v u y) ∈ Work.FoldInst.Tset) :
    glueData.glue ⟨mbarPtC v (Work.Cusp.cuspX v u y), h⟩ =
      ⟨⟨v, (⟨Work.Cusp.bndOfU u, Work.Cusp.bndOfU_mem u⟩,
          fun i => ((y i : ℝ) : AddCircle (1 : ℝ)))⟩, by
        simp only [Work.Space.FillingBdry, Set.mem_ofPred_eq, Work.Space.sqNorm]
        exact Work.Cusp.nrm_bndOfU u⟩ := by
  refine Subtype.ext ?_
  change (Subtype.val ((glueHomeoOf Psi) ⟨mbarPtC v (Work.Cusp.cuspX v u y), h⟩) :
      Σ _ : Work.Space.Cusp, Work.RTInstance.SquarePt × Work.RTInstance.Torus)
    = (⟨v, (⟨Work.Cusp.bndOfU u, Work.Cusp.bndOfU_mem u⟩,
        fun i => ((y i : ℝ) : AddCircle (1 : ℝ)))⟩ : Σ _ : Work.Space.Cusp,
          Work.RTInstance.SquarePt × Work.RTInstance.Torus)
  rw [congrArg Subtype.val (glueHomeoOf_apply Psi v (Work.Cusp.cuspX v u y) h)]
  show (⟨v, (Psi v (Quotient.mk'' (Work.Cusp.cuspX v u y))).1⟩ : Σ _ : Work.Space.Cusp,
      Work.RTInstance.SquarePt × Work.RTInstance.Torus) = _
  rw [Psi_apply]
  refine Sigma.ext rfl (heq_of_eq (Prod.ext ?_ ?_))
  · exact Subtype.ext (congrArg Work.Cusp.bndOfU (Work.Cusp.outerU_cuspX v u y))
  · funext i
    exact congrArg (fun t : Work.Cusp.E2 => ((t i : ℝ) : AddCircle (1 : ℝ)))
      (Work.Cusp.outerY_cuspX v u y)

end Work.RTOwed
