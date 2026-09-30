/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area JacFinal (the final assembly: `Work.DescentGeom.Input` from the areas)
-/
import Submission.Work.JacFinal.Basic
import Submission.Work.JacFinal.GalAct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Area `JacFinal` — assembling `Work.DescentGeom.Input`

From the outputs of the areas of the drive (bundled in `Work.JacFinal.Inputs`) we build, for
every `k`-point `P0` of a curve `C/k`, the chart datum `Work.DescentGeom.Input C.toOver P0`
which area `DescentGeom` turns into the Jacobian package.

The semilinear Galois action on the group chunk is *constructed* in `Work.JacFinal.GalAct` from
the universal property of `AJ` over `k'`.  The `Γ`-stable affine cover `Work.JacFinal.Cover`
(§1.4 of `NOTES_LEAD_jacobian_final.md`) is *proved* in `Work.JacFinal.Orbit` from the two
chart-level items of §1.4: `IsAffineOpen V` for the Brill–Noether chart (area `CH`) and the
statement that the `Γ`-orbit of every point of `G'` lies in one chart range (§1.4(f), which
needs COV′ — `GalCharts.orbit_cov` — and the comparison `β` of area `SY`).
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical MonObj MonoidalCategory CategoryTheory
open CartesianMonoidalCategory

universe u

namespace Work.JacFinal

noncomputable section

variable {k : Type u} [Field k] {C : CurveBasics.Curve k} {P0 : 𝟙_ (Sch k) ⟶ C.toOver}

/-- The comparison of the terminal objects of the base change functor, applied to the base
point: the inverse of the terminal comparison sends `P0` to the base point of `C_{k'}`. -/
theorem terminal_comparison_inv_bcPt (d : Inputs C P0) :
    (CartesianMonoidalCategory.preservesTerminalIso
        (Work.DescentGeom.bcFun k d.k')).hom ≫ bcPt C P0 d.k' =
      (Work.DescentGeom.bcFun k d.k').map P0 := by
  rw [bcPt, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

theorem bcPt_eq_inv (d : Inputs C P0) :
    bcPt C P0 d.k' = (CartesianMonoidalCategory.preservesTerminalIso
        (Work.DescentGeom.bcFun k d.k')).inv ≫ (Work.DescentGeom.bcFun k d.k').map P0 := rfl

namespace Inputs

/-- **The Galois action of `Inputs`**: the semilinear action on the group chunk, constructed in
`Work.JacFinal.GalAct` from the universal property of area `UP`. -/
def toChunk (d : Inputs C P0) :
    Gal.Chunk (k := k) (k' := d.k') (C := C.toOver)
      (P0 := P0) where
  G := d.exports.glued.G
  grpObj := d.exports.grpObj
  isProper := d.exports.isProper_G
  smooth := by
    haveI : GrpObj (Over.mk (Over.hom d.exports.glued.G)) := d.exports.grpObj
    haveI : IsProper (d.exports.glued.G).hom := d.exports.isProper_G
    haveI : GeometricallyIntegral (d.exports.glued.G).hom := d.exports.geomIntegral_G
    exact smooth_of_grpObj (Over.hom d.exports.glued.G)
  geomIntegral := d.exports.geomIntegral_G
  AJ := d.exports.AJ₀
  AJ_pt := by
    rw [← terminal_comparison_inv_bcPt d, Category.assoc, d.exports.AJ₀_pt]
  univ := fun A' _ _ _ _ f hf => by
    haveI : Work.AbVar.IsAbelianVariety A' :=
      ⟨inferInstance, inferInstance, inferInstance⟩
    haveI := d.chart
    haveI := d.exports
    refine Work.Universal.univ (C := C.baseChange d.k') (P0 := bcPt C P0 d.k')
      (D := d.chart) (U := d.exports) f ?_
    rw [bcPt_eq_inv d, Category.assoc, hf, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  epi := fun A' _ _ _ _ u v h => by
    haveI : Work.AbVar.IsAbelianVariety A' :=
      ⟨inferInstance, inferInstance, inferInstance⟩
    haveI := d.chart
    haveI := d.exports
    exact Work.Universal.epi (C := C.baseChange d.k') (P0 := bcPt C P0 d.k')
      (D := d.chart) (U := d.exports) u v h

end Inputs

/-- **The `Γ`-stable affine cover** (§1.4 of the lead's design).  It is the field `hcover` of
`Work.DescentGeom.Input`; it is **proved** in `Submission/Work/JacFinal/Orbit.lean`
(`Work.JacFinal.Inputs.cover_of_chart_orbit`, `…cover_of_affine_orbit`,
`…cover_of_chart_orbit_act`), so it is not an assumption of the assembly. -/
structure Cover (d : Inputs C P0) where
  hcover : ∀ x : d.toChunk.G.left, ∃ Ω : d.toChunk.G.left.Opens, IsAffineOpen Ω ∧
    (∀ σ : Work.Descent.Gal k d.k', (d.toChunk.galAct σ).hom ⁻¹ᵁ Ω = Ω) ∧ x ∈ Ω

/-- The chart datum of area `DescentGeom`, built from `Inputs` and the `Γ`-stable affine
cover. -/
def inputData (d : Inputs C P0) (hc : Cover d) : Work.DescentGeom.Input C.toOver P0 :=
  { k' := d.k'
    field' := d.field'
    algebra' := d.algebra'
    isGalois' := d.galois'
    finiteDimensional' := d.finiteDimensional'
    G' := d.exports.glued.G
    grpObj' := d.exports.grpObj
    isProper' := d.exports.isProper_G
    smooth' := d.toChunk.smooth
    geomIrred' := by
      haveI := d.exports.geomIntegral_G
      infer_instance
    connected' := by
      haveI := d.exports.geomIntegral_G
      haveI : GeometricallyIrreducible (d.exports.glued.G).hom := inferInstance
      haveI : IrreducibleSpace (d.exports.glued.G).left :=
        GeometricallyIrreducible.irreducibleSpace_of_subsingleton
          (f := (d.exports.glued.G).hom)
      infer_instance
    galAct := d.toChunk.galAct
    galAct_hom := d.toChunk.galAct_hom
    galAct_one := d.toChunk.galAct_one
    galAct_mul := d.toChunk.galAct_mul
    galAct_mul_compat := d.toChunk.galAct_mul_compat
    galAct_one_compat := d.toChunk.galAct_one_compat
    galAct_inv_compat := d.toChunk.galAct_inv_compat
    hcover := hc.hcover
    AJ' := d.exports.AJ₀
    AJ'_pt := by
      rw [← terminal_comparison_inv_bcPt d, Category.assoc, d.exports.AJ₀_pt]
    AJ'_compat := d.toChunk.AJ'_compat
    univ' := d.toChunk.univ
    epi' := d.toChunk.epi }

/-- **The final assembly**: the outputs of the areas of the drive (bundled in `Inputs`) and the
`Γ`-stable affine cover produce the chart datum of area `DescentGeom`. -/
theorem nonempty_input (d : Inputs C P0) (hc : Cover d) :
    Nonempty (Work.DescentGeom.Input C.toOver P0) :=
  ⟨inputData d hc⟩

end

end Work.JacFinal
