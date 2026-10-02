import Mathlib
import Submission.Work.ThomBordism.sourceCoord

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# THOM: the canonical identification of the level model's boundary with the pieces

For any raw datum `D0` of the source construction the boundary part of the level model
`{x | D0.v x = 0}` (in the `Lvl` charted space of `Work.PTGeometric.levelSetup`) is canonically
homeomorphic to the disjoint union of the pieces, and the homeomorphism is the collapse
identification `D0.hend` read through the identification of the boundary part with
`D0.S ∩ {D0.v = 0}` (which is a homeomorphism here because both are compact and T2).

The module is **cycle-free**: it imports only `sourceCoord`, so it can be used *inside* the source
construction (`sourceRawAmbientData_tied_collar.lean`), where the assembly datum
`Work.ThomBordism.SourceBoundaryCoordAssemblyData` needs exactly this identification together with
the agreement `(e.symm ⟨a, y⟩).1 = (piecePush D0 a y).1` (the second conjunct below).  The statement
is generic in `D0`, so it can be instantiated at the construction's own witness `D0'`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory
open scoped Manifold

namespace Work.ThomBordism


/-- **The canonical identification of the level model's boundary with the pieces.** -/
theorem levelBdryHomeoOf {k mU m : ℕ} {ι : Type} [Fintype ι] {Fam : ι → Man8}
    (D0 : Work.PTGeometric.RawAmbientData (k + mU) k (Fin m × ι) (fun a => Fam a.2))
    {hWcl : IsClosed (sourceLevelSet D0)}
    {L : Work.PTGeometric.LocalLevelData k D0.M (sourceLevelSet D0)} :
    ∃ e : ↥((modelWithCornersEuclideanHalfSpace 9).boundary
        (Work.PTGeometric.levelSetup (sourceLevelSet D0) hWcl L).Pre) ≃ₜ
        (Σ a : Fin m × ι, (Fam a.2).pt),
      ∀ (a : Fin m × ι) (y : (Fam a.2).pt),
        ((e.symm ⟨a, y⟩ : ↥((modelWithCornersEuclideanHalfSpace 9).boundary
            (Work.PTGeometric.levelSetup (sourceLevelSet D0) hWcl L).Pre)).1 :
          ↥(sourceLevelSet D0)) =
        ((piecePush D0 a y : ↥(sourceLevelBdry D0)) : ↥(sourceLevelSet D0)) := by
  classical
  have hbdrySet : (modelWithCornersEuclideanHalfSpace 9).boundary
      (Work.PTGeometric.levelSetup (sourceLevelSet D0) hWcl L).Pre = sourceLevelBdry D0 :=
    Set.ext fun x => Work.PTGeometric.Lvl.Setup.mem_boundary_iff _ x
  let toB : ↥(D0.S ∩ {x : D0.M | D0.v x = 0}) → ↥(sourceLevelBdry D0) := fun w =>
    ⟨⟨w.1, w.2.2⟩, D0.hSsub w.2.1⟩
  let toS : ↥(sourceLevelBdry D0) → ↥(D0.S ∩ {x : D0.M | D0.v x = 0}) := fun x =>
    ⟨x.1.1, D0.hzero_sub x.1.1 x.2 x.1.2, x.1.2⟩
  have htoB_toS : ∀ x, toB (toS x) = x := fun x => rfl
  have htoS_toB : ∀ w, toS (toB w) = w := fun w => rfl
  have hinner : Continuous (fun w : ↥(D0.S ∩ {x : D0.M | D0.v x = 0}) =>
      (⟨w.1, w.2.2⟩ : ↥(sourceLevelSet D0))) :=
    Continuous.subtype_mk continuous_subtype_val (fun w => w.2.2)
  have hB : Continuous toB := Continuous.subtype_mk hinner (fun w => D0.hSsub w.2.1)
  have hS : Continuous toS :=
    Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val)
      (fun x => ⟨D0.hzero_sub x.1.1 x.2 x.1.2, x.1.2⟩)
  let toBHomeo : ↥(D0.S ∩ {x : D0.M | D0.v x = 0}) ≃ₜ ↥(sourceLevelBdry D0) :=
    { toFun := toB, invFun := toS, left_inv := htoS_toB, right_inv := htoB_toS,
      continuous_toFun := hB, continuous_invFun := hS }
  refine ⟨(Homeomorph.setCongr hbdrySet).trans (toBHomeo.symm.trans D0.hend), ?_⟩
  intro a y
  apply Subtype.ext
  rfl

end Work.ThomBordism
