import Mathlib
import Submission.Work.PTGeometric.SourceWiring
import Submission.Work.ThomBordism.sourceCoord
import Submission.Work.ThomBordism.producedBoundaryAgreement

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# THOM: the plumbing of the last-mile assembly

Two helpers for the assembly of `Work.PTGeometric.OrientationProducer` from the recorded conjuncts of
the source construction (`Submission/Work/ThomBordism/NOTE_R_A_PLAN.md`):

* `bdryNest` — the canonical homeomorphism between the two presentations of a boundary part
  (`{x : ↥W | (x : M) ∈ E}` versus `↥(W ∩ E)`);
* `levelBdryPreimage` — the identification of the *canonical* (`Lvl`) boundary of the raw level
  model with the raw boundary part `{v = 0} ∩ ∂M`, obtained from `Lvl.Setup.mem_boundary_iff` and
  `bdryNest`.  This is the `bdryPreimage` field of `Work.PTGeometric.LevelOrientationModelData`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter
open CategoryTheory CategoryTheory.Limits

namespace Work.ThomBordism

noncomputable section

open Work.PTGeometric Work.Cohomology

variable {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k} {ι : Type} [Fintype ι]
  {Fam : ι → Work.ThomBordism.Man8} [T2Space D.T]

/-- **The canonical homeomorphism between the two presentations of a boundary part.** -/
def bdryNest {M : Type} [TopologicalSpace M] (W E : Set M) :
    ↥{x : ↥W | (x : M) ∈ E} ≃ₜ ↥(W ∩ E) where
  toFun x := ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
  invFun y := ⟨⟨y.1, y.2.1⟩, y.2.2⟩
  left_inv x := Subtype.ext (Subtype.ext rfl)
  right_inv y := Subtype.ext rfl
  continuous_toFun := by
    have h : Continuous (fun x : ↥{x : ↥W | (x : M) ∈ E} => (x.1.1 : M)) :=
      continuous_subtype_val.comp
        (continuous_subtype_val : Continuous (fun x : ↥{x : ↥W | (x : M) ∈ E} => (x.1 : ↥W)))
    exact Continuous.subtype_mk h (fun x => ⟨x.1.2, x.2⟩)
  continuous_invFun := by
    have h : Continuous (fun y : ↥(W ∩ E) => (y.1 : M)) := continuous_subtype_val
    exact Continuous.subtype_mk
      (Continuous.subtype_mk h (fun y => y.2.1)) (fun y => y.2.2)

/-- **The `bdryPreimage` field of `LevelOrientationModelData` for the raw level set**: the canonical
(`Lvl`) boundary of the level model is the raw boundary part `{v = 0} ∩ ∂M`. -/
def levelBdryPreimage (hk : 11 ≤ k) (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam)
    (m : ℕ) (hm : 0 < m) (hpow : (∏ i, Work.PTGeometric.tubeAlpha (G.rep i)) ^ m = 1)
    {hWcl : IsClosed (sourceLevelSet (producedRawData hk G m hm hpow))}
    {L : Work.PTGeometric.LocalLevelData k (producedRawData hk G m hm hpow).M
      (sourceLevelSet (producedRawData hk G m hm hpow))} :
    ((modelWithCornersEuclideanHalfSpace 9).boundary
        (Work.PTGeometric.levelModel (sourceLevelSet (producedRawData hk G m hm hpow)) hWcl L))
      ≃ₜ ↥(sourceLevelSet (producedRawData hk G m hm hpow) ∩
        (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary
          (producedRawData hk G m hm hpow).M) := by
  letI : ChartedSpace (EuclideanHalfSpace 9)
      (Work.PTGeometric.levelModel (sourceLevelSet (producedRawData hk G m hm hpow)) hWcl L) :=
    Work.PTGeometric.Lvl.Setup.instChartedSpace
      (Work.PTGeometric.levelSetup (sourceLevelSet (producedRawData hk G m hm hpow)) hWcl L)
  exact (Homeomorph.setCongr (Set.ext fun x =>
      Work.PTGeometric.Lvl.Setup.mem_boundary_iff
        (Work.PTGeometric.levelSetup (sourceLevelSet (producedRawData hk G m hm hpow)) hWcl L) x)).trans
    (bdryNest (sourceLevelSet (producedRawData hk G m hm hpow))
      ((modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary
        (producedRawData hk G m hm hpow).M))

end

end Work.ThomBordism
