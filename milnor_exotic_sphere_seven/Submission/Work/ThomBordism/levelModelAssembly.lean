import Mathlib
import Submission.Work.ThomBordism.levelModelSetup
import Submission.Work.PTGeometric.OrientationFree

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# THOM: the last-mile assembly (from the recorded conjuncts of the source construction)

`Work.PTGeometric.AmbientOrientationDataFree` for the *produced* data, given the recorded conjuncts of
the source construction (`Submission/Work/ThomBordism/NOTE_R_A_PLAN.md`): the collar of the raw level
set, and a relative fundamental class of the raw level model whose boundary is the sum of the pieces'
classes along the collapse identification.

The class datum (`Work.ThomBordism.LevelClassData`) is a *hypothesis* here, because it is the output
of `Work.ThomBordism.exists_relFundClass_of_pieces_bound` (the `w_fund` bookkeeping, PROVED) applied
to the boundary coordination proved inside the construction.  The index type of the produced data is
`Fin m × ι` with family `fun a => Fam a.2`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter
open CategoryTheory CategoryTheory.Limits

namespace Work.ThomBordism

noncomputable section

open Work.PTGeometric Work.Cohomology

variable {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k} {ι : Type} [Fintype ι]
  {Fam : ι → Work.ThomBordism.Man8} [T2Space D.T]

/-- The collapse identification of the produced data, restricted to the raw level set's boundary
part (the `e` of `Work.PTGeometric.AmbientOrientationDataFree`). -/
def levelBdryHomeo (hk : 11 ≤ k) (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam)
    (m : ℕ) (hm : 0 < m) (hpow : (∏ i, Work.PTGeometric.tubeAlpha (G.rep i)) ^ m = 1)
    (hset : sourceLevelSet (producedRawData hk G m hm hpow) ∩
        (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary
          (producedRawData hk G m hm hpow).M
      = (toAmbientCollapseEnd (Nat.le_add_right k G.mU)
          (producedAmbientData hk G m hm hpow)).S ∩
        {x | (toAmbientCollapseEnd (Nat.le_add_right k G.mU)
          (producedAmbientData hk G m hm hpow)).v x = 0}) :
    ↥(sourceLevelSet (producedRawData hk G m hm hpow) ∩
        (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary
          (producedRawData hk G m hm hpow).M)
      ≃ₜ (Σ a : Fin m × ι, (Fam a.2).pt) :=
  (Homeomorph.setCongr hset).trans
    (toAmbientCollapseEnd (Nat.le_add_right k G.mU)
      (producedAmbientData hk G m hm hpow)).endHomeo

/-- The full identification of the level model's boundary with the pieces. -/
def levelBdryHomeoFull (hk : 11 ≤ k) (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam)
    (m : ℕ) (hm : 0 < m) (hpow : (∏ i, Work.PTGeometric.tubeAlpha (G.rep i)) ^ m = 1)
    (hset : sourceLevelSet (producedRawData hk G m hm hpow) ∩
        (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary
          (producedRawData hk G m hm hpow).M
      = (toAmbientCollapseEnd (Nat.le_add_right k G.mU)
          (producedAmbientData hk G m hm hpow)).S ∩
        {x | (toAmbientCollapseEnd (Nat.le_add_right k G.mU)
          (producedAmbientData hk G m hm hpow)).v x = 0})
    {hWcl : IsClosed (sourceLevelSet (producedRawData hk G m hm hpow))}
    {L : Work.PTGeometric.LocalLevelData k (producedRawData hk G m hm hpow).M
      (sourceLevelSet (producedRawData hk G m hm hpow))} :
    ↥((modelWithCornersEuclideanHalfSpace 9).boundary
        (Work.PTGeometric.levelModel (sourceLevelSet (producedRawData hk G m hm hpow)) hWcl L))
      ≃ₜ (Σ a : Fin m × ι, (Fam a.2).pt) :=
  (levelBdryPreimage hk G m hm hpow (hWcl := hWcl) (L := L)).trans
    (levelBdryHomeo hk G m hm hpow hset)

/-- **The collar and the orientation family of the raw level model** (the two inputs of the
relative-fundamental-class existence theorem `Work.ThomBordism.exists_relFundClass_of_collar'`, in
the `Lvl` chart structure of the level model). -/
def LevelOrientationHyp (hk : 11 ≤ k) (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam)
    (m : ℕ) (hm : 0 < m) (hpow : (∏ i, Work.PTGeometric.tubeAlpha (G.rep i)) ^ m = 1)
    {hWcl : IsClosed (sourceLevelSet (producedRawData hk G m hm hpow))}
    {L : Work.PTGeometric.LocalLevelData k (producedRawData hk G m hm hpow).M
      (sourceLevelSet (producedRawData hk G m hm hpow))} : Prop := by
  let S : Lvl.Setup k :=
    Work.PTGeometric.levelSetup (sourceLevelSet (producedRawData hk G m hm hpow)) hWcl L
  letI := Work.PTGeometric.Lvl.Setup.instChartedSpace S
  exact Nonempty (Work.Surgery.Collar 8 S.Pre) ∧
    ∃ γ : ∀ x : S.Pre, x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary S.Pre →
        Work.Orient.LocH (TopCat.of S.Pre) 9 x,
      Work.Orient.IsHalfOrientationFamily 8 (TopCat.of S.Pre) γ

/-- **The class datum of the raw level model**: a relative fundamental class whose boundary is the
sum of the pieces' classes along the collapse identification. -/
def LevelClassData (hk : 11 ≤ k) (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam)
    (m : ℕ) (hm : 0 < m) (hpow : (∏ i, Work.PTGeometric.tubeAlpha (G.rep i)) ^ m = 1)
    (hset : sourceLevelSet (producedRawData hk G m hm hpow) ∩
        (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary
          (producedRawData hk G m hm hpow).M
      = (toAmbientCollapseEnd (Nat.le_add_right k G.mU)
          (producedAmbientData hk G m hm hpow)).S ∩
        {x | (toAmbientCollapseEnd (Nat.le_add_right k G.mU)
          (producedAmbientData hk G m hm hpow)).v x = 0})
    {hWcl : IsClosed (sourceLevelSet (producedRawData hk G m hm hpow))}
    {L : Work.PTGeometric.LocalLevelData k (producedRawData hk G m hm hpow).M
      (sourceLevelSet (producedRawData hk G m hm hpow))} : Prop := by
  let S : Lvl.Setup k :=
    Work.PTGeometric.levelSetup (sourceLevelSet (producedRawData hk G m hm hpow)) hWcl L
  letI := Work.PTGeometric.Lvl.Setup.instChartedSpace S
  exact ∃ w : (Work.Cohomology.relChains (TopCat.of S.Pre)
      ((modelWithCornersEuclideanHalfSpace 9).boundary S.Pre)).homology 9,
    (∀ (x : S.Pre) (hx : x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary S.Pre),
      Submodule.span ℤ {(HomologicalComplex.homologyMap
        (Work.ThomBordism.relChainsInclPunct (TopCat.of S.Pre)
          ((modelWithCornersEuclideanHalfSpace 9).boundary S.Pre) x hx) 9 w)} = ⊤) ∧
    (Work.Cohomology.hPairδ (TopCat.of S.Pre)
        ((modelWithCornersEuclideanHalfSpace 9).boundary S.Pre) 8 w
      = ∑ i : Fin m × ι, HomologicalComplex.homologyMap
          (Work.Cohomology.chainMap ℤ (Fam i.2).X
            (TopCat.of ((modelWithCornersEuclideanHalfSpace 9).boundary S.Pre))
            (TopCat.ofHom ⟨fun y => (levelBdryHomeoFull hk G m hm hpow hset
                (hWcl := hWcl) (L := L)).symm ⟨i, y⟩,
              (levelBdryHomeoFull hk G m hm hpow hset (hWcl := hWcl)
                (L := L)).continuous_invFun.comp continuous_sigmaMk⟩)) 8 (Fam i.2).c)

/-- **The assembly**: the recorded conjuncts of the source construction give
`Work.PTGeometric.AmbientOrientationDataFree` for the produced data. -/
theorem ambientOrientationDataFree_of_class
    (hk : 11 ≤ k) (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (m : ℕ) (hm : 0 < m)
    (hpow : (∏ i, Work.PTGeometric.tubeAlpha (G.rep i)) ^ m = 1)
    (hset : sourceLevelSet (producedRawData hk G m hm hpow) ∩
        (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary
          (producedRawData hk G m hm hpow).M
      = (toAmbientCollapseEnd (Nat.le_add_right k G.mU)
          (producedAmbientData hk G m hm hpow)).S ∩
        {x | (toAmbientCollapseEnd (Nat.le_add_right k G.mU)
          (producedAmbientData hk G m hm hpow)).v x = 0})
    {hWcl : IsClosed (sourceLevelSet (producedRawData hk G m hm hpow))}
    {L : Work.PTGeometric.LocalLevelData k (producedRawData hk G m hm hpow).M
      (sourceLevelSet (producedRawData hk G m hm hpow))}
    (hw : LevelClassData hk G m hm hpow hset (hWcl := hWcl) (L := L)) :
    Work.PTGeometric.AmbientOrientationDataFree (toAmbientCollapseEnd (Nat.le_add_right k G.mU)
      (producedAmbientData hk G m hm hpow)) := by
  let S : Lvl.Setup k :=
    Work.PTGeometric.levelSetup (sourceLevelSet (producedRawData hk G m hm hpow)) hWcl L
  letI := Work.PTGeometric.Lvl.Setup.instChartedSpace S
  letI := Work.PTGeometric.Lvl.Setup.instIsManifold S
  letI := Work.PTGeometric.Lvl.Setup.instCompactSpace S
  obtain ⟨w, hwf, hws⟩ := hw
  refine ⟨sourceLevelSet (producedRawData hk G m hm hpow), hWcl, L, hset, ⟨{
    chartedSpace := Work.PTGeometric.Lvl.Setup.instChartedSpace S
    isManifold := Work.PTGeometric.Lvl.Setup.instIsManifold S
    compactSpace := Work.PTGeometric.Lvl.Setup.instCompactSpace S
    t2Space := inferInstance
    bdry_eq := Set.ext fun x => Work.PTGeometric.Lvl.Setup.mem_boundary_iff S x
    bdryPreimage := levelBdryPreimage hk G m hm hpow
    w := w
    w_fund := hwf
    sign := hws }⟩⟩

end

end Work.ThomBordism
