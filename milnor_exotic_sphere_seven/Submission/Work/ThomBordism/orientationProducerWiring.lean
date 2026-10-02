import Mathlib
import Submission.Work.ThomBordism.levelModelAssembly
import Submission.Work.ThomBordism.producedBoundaryAgreement

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# THOM: the final wiring of `Work.PTGeometric.OrientationProducer`

`Work.PTGeometric.OrientationProducer` from the two statements that the fleet is proving (project
lead, probe rounds 33/34):

* **`hspec`** — the strengthened existence lemma of the source construction
  (`Work.ThomBordism.sourceRawAmbientData_strengthened`): one witness carrying the tied pin, the
  boundary coordination `SourceBoundaryCoord`, and the collar + orientation family of its level set
  (as `Work.ThomBordism.LevelOrientationHyp`).  After `producedRawData` is repointed to that theorem
  (its type is unchanged), `hspec` is *its spec*;
* **`hglue`** — `Work.ThomBordism.levelClassData_of_coord`: the recorded coordination plus the
  collar/orientation family give the relative-class datum `LevelClassData` of the raw level model.

The result is `Work.ThomBordism.ambientOrientationDataFree_of_class` applied to the two.
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

/-- **The final wiring.** -/
theorem orientationProducer_of_spec
    (hspec : ∀ (k : ℕ) (D : Work.ThomBordism.PontryaginThom.ThomTarget k) (ι : Type) [Fintype ι]
      (Fam : ι → Work.ThomBordism.Man8) [T2Space D.T]
      (hk : 11 ≤ k) (hne : ∀ i, Nonempty (Fam i).pt)
      (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (m : ℕ) (hm : 0 < m)
      (hpow : (∏ i, Work.PTGeometric.tubeAlpha (G.rep i)) ^ m = 1),
      ∃ (hWcl : IsClosed (sourceLevelSet
            (Work.PTGeometric.producedRawData hk G m hm hpow)))
        (L : Work.PTGeometric.LocalLevelData k
          (Work.PTGeometric.producedRawData hk G m hm hpow).M
          (sourceLevelSet (Work.PTGeometric.producedRawData hk G m hm hpow))),
        LevelOrientationHyp hk G m hm hpow (hWcl := hWcl) (L := L))
    (hglue : ∀ (k : ℕ) (D : Work.ThomBordism.PontryaginThom.ThomTarget k) (ι : Type) [Fintype ι]
      (Fam : ι → Work.ThomBordism.Man8) [T2Space D.T]
      (hk : 11 ≤ k) (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (m : ℕ) (hm : 0 < m)
      (hpow : (∏ i, Work.PTGeometric.tubeAlpha (G.rep i)) ^ m = 1)
      (hset : sourceLevelSet (Work.PTGeometric.producedRawData hk G m hm hpow) ∩
          (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary
            (Work.PTGeometric.producedRawData hk G m hm hpow).M
        = (Work.PTGeometric.toAmbientCollapseEnd (Nat.le_add_right k G.mU)
            (Work.PTGeometric.producedAmbientData hk G m hm hpow)).S ∩
          {x | (Work.PTGeometric.toAmbientCollapseEnd (Nat.le_add_right k G.mU)
            (Work.PTGeometric.producedAmbientData hk G m hm hpow)).v x = 0})
      {hWcl : IsClosed (sourceLevelSet (Work.PTGeometric.producedRawData hk G m hm hpow))}
      {L : Work.PTGeometric.LocalLevelData k
        (Work.PTGeometric.producedRawData hk G m hm hpow).M
        (sourceLevelSet (Work.PTGeometric.producedRawData hk G m hm hpow))}
      (hcolγ : LevelOrientationHyp hk G m hm hpow (hWcl := hWcl) (L := L))
      (hcoord : SourceBoundaryCoord (Work.PTGeometric.producedRawData hk G m hm hpow)),
      LevelClassData hk G m hm hpow hset (hWcl := hWcl) (L := L)) :
    Work.PTGeometric.OrientationProducer := by
  intro k D ι _ Fam _ hk hne G m hm hpow
  obtain ⟨hWcl, L, hcolγ⟩ := hspec k D ι Fam hk hne G m hm hpow
  exact ambientOrientationDataFree_of_class hk G m hm hpow
    (Work.PTGeometric.toAmbientCollapseEnd_levelSet_bdry_eq hk G m hm hpow)
    (hglue k D ι Fam hk G m hm hpow _
      hcolγ (Work.PTGeometric.producedRawData_coord hk G m hm hpow))


/-- **The `hspec` input of `orientationProducer_of_spec`, from the source construction.**

`Work.ThomBordism.SourceOrientHyp` (the collar *and* the orientation family of the level model of a
raw datum, `Submission/Work/ThomBordism/sourceCoord.lean`) is *the same proposition* as
`Work.ThomBordism.LevelOrientationHyp` at the produced raw datum; the two definitions differ only in
the way the level set is written (`sourceLevelSet D0` versus `{x | D0.v x = 0}`).  So the third
conjunct of `Work.PTGeometric.producedRawData_spec` is exactly a `LevelOrientationHyp`. -/
theorem sourceLevelOrientationHyp
    {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k} {ι : Type} [Fintype ι]
    {Fam : ι → Work.ThomBordism.Man8} [T2Space D.T]
    (hk : 11 ≤ k) (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (m : ℕ) (hm : 0 < m)
    (hpow : (∏ i, Work.PTGeometric.tubeAlpha (G.rep i)) ^ m = 1) :
    ∃ (hWcl : IsClosed
        (sourceLevelSet (Work.PTGeometric.producedRawData hk G m hm hpow)))
      (L : Work.PTGeometric.LocalLevelData k
        (Work.PTGeometric.producedRawData hk G m hm hpow).M
        (sourceLevelSet (Work.PTGeometric.producedRawData hk G m hm hpow))),
      LevelOrientationHyp hk G m hm hpow (hWcl := hWcl) (L := L) := by
  obtain ⟨hWcl, L, h⟩ := Work.PTGeometric.producedRawData_orientation hk G m hm hpow
  exact ⟨hWcl, L, h⟩

end

end Work.ThomBordism
