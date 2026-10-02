import Submission.Work.PTGeometric.OrientationFree
import Submission.Work.Orient.Preimage
import Submission.Work.PTGeometric.exists_halfOrientationFamily_of_det_pos

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: applying (O3) — the orientation datum from a positively oriented chart structure

`Work.PTGeometric.LevelOrientationModelData` (the free-model orientation datum of the level set,
`OrientationFree.lean`) asks for a `C^∞` `9`-manifold structure on the level-set space `↥W` whose
boundary is the part `W ∩ ∂M` of the source's boundary, a relative fundamental class `w` which is a
local generator at every interior point, and the **signed** boundary identity
(`hPairδ w = ∑ i, (piece i)`).

This file proves that this datum follows from four geometrically primitive inputs:

* **(O3)**, the missing chapter "a positive-determinant atlas orients a manifold with boundary"
  (`Work.PTGeometric.exists_halfOrientationFamily_of_det_pos`, taken here as a hypothesis of the
  *frozen statement* so that the wiring does not depend on its proof being finished);
* a chart structure on `↥W` (with its `C^∞` structure and boundary pinning) whose atlas has
  **positive transitions** — a genuinely *differential-geometric* statement: it is the form in which
  the coorientation of the level set (the oriented Gauss data `GenuineTubeGeometry.gauss`) enters, and
  it is provable in principle by correcting the charts of the canonical model by a constant
  orientation-normalising linear map, see `NOTE_G5_REPAIR.md` §3;
* ORIENT's relative-fundamental-class existence theorem (`Work.Orient.RelativeFundamentalClassExists
  8`, an allowed input: it follows from `Work.Surgery.HasCollar` by
  `Work.Orient.Boundary.RelativeFundamentalClassExists_of_hasCollar`);
* the **sign** for the class produced by ORIENT out of `γ` (G5-(ii): TUBULAR's local degree; ORIENT's
  own `Work.Orient.BoundaryOrientationConvention` is deliberately sign-blind).

## Main results

* `Work.PTGeometric.levelOrientationModelData_of_positiveAtlas`
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter
open CategoryTheory AlgebraicTopology

namespace Work.PTGeometric

noncomputable section

open Work.ThomBordism
open Work.Cohomology

/-- **(O3) as a hypothesis**: a positive-determinant atlas orients a manifold with boundary.  This is
the frozen statement of `Work.PTGeometric.exists_halfOrientationFamily_of_det_pos`. -/
def PositiveAtlasOrients : Prop :=
  ∀ (n : ℕ) (X : TopCat) [T2Space X] [ChartedSpace (EuclideanHalfSpace (n + 1)) X]
    [IsManifold (𝓡∂ (n + 1)) 1 X],
    (∀ (x y : X), x ∉ (𝓡∂ (n + 1)).boundary X → y ∉ (𝓡∂ (n + 1)).boundary X →
      ∀ z ∈ (extChartAt (𝓡∂ (n + 1)) x).target ∩
          (extChartAt (𝓡∂ (n + 1)) x).symm ⁻¹' (extChartAt (𝓡∂ (n + 1)) y).source,
        z 0 > 0 →
        (0 : ℝ) < LinearMap.det ((fderiv ℝ (fun w : EuclideanSpace ℝ (Fin (n + 1)) =>
          (extChartAt (𝓡∂ (n + 1)) y) ((extChartAt (𝓡∂ (n + 1)) x).symm w)) z) :
            EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))) →
    ∃ γ : ∀ x : X, x ∉ (𝓡∂ (n + 1)).boundary X → Work.Orient.LocH X (n + 1) x,
      Work.Orient.IsHalfOrientationFamily n X γ

/-- **The positive-determinant condition for a chart structure on the level set** — the hypothesis
of (O3), stated for the model of `↥W`. -/
def HasPositiveAtlas {k : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M] (W : Set M)
    [ChartedSpace (EuclideanHalfSpace 9) ↥W] [IsManifold (𝓡∂ 9) 1 ↥W] : Prop :=
  ∀ (x y : ↥W), x ∉ (𝓡∂ 9).boundary ↥W → y ∉ (𝓡∂ 9).boundary ↥W →
    ∀ z ∈ (extChartAt (𝓡∂ 9) x).target ∩
        (extChartAt (𝓡∂ 9) x).symm ⁻¹' (extChartAt (𝓡∂ 9) y).source,
      z 0 > 0 →
      (0 : ℝ) < LinearMap.det ((fderiv ℝ (fun w : EuclideanSpace ℝ (Fin 9) =>
        (extChartAt (𝓡∂ 9) y) ((extChartAt (𝓡∂ 9) x).symm w)) z) :
          EuclideanSpace ℝ (Fin 9) →ₗ[ℝ] EuclideanSpace ℝ (Fin 9))

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
  [IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M] [CompactSpace M] [T2Space M]
  {W : Set M} {hWcl : IsClosed W} {L : LocalLevelData k M W}
  {ι : Type} [Fintype ι] {Fam : ι → Man8}

/-- **The orientation datum from a positively oriented chart structure.**

Given (O3) (`hO3`), ORIENT's relative-fundamental-class existence theorem (`hOrient`), a `C^∞`
`9`-manifold structure on `↥W` whose boundary is `W ∩ ∂M` (`cW`, `mW`, `cpt`, `t2`, `hbd`) whose
atlas has positive transitions (`hdet`), and the sign for the class ORIENT produces from the
orientation family that (O3) gives out of `hdet` (`hsign`), the level set carries the free-model
orientation datum. -/
theorem levelOrientationModelData_of_positiveAtlas
    (hO3 : PositiveAtlasOrients)
    (hOrient : Work.Orient.RelativeFundamentalClassExists 8)
    [cW : ChartedSpace (EuclideanHalfSpace 9) ↥W] [mW : IsManifold (𝓡∂ 9) ∞ ↥W]
    [cpt : CompactSpace ↥W] [t2 : T2Space ↥W] [ne : Nonempty ↥W]
    (hbd : (𝓡∂ 9).boundary ↥W = {x : ↥W | (x : M) ∈ (𝓡∂ ((8 + k) + 1)).boundary M})
    (hdet : HasPositiveAtlas (k := k) W)
    (e : ↥(W ∩ (𝓡∂ ((8 + k) + 1)).boundary M) ≃ₜ (Σ i : ι, (Fam i).pt))
    (hsign : ∀ (γ : ∀ x : ↥W, x ∉ (𝓡∂ 9).boundary ↥W → Work.Orient.LocH (TopCat.of ↥W) 9 x)
      (hγ : Work.Orient.IsHalfOrientationFamily 8 (TopCat.of ↥W) γ),
      ∃ bdryPreimage : ((𝓡∂ 9).boundary ↥W) ≃ₜ ↥(W ∩ (𝓡∂ ((8 + k) + 1)).boundary M),
        Work.Cohomology.hPairδ (TopCat.of ↥W) ((𝓡∂ 9).boundary ↥W) 8
            (Classical.choose (Work.Orient.exists_relFundClass_of_halfOrientation hOrient ↥W γ hγ))
          = ∑ i, HomologicalComplex.homologyMap
              (Work.Cohomology.chainMap ℤ (Fam i).X (TopCat.of ((𝓡∂ 9).boundary ↥W))
                (TopCat.ofHom ⟨fun y => (bdryPreimage.trans e).symm ⟨i, y⟩,
                  (bdryPreimage.trans e).continuous_invFun.comp continuous_sigmaMk⟩)) 8 (Fam i).c) :
    LevelOrientationDatumFree W hWcl L Fam e := by
  haveI : IsManifold (𝓡∂ 9) 1 ↥W := IsManifold.of_le (n := ∞) (by simp)
  obtain ⟨γ, hγ⟩ := hO3 8 (TopCat.of ↥W) hdet
  obtain ⟨bdryPreimage, hsign'⟩ := hsign γ hγ
  exact ⟨{ chartedSpace := cW, isManifold := mW, compactSpace := cpt, t2Space := t2, bdry_eq := hbd, bdryPreimage := bdryPreimage, w := Classical.choose (Work.Orient.exists_relFundClass_of_halfOrientation hOrient ↥W γ hγ), w_fund := (Classical.choose_spec (Work.Orient.exists_relFundClass_of_halfOrientation hOrient ↥W γ hγ)).2.1, sign := hsign' }⟩

/-- **The orientation datum from an orientation family** (the §10 route): given an orientation family
`γ` of a `C^∞` `9`-manifold structure on `↥W` with boundary `W ∩ ∂M` (as produced by
`Work.PTGeometric.exists_chartedSpace_and_orientationFamily_of_levelChartData`) and the sign for the
class ORIENT produces out of it, the free-model datum follows — with no positive-atlas hypothesis and
no (O3). -/
theorem levelOrientationModelData_of_orientationFamily
    (hOrient : Work.Orient.RelativeFundamentalClassExists 8)
    [cW : ChartedSpace (EuclideanHalfSpace 9) ↥W] [mW : IsManifold (𝓡∂ 9) ∞ ↥W]
    [cpt : CompactSpace ↥W] [t2 : T2Space ↥W] [ne : Nonempty ↥W]
    (hbd : (𝓡∂ 9).boundary ↥W = {x : ↥W | (x : M) ∈ (𝓡∂ ((8 + k) + 1)).boundary M})
    (γ : ∀ x : ↥W, x ∉ (𝓡∂ 9).boundary ↥W → Work.Orient.LocH (TopCat.of ↥W) 9 x)
    (hγ : Work.Orient.IsHalfOrientationFamily 8 (TopCat.of ↥W) γ)
    (e : ↥(W ∩ (𝓡∂ ((8 + k) + 1)).boundary M) ≃ₜ (Σ i : ι, (Fam i).pt))
    (hsign : ∃ bdryPreimage : ((𝓡∂ 9).boundary ↥W) ≃ₜ ↥(W ∩ (𝓡∂ ((8 + k) + 1)).boundary M),
      Work.Cohomology.hPairδ (TopCat.of ↥W) ((𝓡∂ 9).boundary ↥W) 8
          (Classical.choose (Work.Orient.exists_relFundClass_of_halfOrientation hOrient ↥W γ hγ))
        = ∑ i, HomologicalComplex.homologyMap
            (Work.Cohomology.chainMap ℤ (Fam i).X (TopCat.of ((𝓡∂ 9).boundary ↥W))
              (TopCat.ofHom ⟨fun y => (bdryPreimage.trans e).symm ⟨i, y⟩,
                (bdryPreimage.trans e).continuous_invFun.comp continuous_sigmaMk⟩)) 8 (Fam i).c) :
    LevelOrientationDatumFree W hWcl L Fam e := by
  obtain ⟨bdryPreimage, hsign'⟩ := hsign
  exact ⟨{ chartedSpace := cW, isManifold := mW, compactSpace := cpt, t2Space := t2, bdry_eq := hbd, bdryPreimage := bdryPreimage, w := Classical.choose (Work.Orient.exists_relFundClass_of_halfOrientation hOrient ↥W γ hγ), w_fund := (Classical.choose_spec (Work.Orient.exists_relFundClass_of_halfOrientation hOrient ↥W γ hγ)).2.1, sign := hsign' }⟩

/-- **(O3) is proved**: `Work.PTGeometric.exists_halfOrientationFamily_of_det_pos`
(`Submission.Work.PTGeometric.exists_halfOrientationFamily_of_det_pos`) is the missing chapter
"a positive-determinant atlas orients a manifold with boundary". -/
theorem positiveAtlasOrients : PositiveAtlasOrients :=
  fun n X _ _ _ hdet => exists_halfOrientationFamily_of_det_pos n X hdet

/-- **The orientation datum from a positively oriented chart structure** — the (O3)-wire with (O3)
discharged, so the geometric inputs are exactly: a `C^∞` `9`-manifold structure on `↥W` with boundary
`W ∩ ∂M` whose atlas has positive transitions, the sign for the class ORIENT produces, and ORIENT's
`RelativeFundamentalClassExists 8`. -/
theorem levelOrientationModelData_of_positiveAtlas'
    (hOrient : Work.Orient.RelativeFundamentalClassExists 8)
    [cW : ChartedSpace (EuclideanHalfSpace 9) ↥W] [mW : IsManifold (𝓡∂ 9) ∞ ↥W]
    [cpt : CompactSpace ↥W] [t2 : T2Space ↥W] [ne : Nonempty ↥W]
    (hbd : (𝓡∂ 9).boundary ↥W = {x : ↥W | (x : M) ∈ (𝓡∂ ((8 + k) + 1)).boundary M})
    (hdet : HasPositiveAtlas (k := k) W)
    (e : ↥(W ∩ (𝓡∂ ((8 + k) + 1)).boundary M) ≃ₜ (Σ i : ι, (Fam i).pt))
    (hsign : ∀ (γ : ∀ x : ↥W, x ∉ (𝓡∂ 9).boundary ↥W → Work.Orient.LocH (TopCat.of ↥W) 9 x)
      (hγ : Work.Orient.IsHalfOrientationFamily 8 (TopCat.of ↥W) γ),
      ∃ bdryPreimage : ((𝓡∂ 9).boundary ↥W) ≃ₜ ↥(W ∩ (𝓡∂ ((8 + k) + 1)).boundary M),
        Work.Cohomology.hPairδ (TopCat.of ↥W) ((𝓡∂ 9).boundary ↥W) 8
            (Classical.choose (Work.Orient.exists_relFundClass_of_halfOrientation hOrient ↥W γ hγ))
          = ∑ i, HomologicalComplex.homologyMap
              (Work.Cohomology.chainMap ℤ (Fam i).X (TopCat.of ((𝓡∂ 9).boundary ↥W))
                (TopCat.ofHom ⟨fun y => (bdryPreimage.trans e).symm ⟨i, y⟩,
                  (bdryPreimage.trans e).continuous_invFun.comp continuous_sigmaMk⟩)) 8 (Fam i).c) :
    LevelOrientationDatumFree W hWcl L Fam e :=
  levelOrientationModelData_of_positiveAtlas positiveAtlasOrients hOrient hbd hdet e hsign

end

end Work.PTGeometric
