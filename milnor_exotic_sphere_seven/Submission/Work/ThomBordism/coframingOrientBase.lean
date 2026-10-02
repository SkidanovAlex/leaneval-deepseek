import Mathlib
import Submission.Work.ThomBordism.levelSet_positiveAtlas_of_coframing
import Submission.Work.ThomBordism.isHalfOrientationFamily_relChainsInclPunct
import Submission.Work.ThomBordism.orientOfCollar
import Submission.Work.ThomBordism.CollarInstanceCongr
import Submission.Work.PTGeometric.LevelModel
import Submission.Work.PTGeometric.exists_halfOrientationFamily_of_det_pos
import Submission.Work.Orient.Boundary

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# THOM: the orientation family of a coframed level set, in a module BELOW the source construction

This is `Work.ThomBordism.orientationFamily_of_coframingDataBase`: the *same* statement and proof as
`Work.ThomBordism.orientationFamily_of_coframingData` (`orientationFamily_of_data.lean`), but in a
module whose import closure does **not** contain
`Submission.Work.ThomBordism.sourceRawAmbientData_tied_collar`, so that the source construction itself
can use it (`NOTE_SESSION30.md` §7: the original module imports
`sourceLevelSet_orientationFamily`, which imports the construction — an import cycle).

The only non-generic ingredient of the original proof was `exists_localGenerator_congr`, which is
copied here verbatim.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter
open CategoryTheory CategoryTheory.Limits

abbrev AmbientPositiveAtlas (k : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M] : Prop :=
  ∀ (x y : M),
    x ∉ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary M →
    y ∉ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary M →
    ∀ z ∈ (extChartAt (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)) x).target ∩
        (extChartAt (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)) x).symm ⁻¹'
          (extChartAt (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)) y).source,
      z 0 > 0 →
      (0 : ℝ) < LinearMap.det
        ((fderiv ℝ (fun w : EuclideanSpace ℝ (Fin ((8 + k) + 1)) =>
          (extChartAt (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)) y)
            ((extChartAt (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)) x).symm w)) z)
          : EuclideanSpace ℝ (Fin ((8 + k) + 1)) →ₗ[ℝ]
            EuclideanSpace ℝ (Fin ((8 + k) + 1)))

/-- **A positively oriented coframing of a plane field over the zeros of `v`.** -/
abbrev PlaneFieldCoframing (n k : ℕ) (M : Type) [TopologicalSpace M]
    (P : M → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (W : Set M) : Prop :=
  ∃ (m : ℕ) (U : Fin m → Set M)
    (ℓ : Fin m → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (e : Fin m → M → EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin n)),
    (∀ j, IsOpen (U j)) ∧ (∀ x ∈ W, ∃ j, x ∈ U j) ∧
    (∀ j y, y ∈ U j → ∀ c : EuclideanSpace ℝ (Fin k),
      ℓ j (e j y c) = c ∧ P y (e j y c) = e j y c) ∧
    (∀ j y, y ∈ U j → Function.Injective (e j y)) ∧
    (∀ j j' y, y ∈ U j → y ∈ U j' →
      0 < LinearMap.det ((ℓ j').comp (e j y)
        : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)))

namespace Work.ThomBordism

noncomputable section

open Work.PTGeometric Work.Cohomology

/-- (Copied from `sourceLevelSet_orientationFamily.lean`.)  The local-generator property of a
relative class is invariant under an equality of the excluded sets.

PRIVATE: the same lemma exists under this name in `sourceLevelSet_orientationFamily.lean` and in
`levelSet_orientationFamily_of_collar.lean`; those modules are *above* the source construction while
this one is *below* it, so a consumer that imports this module together with either of those would
otherwise see a duplicate declaration.  No other module uses this copy. -/
private theorem exists_localGenerator_congr {W : TopCat} {E F : Set W} (h : E = F)
    (hv : ∃ w : (Work.Cohomology.relChains W E).homology 9,
      ∀ x (hx : x ∉ E), Submodule.span ℤ {(HomologicalComplex.homologyMap
        (Work.ThomBordism.relChainsInclPunct W E x hx) 9 w)} = ⊤) :
    ∃ w : (Work.Cohomology.relChains W F).homology 9,
      ∀ x (hx : x ∉ F), Submodule.span ℤ {(HomologicalComplex.homologyMap
        (Work.ThomBordism.relChainsInclPunct W F x hx) 9 w)} = ⊤ := by
  subst h
  exact hv

/-- **The orientation family of a coframed level set, for arbitrary data.** -/
theorem orientationFamily_of_coframingDataBase {n k : ℕ} {M : Type} [TopologicalSpace M]
    [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
      ((⊤ : ENat) : WithTop ENat) M]
    (P : M → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (v : M → EuclideanSpace ℝ (Fin n))
    (hPgr : ∀ x, P x ∈ Work.PTGeometric.Gr n k)
    (hvsm : ContMDiff (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ENat) : WithTop ENat) v)
    (hMem : ∀ x, P x (v x) = v x)
    (W : Set M) (hWcl : IsClosed W) (hW : W = {x : M | v x = 0}) (hWne : W.Nonempty)
    (hMdet : AmbientPositiveAtlas k M)
    (hlink : ∀ x ∈ W, Set.range (mfderiv (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) v x) = {z | P x z = z})
    (L : Work.PTGeometric.LocalLevelData k M W)
    (hcof : PlaneFieldCoframing n k M P W)
    (hcol : Nonempty (@Work.Surgery.Collar 8 (Work.PTGeometric.levelModel W hWcl L) inferInstance
      (Work.PTGeometric.Lvl.Setup.instChartedSpace
        (Work.PTGeometric.levelSetup W hWcl L)))) :
    letI : ChartedSpace (EuclideanHalfSpace 9) (Work.PTGeometric.levelSetup W hWcl L).Pre :=
      Work.PTGeometric.Lvl.Setup.instChartedSpace (Work.PTGeometric.levelSetup W hWcl L)
    ∃ γ : ∀ x : (Work.PTGeometric.levelSetup W hWcl L).Pre,
        x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary
          (Work.PTGeometric.levelSetup W hWcl L).Pre →
        Work.Orient.LocH (TopCat.of (Work.PTGeometric.levelSetup W hWcl L).Pre) 9 x,
      Work.Orient.IsHalfOrientationFamily 8 (TopCat.of (Work.PTGeometric.levelSetup W hWcl L).Pre) γ := by
  classical
  haveI hWne' : Nonempty ↥W := ⟨⟨hWne.choose, hWne.choose_spec⟩⟩
  haveI hWcompact : CompactSpace ↥W := isCompact_iff_compactSpace.mp hWcl.isCompact
  haveI hW2 : T2Space ↥W := inferInstance
  let Sbd : Set (Work.PTGeometric.levelSetup W hWcl L).Pre :=
    {x : ↥W | (x : M) ∈ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary M}
  have hbdL : (modelWithCornersEuclideanHalfSpace 9).boundary
      (Work.PTGeometric.levelSetup W hWcl L).Pre = Sbd := by
    refine Set.ext (fun x => ?_)
    exact Work.PTGeometric.Lvl.Setup.mem_boundary_iff (Work.PTGeometric.levelSetup W hWcl L) x
  have key : ∃ w : (Work.Cohomology.relChains
        (TopCat.of (Work.PTGeometric.levelSetup W hWcl L).Pre) Sbd).homology 9,
      ∀ x (hx : x ∉ Sbd), Submodule.span ℤ {(HomologicalComplex.homologyMap
        (Work.ThomBordism.relChainsInclPunct
          (TopCat.of (Work.PTGeometric.levelSetup W hWcl L).Pre) Sbd x hx) 9 w)} = ⊤ := by
    obtain ⟨I, hbdI, hmI, hdet⟩ := Work.ThomBordism.levelSet_positiveAtlas_of_coframing
      (k := k) (n := n) (M := M) hMdet P hPgr v hvsm hMem W hWcl hW hlink L hcof
    letI : ChartedSpace (EuclideanHalfSpace 9) ↥W := I
    haveI : IsManifold (modelWithCornersEuclideanHalfSpace 9)
        ((⊤ : ENat) : WithTop ENat) ↥W := hmI
    haveI : IsManifold (modelWithCornersEuclideanHalfSpace 9) 1 ↥W :=
      IsManifold.of_le (n := ((⊤ : ENat) : WithTop ENat)) (by simp)
    obtain ⟨γ₁, hγ₁⟩ := Work.PTGeometric.exists_halfOrientationFamily_of_det_pos 8
      (TopCat.of ↥W) hdet
    obtain ⟨cL⟩ := hcol
    have hcolI : @Work.Surgery.Collar 8 ↥W _ I :=
      Collar.of_instance_congr (hbdL.trans hbdI.symm) cL
    obtain ⟨w, -, hwgen, -⟩ :=
      Work.ThomBordism.exists_relFundClass_of_collar' (n := 8) hcolI γ₁ hγ₁
    exact exists_localGenerator_congr hbdI ⟨w, hwgen⟩
  obtain ⟨w, hw⟩ := exists_localGenerator_congr hbdL.symm key
  haveI : IsManifold (modelWithCornersEuclideanHalfSpace 9) 1
      (Work.PTGeometric.levelSetup W hWcl L).Pre :=
    IsManifold.of_le (n := ((⊤ : ENat) : WithTop ENat)) (by simp)
  exact ⟨fun x hx => HomologicalComplex.homologyMap
      (Work.ThomBordism.relChainsInclPunct
        (TopCat.of (Work.PTGeometric.levelSetup W hWcl L).Pre)
        ((modelWithCornersEuclideanHalfSpace 9).boundary
          (Work.PTGeometric.levelSetup W hWcl L).Pre) x hx) 9 w,
    Work.ThomBordism.isHalfOrientationFamily_relChainsInclPunct w hw⟩

end

end Work.ThomBordism
