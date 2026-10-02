import Mathlib
import Submission.Work.ThomBordism.boundarySign_chartLocal
import Submission.Work.PTGeometric.FlatSource
import Submission.Work.ThomBordism.localBoundaryTransfer_congr

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The uniform boundary sign: the transfer of the chart-local boundary sign along a map of pairs

This file contains the *transport* step of the proof of
`Work.ThomBordism.boundarySign_chartLocal_univ`: if the analogue of the target's equation holds for a
second instance `(W',∂W')` with a constant `c`, and the map of pairs `(Φ, Φb)` carries the chart
generators of the first instance to those of the second (in the precise sense of the hypotheses
below), then the equation holds for the first instance with the *same* constant `c`.

The content is the naturality of `hPairδ` and of the local classes (`locClass_hPairDelta_natural_aux`)
together with the fact that the local class of `hPairδ` is determined by the localisation of the class
at a single interior point of a half-ball piece (`locClass_hPairDelta_eq_of_localClass_eq`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open CategoryTheory
open scoped Manifold
open Work.PTGeometric.HOF

namespace Work.ThomBordism

/-- **Transfer of the boundary-sign equation along a map of pairs.**

If the analogue of the target's equation holds for a second instance `(W',∂W')` with the constant
`c`, and the chart generators of `W` are carried by the map of pairs `(Φ, Φb)` to those of `W'`, then
the equation holds for `(W,∂W)` with the same constant `c`.  The point of `W'` at which everything is
stated is the image `Φb ⟨y,hy⟩` of the base point, and the interior point is `Φ x₀`. -/
theorem boundarySign_transfer_of_chartCorr (n : ℕ) (hn : 1 ≤ n) (c : ℤ)
    (W : TopCat) [CompactSpace W] [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 W]
    {y : W} (hy : y ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    (e : OpenPartialHomeomorph W (Euc (n + 1)))
    (heS : y ∈ e.source)
    (eb : OpenPartialHomeomorph ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) (Euc n))
    (hyeb : (⟨y, hy⟩ : ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)) ∈ eb.source)
    {r : ℝ} (hr : 0 < r) (hgood : Work.Orient.halfBallGood (n + 1) W y r)
    {x₀ : W} (hx₀ : x₀ ∈ Work.Orient.halfBallPiece (n + 1) W y r)
    (hx₀int : x₀ ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    (hx₀e : x₀ ∈ e.source)
    (w : (Work.Cohomology.relChains W
      ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)).homology (n + 1))
    (hw : (HomologicalComplex.homologyMap
          (Work.Orient.relPunct W ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
            x₀ hx₀int) (n + 1)).hom w
        = chartTr e x₀ hx₀e (eucFam (n + 1) (by omega) (e x₀)))
    (W' : TopCat) [CompactSpace W'] [T2Space W']
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W']
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 W']
    (Φ : W ⟶ W') (Φb : TopCat.of ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) ⟶
      TopCat.of ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W'))
    (hΦb : ∀ z : ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W),
      (Φb z : W') = Φ z.1)
    (hpairb : ∀ z : ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W),
      z ∉ ({⟨y, hy⟩} : Set ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)) →
      Φb z ∉ ({Φb ⟨y, hy⟩} : Set ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W')))
    (e' : OpenPartialHomeomorph W' (Euc (n + 1)))
    (eb' : OpenPartialHomeomorph ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W') (Euc n))
    (hyeb' : Φb ⟨y, hy⟩ ∈ eb'.source)
    {r' : ℝ} (hr' : 0 < r')
    (hgood' : Work.Orient.halfBallGood (n + 1) W' (↑(Φb ⟨y, hy⟩)) r')
    (hx₀' : Φ x₀ ∈ Work.Orient.halfBallPiece (n + 1) W' (↑(Φb ⟨y, hy⟩)) r')
    (hx₀int' : Φ x₀ ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W')
    (hx₀e' : Φ x₀ ∈ e'.source)
    (w' : (Work.Cohomology.relChains W'
      ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W')).homology (n + 1))
    (hw' : (HomologicalComplex.homologyMap
          (Work.Orient.relPunct W' ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W')
            (Φ x₀) hx₀int') (n + 1)).hom w'
        = chartTr e' (Φ x₀) hx₀e' (eucFam (n + 1) (by omega) (e' (Φ x₀))))
    (hEq' : Work.Orient.locClass
        (TopCat.of ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W')) n
        ((Work.Cohomology.hPairδ W'
          ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W') n).hom w') (Φb ⟨y, hy⟩)
      = c • chartTr (W := TopCat.of
            ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W')) eb' (Φb ⟨y, hy⟩) hyeb'
          (eucFam n hn (eb' (Φb ⟨y, hy⟩))))
    (hΦinj : ∀ z : W, Φ z = Φ x₀ → z = x₀)
    (hInt : RelHmapOf (n + 1) Φ ({x₀} : Set W) ({Φ x₀} : Set W')
        (fun z hz hzx => hz (hΦinj z hzx))
        (chartTr e x₀ hx₀e (eucFam (n + 1) (by omega) (e x₀)))
      = chartTr e' (Φ x₀) hx₀e' (eucFam (n + 1) (by omega) (e' (Φ x₀))))
    (hBd : RelHmapOf n Φb
        ({⟨y, hy⟩} : Set ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W))
        ({Φb ⟨y, hy⟩} : Set ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W')) hpairb
        (chartTr (W := TopCat.of ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W))
          eb ⟨y, hy⟩ hyeb (eucFam n hn (eb ⟨y, hy⟩)))
      = chartTr (W := TopCat.of ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W'))
          eb' (Φb ⟨y, hy⟩) hyeb' (eucFam n hn (eb' (Φb ⟨y, hy⟩))))
    (hinjb : Function.Injective (RelHmapOf n Φb
        ({⟨y, hy⟩} : Set ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W))
        ({Φb ⟨y, hy⟩} : Set ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W')) hpairb)) :
    Work.Orient.locClass
        (TopCat.of ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)) n
        ((Work.Cohomology.hPairδ W
          ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) n).hom w) ⟨y, hy⟩
      = c • chartTr (W := TopCat.of
            ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)) eb ⟨y, hy⟩ hyeb
          (eucFam n hn (eb ⟨y, hy⟩)) := by
  classical
  -- the compatibility of the map of pairs
  have hwComp : Work.Cohomology.subtypeIncl W
      ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) ≫ Φ
      = Φb ≫ Work.Cohomology.subtypeIncl W'
        ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W') := by
    apply TopCat.ext
    intro z
    exact (hΦb z).symm
  have hpairx : ∀ z : W, z ∉ ({x₀} : Set W) → Φ z ∉ ({Φ x₀} : Set W') :=
    fun z hz hzx => hz (hΦinj z hzx)
  have hγ : RelHmapOf (n + 1) Φ ({x₀} : Set W) ({Φ x₀} : Set W') hpairx
      ((HomologicalComplex.homologyMap
        (Work.Orient.relPunct W ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
          x₀ hx₀int) (n + 1)).hom w)
      = (HomologicalComplex.homologyMap
        (Work.Orient.relPunct W' ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W')
          (Φ x₀) hx₀int') (n + 1)).hom w' := by
    rw [hw, hInt, hw']
  -- the punctured localisations of `Φ_* w` and `w'` agree
  have hrel : (HomologicalComplex.homologyMap
        (Work.Orient.relPunct W' ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W')
          (Φ x₀) hx₀int') (n + 1)).hom
        ((HomologicalComplex.homologyMap
          (Work.Cohomology.relChainsMapOf W W'
            ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
            ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W') Φ Φb hwComp)
          (n + 1)).hom w)
      = (HomologicalComplex.homologyMap
        (Work.Orient.relPunct W' ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W')
          (Φ x₀) hx₀int') (n + 1)).hom w' := by
    have hsq := Work.ThomBordism.relChainsMapOf_relPunct_aux
      ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
      ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W') Φ Φb hwComp
      hx₀int hx₀int' (fun z hz hzx => hz (hΦinj z hzx))
    have h2 : (HomologicalComplex.homologyMap
          (Work.Orient.relPunct W' ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W')
            (Φ x₀) hx₀int') (n + 1)).hom
          ((HomologicalComplex.homologyMap
            (Work.Cohomology.relChainsMapOf W W'
              ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
              ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W') Φ Φb hwComp)
            (n + 1)).hom w)
        = (HomologicalComplex.homologyMap
            ((Work.Cohomology.relChainsMapOf W W'
              ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
              ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W') Φ Φb hwComp)
              ≫ (Work.Orient.relPunct W'
                ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W')
                (Φ x₀) hx₀int'))
            (n + 1)).hom w := by
      rw [← ModuleCat.comp_apply, ← HomologicalComplex.homologyMap_comp]
    rw [h2, hsq, HomologicalComplex.homologyMap_comp, ModuleCat.comp_apply]
    exact hγ
  -- the two classes have the same interior localisation, hence the same boundary local class
  have hdet := Work.ThomBordism.locClass_hPairDelta_eq_of_localClass_eq (n := n) W' rfl
    (Φb ⟨y, hy⟩).2 hr' hgood' hx₀' hx₀int' hrel
  -- naturality of the boundary local class, at the image point
  have hnat := Work.ThomBordism.locClass_hPairDelta_natural_aux
    (A := (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    (A' := (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W') Φ Φb hwComp hy hpairb n w
  have key : RelHmapOf n Φb
        ({⟨y, hy⟩} : Set ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W))
        ({Φb ⟨y, hy⟩} : Set ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W')) hpairb
        (Work.Orient.locClass (TopCat.of
          ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)) n
          ((Work.Cohomology.hPairδ W
            ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) n).hom w) ⟨y, hy⟩)
      = RelHmapOf n Φb
        ({⟨y, hy⟩} : Set ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W))
        ({Φb ⟨y, hy⟩} : Set ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W')) hpairb
        (c • chartTr (W := TopCat.of
            ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)) eb ⟨y, hy⟩ hyeb
          (eucFam n hn (eb ⟨y, hy⟩))) := by
    rw [hnat, hdet, hEq', map_zsmul, hBd]
  exact hinjb key

end Work.ThomBordism
