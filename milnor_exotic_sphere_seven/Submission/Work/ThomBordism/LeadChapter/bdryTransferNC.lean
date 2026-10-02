import Mathlib
import Submission.Work.ThomBordism.boundarySign_transfer_bdry

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open CategoryTheory

namespace Work.ThomBordism.LeadChapter

theorem bdryTransferNC (n : ℕ) (hn : 1 ≤ n) (c : ℤ)
    (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 W]
    {B : Set W} {y : W} (hy : y ∈ B)
    (eb : OpenPartialHomeomorph ↥B (Work.PTGeometric.HOF.Euc n))
    (hyeb : (⟨y, hy⟩ : ↥B) ∈ eb.source)
    {x₀ : W} (hx₀int : x₀ ∉ B)
    (w : (Work.Cohomology.relChains W B).homology (n + 1))
    (W' : TopCat) [CompactSpace W'] [T2Space W']
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W']
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 W']
    {B' : Set W'} (hB' : (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W' = B')
    (Φ : W ⟶ W') (Φb : TopCat.of ↥B ⟶ TopCat.of ↥B')
    (hΦb : ∀ z : ↥B, (Φb z : W') = Φ z.1)
    (hpairb : ∀ z : ↥B, z ∉ ({⟨y, hy⟩} : Set ↥B) →
      Φb z ∉ ({Φb ⟨y, hy⟩} : Set ↥B'))
    (hΦinj : ∀ z : W, Φ z = Φ x₀ → z = x₀)
    (eb' : OpenPartialHomeomorph ↥B' (Work.PTGeometric.HOF.Euc n))
    (hyeb' : Φb ⟨y, hy⟩ ∈ eb'.source)
    {r' : ℝ} (hr' : 0 < r')
    (hgood' : Work.Orient.halfBallGood (n + 1) W' (↑(Φb ⟨y, hy⟩)) r')
    (hx₀' : Φ x₀ ∈ Work.Orient.halfBallPiece (n + 1) W' (↑(Φb ⟨y, hy⟩)) r')
    (hx₀int' : Φ x₀ ∉ B')
    (w' : (Work.Cohomology.relChains W' B').homology (n + 1))
    (hγ : Work.PTGeometric.HOF.RelHmapOf (n + 1) Φ ({x₀} : Set W) ({Φ x₀} : Set W')
        (fun z hz hzx => hz (hΦinj z hzx))
        ((HomologicalComplex.homologyMap
          (Work.Orient.relPunct W B x₀ hx₀int) (n + 1)).hom w)
      = (HomologicalComplex.homologyMap
          (Work.Orient.relPunct W' B' (Φ x₀) hx₀int') (n + 1)).hom w')
    (hChartB : Work.PTGeometric.HOF.RelHmapOf n Φb ({⟨y, hy⟩} : Set ↥B)
        ({Φb ⟨y, hy⟩} : Set ↥B') hpairb
        (Work.PTGeometric.HOF.chartTr (W := TopCat.of ↥B) eb ⟨y, hy⟩ hyeb
          (Work.PTGeometric.HOF.eucFam n hn (eb ⟨y, hy⟩)))
      = Work.PTGeometric.HOF.chartTr (W := TopCat.of ↥B') eb' (Φb ⟨y, hy⟩) hyeb'
          (Work.PTGeometric.HOF.eucFam n hn (eb' (Φb ⟨y, hy⟩))))
    (hEq' : Work.Orient.locClass (TopCat.of ↥B') n
        ((Work.Cohomology.hPairδ W' B' n).hom w') (Φb ⟨y, hy⟩)
      = c • Work.PTGeometric.HOF.chartTr (W := TopCat.of ↥B') eb' (Φb ⟨y, hy⟩) hyeb'
          (Work.PTGeometric.HOF.eucFam n hn (eb' (Φb ⟨y, hy⟩))))
    (hinjb : Function.Injective (Work.PTGeometric.HOF.RelHmapOf n Φb ({⟨y, hy⟩} : Set ↥B)
        ({Φb ⟨y, hy⟩} : Set ↥B') hpairb)) :
    Work.Orient.locClass (TopCat.of ↥B) n ((Work.Cohomology.hPairδ W B n).hom w) ⟨y, hy⟩
      = c • Work.PTGeometric.HOF.chartTr (W := TopCat.of ↥B) eb ⟨y, hy⟩ hyeb
          (Work.PTGeometric.HOF.eucFam n hn (eb ⟨y, hy⟩)) := by
  classical
  -- the compatibility of the pair map `(Φ, Φb)`
  have hw : Work.Cohomology.subtypeIncl W B ≫ Φ = Φb ≫ Work.Cohomology.subtypeIncl W' B' := by
    apply TopCat.ext
    intro z
    exact (hΦb z).symm
  -- the transported relative fundamental class
  let wtilde : (Work.Cohomology.relChains W' B').homology (n + 1) :=
    (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMapOf W W' B B' Φ Φb hw) (n + 1)).hom w
  -- the punctured localisations of `wtilde` and `w'` at `Φ x₀` agree
  have hPunct : (HomologicalComplex.homologyMap (Work.Orient.relPunct W' B' (Φ x₀) hx₀int')
        (n + 1)).hom wtilde
      = (HomologicalComplex.homologyMap (Work.Orient.relPunct W' B' (Φ x₀) hx₀int')
          (n + 1)).hom w' := by
    have hsq := relChainsMapOf_relPunct_aux B B' Φ Φb hw hx₀int hx₀int'
      (fun z hz hzx => hz (hΦinj z hzx))
    have h2 : (HomologicalComplex.homologyMap (Work.Orient.relPunct W' B' (Φ x₀) hx₀int')
          (n + 1)).hom
          ((HomologicalComplex.homologyMap
            (Work.Cohomology.relChainsMapOf W W' B B' Φ Φb hw) (n + 1)).hom w)
        = (HomologicalComplex.homologyMap
            ((Work.Cohomology.relChainsMapOf W W' B B' Φ Φb hw)
              ≫ (Work.Orient.relPunct W' B' (Φ x₀) hx₀int')) (n + 1)).hom w := by
      rw [← ModuleCat.comp_apply, ← HomologicalComplex.homologyMap_comp]
    rw [h2, hsq, HomologicalComplex.homologyMap_comp, ModuleCat.comp_apply]
    exact hγ
  -- hence the boundary local classes of `hPairδ wtilde` and `hPairδ w'` agree at `Φb ⟨y, hy⟩`
  have hloc := Work.ThomBordism.locClass_hPairDelta_eq_of_localClass_eq (n := n) W' hB'
    (Φb ⟨y, hy⟩).2 hr' hgood' hx₀' hx₀int' hPunct
  have hloc' : Work.Orient.locClass (TopCat.of ↥B') n
        ((Work.Cohomology.hPairδ W' B' n).hom wtilde) (Φb ⟨y, hy⟩)
      = Work.Orient.locClass (TopCat.of ↥B') n
        ((Work.Cohomology.hPairδ W' B' n).hom w') (Φb ⟨y, hy⟩) := hloc
  -- naturality of the local class of `hPairδ` under the map of pairs `(Φ, Φb)`
  have hnat := locClass_hPairDelta_natural_aux (A := B) (A' := B') Φ Φb hw hy hpairb n w
  -- the key identity: the transport of the two sides of the claim agree
  have key : Work.PTGeometric.HOF.RelHmapOf n Φb ({⟨y, hy⟩} : Set ↥B)
        ({Φb ⟨y, hy⟩} : Set ↥B') hpairb
        (Work.Orient.locClass (TopCat.of ↥B) n ((Work.Cohomology.hPairδ W B n).hom w) ⟨y, hy⟩)
      = Work.PTGeometric.HOF.RelHmapOf n Φb ({⟨y, hy⟩} : Set ↥B)
        ({Φb ⟨y, hy⟩} : Set ↥B') hpairb
        (c • Work.PTGeometric.HOF.chartTr (W := TopCat.of ↥B) eb ⟨y, hy⟩ hyeb
          (Work.PTGeometric.HOF.eucFam n hn (eb ⟨y, hy⟩))) := by
    rw [map_zsmul, hChartB, hnat, hloc', hEq']
  exact hinjb key

end Work.ThomBordism.LeadChapter
