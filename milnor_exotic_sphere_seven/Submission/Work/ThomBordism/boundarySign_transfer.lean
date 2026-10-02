import Mathlib
import Submission.Work.ThomBordism.stdHalfBallBoundarySign
import Submission.Work.PTGeometric.HOFXfer

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open CategoryTheory
open Work.PTGeometric.HOF

namespace Work.ThomBordism

/-! ## The transport of relative homology along a homeomorphism of pairs

These are the two elementary facts used by `boundarySign_transfer`: a map of pairs which has a
pointwise left inverse induces an *injective* map on the relative homology groups, and the transport
along a homeomorphism `Φb` of a single point is such a map (with left inverse the transport along
`Φb.symm`). -/

/-- **A map of pairs with a pointwise left inverse induces an injective map on relative homology.** -/
theorem relHmapOf_injective_of_leftInverse {X Y : TopCat} {n : ℕ} (f : X ⟶ Y) (g : Y ⟶ X)
    {K : Set X} {K' : Set Y} (hf : ∀ x, x ∉ K → f x ∉ K') (hg : ∀ y, y ∉ K' → g y ∉ K)
    (hgf : ∀ x : X, g (f x) = x) :
    Function.Injective (RelHmapOf n f K K' hf) := by
  have hpair : ∀ x : X, x ∉ K → (f ≫ g) x ∉ K := by
    intro x hx
    have hx' : (f ≫ g) x = x := hgf x
    rw [hx']; exact hx
  have hcomp : (RelHmapOf n g K' K hg).comp (RelHmapOf n f K K' hf) = LinearMap.id := by
    rw [RelHmapOf_comp (n := n) f g hf hg hpair]
    have h1 : (f ≫ g) = 𝟙 X := by
      apply TopCat.ext
      intro z
      exact hgf z
    rw [RelHmapOf_congr (n := n) h1 hpair (fun x hx => hx), RelHmapOf_id]
  intro a b hab
  have h1 : RelHmapOf n g K' K hg (RelHmapOf n f K K' hf a) = a := by
    have := LinearMap.congr_fun hcomp a; simpa using this
  have h2 : RelHmapOf n g K' K hg (RelHmapOf n f K K' hf b) = b := by
    have := LinearMap.congr_fun hcomp b; simpa using this
  rw [← h1, hab, h2]

/-- **Injectivity of the transport along a homeomorphism at a single point.** -/
theorem relHmapOf_homeomorph_point_injective {W : TopCat} {B : Set W} {Z : TopCat}
    (Φb : (TopCat.of ↥B) ≃ₜ Z) (m : ℕ) (y : ↥B) :
    Function.Injective
      (RelHmapOf m (TopCat.ofHom ⟨fun z : ↥B => Φb z, Φb.continuous⟩)
        ({y} : Set ↥B) ({Φb y} : Set Z)
        (fun z hz hzy => hz (Φb.injective hzy))) := by
  refine relHmapOf_injective_of_leftInverse (n := m)
    (f := TopCat.ofHom ⟨fun z : ↥B => Φb z, Φb.continuous⟩)
    (g := TopCat.ofHom ⟨fun z : Z => Φb.symm z, Φb.continuous_invFun⟩)
    (K := ({y} : Set ↥B)) (K' := ({Φb y} : Set Z))
    (fun z hz hzy => hz (Φb.injective hzy)) ?_ ?_
  · intro z hz hzy
    have hzy' : Φb.symm z = y := hzy
    exact hz (by rw [← hzy']; exact (Φb.apply_symm_apply z).symm)
  · exact fun z => Φb.symm_apply_apply z

theorem boundarySign_transfer (m : ℕ) (hm : 1 ≤ m)
    (W : TopCat) [CompactSpace W] [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (m + 1)) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace (m + 1)) 1 W]
    {B : Set W} (hB : (modelWithCornersEuclideanHalfSpace (m + 1)).boundary W = B)
    (Φ : W ≃ₜ (TopCat.of ↥(Work.ThomBordism.stdHalfBall (m + 1))))
    (hΦ : ∀ z : W, z ∈ B ↔ Φ z ∈ Work.ThomBordism.stdHalfBallBdry (m + 1))
    (Φb : (TopCat.of ↥B) ≃ₜ (TopCat.of ↥(Work.ThomBordism.stdHalfBallBdry (m + 1))))
    (hΦb : ∀ y : ↥B, Φb y = ⟨Φ y.1, (hΦ y.1).mp y.2⟩)
    (w : (Work.Cohomology.relChains W B).homology (m + 1))
    (ψ : (Work.Cohomology.singularChains ℤ (TopCat.of ↥B)).homology m)
    (w' : (Work.Cohomology.relChains (TopCat.of ↥(Work.ThomBordism.stdHalfBall (m + 1)))
        (Work.ThomBordism.stdHalfBallBdry (m + 1))).homology (m + 1))
    (ψ' : (Work.Cohomology.singularChains ℤ
        (TopCat.of ↥(Work.ThomBordism.stdHalfBallBdry (m + 1)))).homology m)
    (hw' : ∀ (x : ↥(Work.ThomBordism.stdHalfBall (m + 1)))
        (hx : x ∈ (Work.ThomBordism.stdIntChart (m + 1)).source),
      (HomologicalComplex.homologyMap
        (Work.Orient.relPunct (TopCat.of ↥(Work.ThomBordism.stdHalfBall (m + 1)))
          (Work.ThomBordism.stdHalfBallBdry (m + 1)) x
          (Work.ThomBordism.stdIntChart_source_notMem (m + 1) hx)) (m + 1)).hom w'
        = Work.ThomBordism.stdIntOrient m x hx)
    (hψ' : ∀ (y : ↥(Work.ThomBordism.stdHalfBallBdry (m + 1)))
        (hy : y ∈ (Work.ThomBordism.stdFlatChart m).source),
      Work.Orient.locClass (TopCat.of ↥(Work.ThomBordism.stdHalfBallBdry (m + 1))) m ψ' y
        = Work.ThomBordism.stdFlatGen m hm y hy)
    (hγw : ∀ (x : W) (hx : x ∉ B),
      Work.PTGeometric.HOF.RelHmapOf (m + 1)
          (TopCat.ofHom ⟨fun z : W => Φ z, Φ.continuous⟩) {x} {Φ x}
          (fun z hz hzx => hz (Φ.injective hzx))
        ((HomologicalComplex.homologyMap (Work.Orient.relPunct W B x hx) (m + 1)).hom w)
      = (HomologicalComplex.homologyMap
          (Work.Orient.relPunct (TopCat.of ↥(Work.ThomBordism.stdHalfBall (m + 1)))
            (Work.ThomBordism.stdHalfBallBdry (m + 1)) (Φ x) (fun hb => hx ((hΦ x).mpr hb)))
          (m + 1)).hom w')
    (hψ : ∀ (y : ↥B),
      Work.PTGeometric.HOF.RelHmapOf m
          (TopCat.ofHom ⟨fun z : ↥B => Φb z, Φb.continuous⟩) {y} {Φb y}
          (fun z hz hzy => hz (Φb.injective hzy))
        (Work.Orient.locClass (TopCat.of ↥B) m ψ y)
      = Work.Orient.locClass (TopCat.of ↥(Work.ThomBordism.stdHalfBallBdry (m + 1))) m ψ' (Φb y))
    (hPair : ∀ (y : ↥B),
      Work.PTGeometric.HOF.RelHmapOf m
          (TopCat.ofHom ⟨fun z : ↥B => Φb z, Φb.continuous⟩) {y} {Φb y}
          (fun z hz hzy => hz (Φb.injective hzy))
        (Work.Orient.locClass (TopCat.of ↥B) m
          ((Work.Cohomology.hPairδ W B m).hom w) y)
      = Work.Orient.locClass (TopCat.of ↥(Work.ThomBordism.stdHalfBallBdry (m + 1))) m
          ((Work.Cohomology.hPairδ (TopCat.of ↥(Work.ThomBordism.stdHalfBall (m + 1)))
            (Work.ThomBordism.stdHalfBallBdry (m + 1)) m).hom w') (Φb y)) :
    ∃ c : ℤ, (c = 1 ∨ c = -1) ∧
      ∀ (y : ↥B) (hy : Φb y ∈ (Work.ThomBordism.stdFlatChart m).source),
        Work.Orient.locClass (TopCat.of ↥B) m
          ((Work.Cohomology.hPairδ W B m).hom w) y
        = c • Work.Orient.locClass (TopCat.of ↥B) m ψ y := by
  classical
  obtain ⟨c, hc, hspec⟩ := stdHalfBallBoundarySign m hm
  refine ⟨c, hc, ?_⟩
  intro y hy
  have hinj := relHmapOf_homeomorph_point_injective (B := B)
    (Z := TopCat.of ↥(stdHalfBallBdry (m + 1))) Φb m y
  have key : RelHmapOf m (TopCat.ofHom ⟨fun z : ↥B => Φb z, Φb.continuous⟩)
        ({y} : Set ↥B) ({Φb y} : Set ↥(stdHalfBallBdry (m + 1)))
        (fun z hz hzy => hz (Φb.injective hzy))
        (Work.Orient.locClass (TopCat.of ↥B) m
          ((Work.Cohomology.hPairδ W B m).hom w) y)
      = RelHmapOf m (TopCat.ofHom ⟨fun z : ↥B => Φb z, Φb.continuous⟩)
        ({y} : Set ↥B) ({Φb y} : Set ↥(stdHalfBallBdry (m + 1)))
        (fun z hz hzy => hz (Φb.injective hzy))
        (c • Work.Orient.locClass (TopCat.of ↥B) m ψ y) := by
    calc RelHmapOf m (TopCat.ofHom ⟨fun z : ↥B => Φb z, Φb.continuous⟩)
          ({y} : Set ↥B) ({Φb y} : Set ↥(stdHalfBallBdry (m + 1)))
          (fun z hz hzy => hz (Φb.injective hzy))
          (Work.Orient.locClass (TopCat.of ↥B) m
            ((Work.Cohomology.hPairδ W B m).hom w) y)
        = Work.Orient.locClass (TopCat.of ↥(stdHalfBallBdry (m + 1))) m
            ((Work.Cohomology.hPairδ (TopCat.of ↥(Work.ThomBordism.stdHalfBall (m + 1)))
              (Work.ThomBordism.stdHalfBallBdry (m + 1)) m).hom w') (Φb y) := hPair y
      _ = c • Work.ThomBordism.stdFlatGen m hm (Φb y) hy := hspec w' hw' (Φb y) hy
      _ = c • Work.Orient.locClass (TopCat.of ↥(stdHalfBallBdry (m + 1))) m ψ' (Φb y) := by
            rw [hψ' (Φb y) hy]
      _ = c • RelHmapOf m (TopCat.ofHom ⟨fun z : ↥B => Φb z, Φb.continuous⟩)
            ({y} : Set ↥B) ({Φb y} : Set ↥(stdHalfBallBdry (m + 1)))
            (fun z hz hzy => hz (Φb.injective hzy))
            (Work.Orient.locClass (TopCat.of ↥B) m ψ y) := by
            rw [hψ y]
      _ = RelHmapOf m (TopCat.ofHom ⟨fun z : ↥B => Φb z, Φb.continuous⟩)
            ({y} : Set ↥B) ({Φb y} : Set ↥(stdHalfBallBdry (m + 1)))
            (fun z hz hzy => hz (Φb.injective hzy))
            (c • Work.Orient.locClass (TopCat.of ↥B) m ψ y) := by
            exact (map_zsmul (f := RelHmapOf m
              (TopCat.ofHom ⟨fun z : ↥B => Φb z, Φb.continuous⟩)
              ({y} : Set ↥B) ({Φb y} : Set ↥(stdHalfBallBdry (m + 1)))
              (fun z hz hzy => hz (Φb.injective hzy)))
              c (Work.Orient.locClass (TopCat.of ↥B) m ψ y)).symm
  exact hinj key

end Work.ThomBordism
