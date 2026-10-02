import Submission.Work.Tubular.TubeClass.Reduction
import Submission.Work.Tubular.TubeClass.localisationCollapseClassSpanTop
import Submission.Work.Tubular.TubeClass.punctComplTopHomologyVanishing

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Tubular

theorem tubeCollapseClass_span_top {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt] {k : ℕ}
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (q : Work.Tubular.NormalSphSub E ε)
    (hU : IsCompact C.U) {R : ℝ} (hR : 0 ≤ R)
    (hbox : ∀ y ∈ C.U, ∀ i : Fin (8 + k), |y i| < R)
    (g : C(OnePoint (Euc (8 + k)), OnePoint (NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    (hg2 : ∀ y, y ∈ C.openTube → g (OnePoint.some y)
      = OnePoint.some (normalBlowUp E ε (C.inv y))) :
    Submodule.span ℤ
      { ((HomologicalComplex.homologyMap (CategoryTheory.Limits.cokernel.π
          (Work.Cohomology.inclChains (TopCat.of (OnePoint (NormalTotal E)))
            (onePointNonzero E))) (8 + k))
          (Work.Stems.hurewiczChain (8 + k) (by omega) OnePoint.infty
            (tubeGenLoopOnePoint C g hg hR hbox))) } = ⊤ := by
  classical
  obtain ⟨v₀⟩ := (inferInstance : Nonempty V.pt)
  have hA := Work.Tubular.TubeClass.punctComplTopHomologyVanishing E v₀
  have hB := Work.Tubular.TubeClass.localisationCollapseClassSpanTop C hU hR hbox g hg hg2 v₀
  have hspan := span_hurewiczChain_top_of_localisation C hU hR hbox g hg hg2 v₀ hA hB
  have hbij := Work.Cohomology.homologyMap_cokernel_pi_bijective_of_isZero
    (TopCat.of (OnePoint (NormalTotal E))) (onePointNonzero E) (8 + k) (by omega)
    (isZero_homology_onePointNonzero E (8 + k) (by omega))
    (isZero_homology_onePointNonzero E (8 + k - 1) (by omega))
  have hsurj : Function.Surjective ⇑(ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains
        (TopCat.of (OnePoint (NormalTotal E))) (onePointNonzero E))) (8 + k))) :=
    hbij.surjective
  have key : Submodule.map (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains
        (TopCat.of (OnePoint (NormalTotal E))) (onePointNonzero E))) (8 + k)))
      (Submodule.span ℤ
        ({(Work.Stems.hurewiczChain (8 + k) (by omega) OnePoint.infty
          (tubeGenLoopOnePoint C g hg hR hbox))} : Set _)) = ⊤ := by
    rw [hspan, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr hsurj
  rwa [Submodule.map_span, Set.image_singleton] at key

end Work.Tubular
