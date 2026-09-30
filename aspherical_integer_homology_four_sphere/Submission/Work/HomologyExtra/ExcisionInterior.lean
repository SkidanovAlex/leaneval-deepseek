import Mathlib
import Submission.Work.Homology.Corollaries
import Submission.Work.Cohomology.localHomology
import Submission.Work.Cohomology.smallChains_homology_iso_int
import Submission.Work.Cohomology.excisionAux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Excision for a cover by interiors, in the form used below

The ported chapter proves the small-simplices theorem for a cover whose *interiors* cover the space
(`Work.Cohomology.smallChains_homology_iso_int`), and deduces the open-cover form of excision
(`Work.Cohomology.excision_relChainsMap_isIso`, for `U, A` open).  The pair used in this
development, `(∂Δⁿ⁺¹, B)` with `B = simplexStar n` the closed star of the last vertex, has a *closed*
second component, so we record the same five-lemma argument with the hypothesis
`interior A ∪ interior U = univ` instead of openness.
-/

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.HomologyExtra

noncomputable section

/-- **Excision (interior form)**: if `interior A ∪ interior U = univ`, the inclusion of pairs
`(U, A ∩ U) → (X, A)` is a homology isomorphism, i.e. the induced map on relative chain complexes
`Work.Cohomology.relChainsMap X U A` is a quasi-isomorphism. -/
theorem isIso_homologyMap_relChainsMap_of_interior (X : TopCat) (U A : Set X)
    (hcov : interior A ∪ interior U = Set.univ) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap X U A) n) := by
  let A' : Set U := {x : U | (x : X) ∈ A}
  let u : Work.Cohomology.singularChains ℤ (TopCat.of A) ⟶ Work.Cohomology.smallChains A U :=
    Work.Cohomology.smallOfU A U
  let w : Work.Cohomology.smallChains A U ⟶ Work.Cohomology.singularChains ℤ X :=
    Work.Cohomology.smallToSing A U
  have huw : u ≫ w = Work.Cohomology.inclChains X A :=
    Work.Cohomology.smallOfU_comp_smallToSing A U
  have huw' : u ≫ w = (𝟙 (Work.Cohomology.singularChains ℤ (TopCat.of A))) ≫
      Work.Cohomology.inclChains X A := by
    rw [Category.id_comp]; exact huw
  let S₁ : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
    ShortComplex.mk u (cokernel.π u) (cokernel.condition u)
  let S₂ : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) := Work.Cohomology.hPairShort X A
  have hS₁ : S₁.ShortExact :=
    { exact := ShortComplex.exact_cokernel u
      mono_f := Work.Cohomology.mono_smallOfU A U
      epi_g := inferInstance }
  have hS₂ : S₂.ShortExact := Work.Cohomology.hPairShort_shortExact X A
  let τ₃ : S₁.X₃ ⟶ S₂.X₃ := cokernel.map u (Work.Cohomology.inclChains X A) (𝟙 _) w huw'
  have hcomp1 : (𝟙 S₁.X₁) ≫ S₂.f = S₁.f ≫ w := by
    show (𝟙 (Work.Cohomology.singularChains ℤ (TopCat.of A))) ≫ Work.Cohomology.inclChains X A
      = u ≫ w
    rw [Category.id_comp]; exact huw.symm
  have hcomp2 : w ≫ S₂.g = S₁.g ≫ τ₃ := by
    show w ≫ cokernel.π (Work.Cohomology.inclChains X A)
      = cokernel.π u ≫ cokernel.map u (Work.Cohomology.inclChains X A) (𝟙 _) w huw'
    exact (Work.Cohomology.cokernel_π_map u (Work.Cohomology.inclChains X A) (𝟙 _) w huw').symm
  let φ : S₁ ⟶ S₂ := ShortComplex.homMk (𝟙 S₁.X₁) w τ₃ hcomp1 hcomp2
  have hφ₂ : φ.τ₂ = w := rfl
  have hφ₁ : φ.τ₁ = 𝟙 S₁.X₁ := rfl
  have hτ₃ : IsIso (HomologicalComplex.homologyMap τ₃ n) := by
    refine HomologicalComplex.HomologySequence.isIso_homologyMap_τ₃ φ hS₁ hS₂ n ?_ ?_ ?_ ?_
    · rw [hφ₁, HomologicalComplex.homologyMap_id]; infer_instance
    · rw [hφ₂]; exact Work.Cohomology.smallChains_homology_iso_int A U hcov n
    · intro j _
      rw [hφ₁, HomologicalComplex.homologyMap_id]; infer_instance
    · intro j _
      rw [hφ₂]
      haveI := Work.Cohomology.smallChains_homology_iso_int A U hcov j
      infer_instance
  obtain ⟨e, he⟩ := Work.Cohomology.cokerSmallOfU_iso_relChains_compat X A U
  have key : cokernel.π (Work.Cohomology.smallOfU A U) ≫ τ₃
      = w ≫ cokernel.π (Work.Cohomology.inclChains X A) :=
    Work.Cohomology.cokernel_π_map u (Work.Cohomology.inclChains X A) (𝟙 _) w huw'
  have hfac : Work.Cohomology.relChainsMap X U A = e.hom ≫ τ₃ := by
    apply (cancel_epi (cokernel.π (Work.Cohomology.inclChains (TopCat.of U) A'))).1
    calc cokernel.π (Work.Cohomology.inclChains (TopCat.of U) A')
          ≫ Work.Cohomology.relChainsMap X U A
        = Work.Cohomology.chainMap ℤ (TopCat.of U) X (Work.Cohomology.subtypeIncl X U)
            ≫ cokernel.π (Work.Cohomology.inclChains X A) :=
          Work.Cohomology.cokernel_π_relChainsMap X U A
      _ = Work.Cohomology.inclChains X U ≫ cokernel.π (Work.Cohomology.inclChains X A) := rfl
      _ = (Work.Cohomology.smallOfV A U ≫ w) ≫ cokernel.π (Work.Cohomology.inclChains X A) := by
            rw [Work.Cohomology.smallOfV_comp_smallToSing]
      _ = Work.Cohomology.smallOfV A U
            ≫ (w ≫ cokernel.π (Work.Cohomology.inclChains X A)) := Category.assoc _ _ _
      _ = Work.Cohomology.smallOfV A U
            ≫ (cokernel.π (Work.Cohomology.smallOfU A U) ≫ τ₃) := by rw [key]
      _ = (Work.Cohomology.smallOfV A U
            ≫ cokernel.π (Work.Cohomology.smallOfU A U)) ≫ τ₃ := (Category.assoc _ _ _).symm
      _ = (cokernel.π (Work.Cohomology.inclChains (TopCat.of U) A') ≫ e.hom) ≫ τ₃ := by rw [he]
      _ = cokernel.π (Work.Cohomology.inclChains (TopCat.of U) A') ≫ (e.hom ≫ τ₃) :=
          Category.assoc _ _ _
  rw [hfac, HomologicalComplex.homologyMap_comp]
  haveI : IsIso (HomologicalComplex.homologyMap e.hom n) :=
    Functor.map_isIso (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n)
      e.hom
  infer_instance

/-- **Excision (interior form), for the map induced on relative chains of a pair map.**  If
`interior A ∪ interior U = univ` and `Φ : (U, A ∩ U) → (X, A)` is the inclusion of pairs (in the
sense that `Φ.hom` is the inclusion `U ↪ X`), then the map induced by `Φ` on relative chains is a
quasi-isomorphism.  This is the form used for the inclusion `(S, B ∩ S) → (X, B)`. -/
theorem isIso_relChainMap_homologyMap_of_interior (X : TopCat) (U A : Set X)
    (hcov : interior A ∪ interior U = Set.univ)
    (Φ : Work.Homology.PairHom (TopCat.of U) X {x : ↥U | (x : X) ∈ A} A)
    (hΦ : Φ.hom = Work.Cohomology.subtypeIncl X U) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (Work.Homology.relChainMap Work.Homology.ZMod Φ) n) := by
  let A' : Set U := {x : U | (x : X) ∈ A}
  let u : Work.Cohomology.singularChains ℤ (TopCat.of A) ⟶ Work.Cohomology.smallChains A U :=
    Work.Cohomology.smallOfU A U
  let w : Work.Cohomology.smallChains A U ⟶ Work.Cohomology.singularChains ℤ X :=
    Work.Cohomology.smallToSing A U
  have huw : u ≫ w = Work.Cohomology.inclChains X A :=
    Work.Cohomology.smallOfU_comp_smallToSing A U
  have huw' : u ≫ w = (𝟙 (Work.Cohomology.singularChains ℤ (TopCat.of A))) ≫
      Work.Cohomology.inclChains X A := by
    rw [Category.id_comp]; exact huw
  let S₁ : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
    ShortComplex.mk u (cokernel.π u) (cokernel.condition u)
  let S₂ : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) := Work.Cohomology.hPairShort X A
  have hS₁ : S₁.ShortExact :=
    { exact := ShortComplex.exact_cokernel u
      mono_f := Work.Cohomology.mono_smallOfU A U
      epi_g := inferInstance }
  have hS₂ : S₂.ShortExact := Work.Cohomology.hPairShort_shortExact X A
  let τ₃ : S₁.X₃ ⟶ S₂.X₃ := cokernel.map u (Work.Cohomology.inclChains X A) (𝟙 _) w huw'
  have hcomp1 : (𝟙 S₁.X₁) ≫ S₂.f = S₁.f ≫ w := by
    show (𝟙 (Work.Cohomology.singularChains ℤ (TopCat.of A))) ≫ Work.Cohomology.inclChains X A
      = u ≫ w
    rw [Category.id_comp]; exact huw.symm
  have hcomp2 : w ≫ S₂.g = S₁.g ≫ τ₃ := by
    show w ≫ cokernel.π (Work.Cohomology.inclChains X A)
      = cokernel.π u ≫ cokernel.map u (Work.Cohomology.inclChains X A) (𝟙 _) w huw'
    exact (Work.Cohomology.cokernel_π_map u (Work.Cohomology.inclChains X A) (𝟙 _) w huw').symm
  let φ : S₁ ⟶ S₂ := ShortComplex.homMk (𝟙 S₁.X₁) w τ₃ hcomp1 hcomp2
  have hφ₂ : φ.τ₂ = w := rfl
  have hφ₁ : φ.τ₁ = 𝟙 S₁.X₁ := rfl
  have hτ₃ : IsIso (HomologicalComplex.homologyMap τ₃ n) := by
    refine HomologicalComplex.HomologySequence.isIso_homologyMap_τ₃ φ hS₁ hS₂ n ?_ ?_ ?_ ?_
    · rw [hφ₁, HomologicalComplex.homologyMap_id]; infer_instance
    · rw [hφ₂]; exact Work.Cohomology.smallChains_homology_iso_int A U hcov n
    · intro j _
      rw [hφ₁, HomologicalComplex.homologyMap_id]; infer_instance
    · intro j _
      rw [hφ₂]
      haveI := Work.Cohomology.smallChains_homology_iso_int A U hcov j
      infer_instance
  obtain ⟨e, he⟩ := Work.Cohomology.cokerSmallOfU_iso_relChains_compat X A U
  have key : cokernel.π (Work.Cohomology.smallOfU A U) ≫ τ₃
      = w ≫ cokernel.π (Work.Cohomology.inclChains X A) :=
    Work.Cohomology.cokernel_π_map u (Work.Cohomology.inclChains X A) (𝟙 _) w huw'
  have hfac : Work.Homology.relChainMap Work.Homology.ZMod Φ = e.hom ≫ τ₃ := by
    apply (cancel_epi (cokernel.π (Work.Cohomology.inclChains (TopCat.of U) A'))).1
    calc cokernel.π (Work.Cohomology.inclChains (TopCat.of U) A')
          ≫ Work.Homology.relChainMap Work.Homology.ZMod Φ
        = Work.Homology.singChainMap Work.Homology.ZMod Φ.hom
            ≫ cokernel.π (Work.Cohomology.inclChains X A) := by
          show Work.Homology.relProj Work.Homology.ZMod (TopCat.of U) A'
              ≫ Work.Homology.relChainMap Work.Homology.ZMod Φ = _
          rw [← Work.Homology.relChainMap_comp_relProj]
          rfl
      _ = Work.Cohomology.inclChains X U ≫ cokernel.π (Work.Cohomology.inclChains X A) := by
          rw [hΦ]
      _ = (Work.Cohomology.smallOfV A U ≫ w) ≫ cokernel.π (Work.Cohomology.inclChains X A) := by
            rw [Work.Cohomology.smallOfV_comp_smallToSing]
      _ = Work.Cohomology.smallOfV A U
            ≫ (w ≫ cokernel.π (Work.Cohomology.inclChains X A)) := Category.assoc _ _ _
      _ = Work.Cohomology.smallOfV A U
            ≫ (cokernel.π (Work.Cohomology.smallOfU A U) ≫ τ₃) := by rw [key]
      _ = (Work.Cohomology.smallOfV A U
            ≫ cokernel.π (Work.Cohomology.smallOfU A U)) ≫ τ₃ := (Category.assoc _ _ _).symm
      _ = (cokernel.π (Work.Cohomology.inclChains (TopCat.of U) A') ≫ e.hom) ≫ τ₃ := by rw [he]
      _ = cokernel.π (Work.Cohomology.inclChains (TopCat.of U) A') ≫ (e.hom ≫ τ₃) :=
          Category.assoc _ _ _
  rw [hfac, HomologicalComplex.homologyMap_comp]
  haveI : IsIso (HomologicalComplex.homologyMap e.hom n) :=
    Functor.map_isIso (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n)
      e.hom
  infer_instance

end

end Work.HomologyExtra
