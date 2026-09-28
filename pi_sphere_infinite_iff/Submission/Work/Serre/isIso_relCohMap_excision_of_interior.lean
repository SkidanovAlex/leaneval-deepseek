import Mathlib
import Submission.Work.Thom.Cohomology
import Submission.Work.Cohomology.dualZMapRelChainsMapIsIso
import Submission.Work.Cohomology.cappedPairMapIso

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Serre

noncomputable section

open Work.Cohomology

/-! ## Excision for the `ℤ`-duals, in the "interiors cover" form

`Work.Cohomology.dualZMapRelChainsMapIsIso` assumes `U, A` open with `U ∪ A = univ`, but its proof
uses the openness in exactly one place: to rewrite the hypothesis into
`interior A ∪ interior U = univ` for `Work.Cohomology.smallChainsHomotopyEquivInt`, which is
already stated with the interior hypothesis.  Everything else in the proof (the factorisation of
`relChainsMap X U A` through `coker (smallOfU A U)`, the two degreewise split short exact sequences
and the dual five lemma) uses only the cokernel/small-chains vocabulary, which does not see
openness.  We therefore restate the result with the weaker hypothesis. -/

/-- **Excision for the `ℤ`-dual of the relative chain complexes, for a cover by interiors.** -/
theorem dualZMapRelChainsMapIsIso_of_interior (R : Type) [CommRing R] (X : TopCat) (U A : Set X)
    (hcov : interior A ∪ interior U = Set.univ) (n : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.dualZMap R (Work.Cohomology.relChains (TopCat.of U) {y : U | (y : X) ∈ A})
        (Work.Cohomology.relChains X A) (Work.Cohomology.relChainsMap X U A)) n) := by
  let A' : Set U := {y : U | (y : X) ∈ A}
  -- the canonical identification of `coker (smallOfU A U)` with `C_*(U, A ∩ U)`
  obtain ⟨e, he⟩ := cokerSmallOfU_iso_relChains_compat X A U
  -- the factorisation `relChainsMap X U A = e.hom ≫ τ`
  have huw' : smallOfU A U ≫ smallToSing A U
      = (𝟙 (singularChains ℤ (TopCat.of A))) ≫ inclChains X A := by
    rw [Category.id_comp]
    exact smallOfU_comp_smallToSing A U
  let τ : cokernel (smallOfU A U) ⟶ relChains X A :=
    cokernel.map (smallOfU A U) (inclChains X A) (𝟙 _) (smallToSing A U) huw'
  have hkey : cokernel.π (smallOfU A U) ≫ τ
      = smallToSing A U ≫ cokernel.π (inclChains X A) :=
    cokernel_π_map (smallOfU A U) (inclChains X A) (𝟙 _) (smallToSing A U) huw'
  have hfac : relChainsMap X U A = e.hom ≫ τ := by
    apply (cancel_epi (cokernel.π (inclChains (TopCat.of U) A'))).1
    calc cokernel.π (inclChains (TopCat.of U) A') ≫ relChainsMap X U A
        = chainMap ℤ (TopCat.of U) X (subtypeIncl X U) ≫ cokernel.π (inclChains X A) :=
          cokernel_π_relChainsMap X U A
      _ = inclChains X U ≫ cokernel.π (inclChains X A) := rfl
      _ = (smallOfV A U ≫ smallToSing A U) ≫ cokernel.π (inclChains X A) := by
            rw [smallOfV_comp_smallToSing]
      _ = smallOfV A U ≫ (smallToSing A U ≫ cokernel.π (inclChains X A)) :=
            Category.assoc _ _ _
      _ = smallOfV A U ≫ (cokernel.π (smallOfU A U) ≫ τ) := by rw [hkey]
      _ = (smallOfV A U ≫ cokernel.π (smallOfU A U)) ≫ τ := (Category.assoc _ _ _).symm
      _ = (cokernel.π (inclChains (TopCat.of U) A') ≫ e.hom) ≫ τ := by rw [he]
      _ = cokernel.π (inclChains (TopCat.of U) A') ≫ (e.hom ≫ τ) := Category.assoc _ _ _
  -- the two degreewise split short exact sequences of `ℤ`-chain complexes and a morphism between
  -- them
  let S₁ : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
    ShortComplex.mk (smallOfU A U) (cokernel.π (smallOfU A U)) (cokernel.condition _)
  have hS₁ : S₁.ShortExact :=
    { exact := ShortComplex.exact_cokernel (smallOfU A U)
      mono_f := mono_smallOfU A U
      epi_g := inferInstance }
  have hs₁ : IsDegreewiseSplit S₁ := isDegreewiseSplit_small X A U
  let S₂ : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) := hPairShort X A
  have hS₂ : S₂.ShortExact := hPairShort_shortExact X A
  have hs₂ : IsDegreewiseSplit S₂ := isDegreewiseSplit_pair X A
  have hcomm1 : (𝟙 (singularChains ℤ (TopCat.of A))) ≫ S₂.f = S₁.f ≫ smallToSing A U := by
    show inclChains X A = smallOfU A U ≫ smallToSing A U
    rw [smallOfU_comp_smallToSing]
  have hcomm2 : smallToSing A U ≫ S₂.g = S₁.g ≫ τ := hkey.symm
  let φ : S₁ ⟶ S₂ := ShortComplex.homMk (𝟙 _) (smallToSing A U) τ hcomm1 hcomm2
  -- the dualised short exact sequences and the dualised morphism
  have hT₁ : (dualZShort R S₁).ShortExact := dualZSplitExact R hS₁ hs₁
  have hT₂ : (dualZShort R S₂).ShortExact := dualZSplitExact R hS₂ hs₂
  let θ : dualZShort R S₂ ⟶ dualZShort R S₁ :=
    ShortComplex.homMk (dualZMap R S₁.X₃ S₂.X₃ τ) (dualZMap R S₁.X₂ S₂.X₂ (smallToSing A U))
      (dualZMap R S₁.X₁ S₂.X₁ (𝟙 _))
      (by
        show dualZMap R S₁.X₃ S₂.X₃ τ ≫ dualZMap R S₁.X₂ S₁.X₃ S₁.g
          = dualZMap R S₂.X₂ S₂.X₃ S₂.g ≫ dualZMap R S₁.X₂ S₂.X₂ (smallToSing A U)
        rw [← dualZMap_comp, ← dualZMap_comp, hcomm2])
      (by
        show dualZMap R S₁.X₂ S₂.X₂ (smallToSing A U) ≫ dualZMap R S₁.X₁ S₁.X₂ S₁.f
          = dualZMap R S₂.X₁ S₂.X₂ S₂.f ≫ dualZMap R S₁.X₁ S₂.X₁ (𝟙 _)
        rw [← dualZMap_comp, ← dualZMap_comp, hcomm1])
  -- the middle component is a quasi-isomorphism by the homotopy equivalence `smallToSing A U`
  have hθ₂ : ∀ m, IsIso (HomologicalComplex.homologyMap θ.τ₂ m) := by
    intro m
    have h2 : θ.τ₂ = dualZMap R S₁.X₂ S₂.X₂ (smallToSing A U) := rfl
    rw [h2]
    obtain ⟨e₂, he₂⟩ := smallChainsHomotopyEquivInt (X := X) A U hcov
    rw [← he₂]
    exact isIso_homologyMap_dualZMap R e₂ m
  -- the third component is the dual of an identity, hence an isomorphism
  have hθ₃ : ∀ m, IsIso (HomologicalComplex.homologyMap θ.τ₃ m) := by
    intro m
    haveI : IsIso θ.τ₃ := by
      rw [show θ.τ₃ = dualZMap R S₁.X₁ S₁.X₁ (𝟙 S₁.X₁) from rfl, dualZMap_id]
      exact IsIso.id _
    exact Functor.map_isIso (HomologicalComplex.homologyFunctor (ModuleCat R)
      (ComplexShape.up ℕ) m) θ.τ₃
  -- the dual five lemma
  have hτiso : ∀ m, IsIso (HomologicalComplex.homologyMap (dualZMap R S₁.X₃ S₂.X₃ τ) m) :=
    isIso_homologyMap_tau1 R θ hT₂ hT₁ hθ₂ hθ₃
  -- assemble along the factorisation
  haveI hτ : IsIso (HomologicalComplex.homologyMap
      (dualZMap R (cokernel (smallOfU A U)) (relChains X A) τ) n) := hτiso n
  have hei : IsIso (dualZMap R (relChains (TopCat.of U) A') (cokernel (smallOfU A U)) e.hom) := by
    rw [show dualZMap R (relChains (TopCat.of U) A') (cokernel (smallOfU A U)) e.hom
      = (dualZIsoOfIso R e).inv from rfl]
    infer_instance
  haveI := hei
  rw [hfac, dualZMap_comp, HomologicalComplex.homologyMap_comp]
  infer_instance

/-- **Excision for relative cohomology with coefficients in `R`, "interiors cover" form.**  The
inclusion of pairs `(U, U ∩ A) → (X, A)` induces an isomorphism on relative cohomology whenever
`interior A ∪ interior U = univ`. -/
theorem relComplexMap_excision_isIso_of_interior (R : Type) [CommRing R] (X : TopCat) (U A : Set X)
    (hcov : interior A ∪ interior U = Set.univ) (n : ℕ)
    (h : ∀ x ∈ {y : U | (y : X) ∈ A},
      (ConcreteCategory.hom (subtypeIncl X U)) x ∈ A) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (relComplexMap R {y : U | (y : X) ∈ A} A (subtypeIncl X U) h) n) := by
  rw [relComplexMapDualZ R {y : U | (y : X) ∈ A} A (subtypeIncl X U) h]
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]
  rw [relChainsMapOf_relMapSub_eq_relChainsMap X U A h]
  haveI hB : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (dualZMap R (relChains (TopCat.of U) {y : U | (y : X) ∈ A}) (relChains X A)
        (relChainsMap X U A)) n) :=
    dualZMapRelChainsMapIsIso_of_interior R X U A hcov n
  haveI h1 : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (CategoryTheory.Iso.inv (relZIsoComplex R X A)) n) :=
    Functor.map_isIso (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) n)
      (CategoryTheory.Iso.inv (relZIsoComplex R X A))
  haveI h2 : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (CategoryTheory.Iso.hom (relZIsoComplex R (TopCat.of U) {y : U | (y : X) ∈ A})) n) :=
    Functor.map_isIso (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) n)
      (CategoryTheory.Iso.hom (relZIsoComplex R (TopCat.of U) {y : U | (y : X) ∈ A}))
  exact inferInstance

/-- **Excision for relative singular cohomology, in the "interiors cover" form.**  Let `X` be a
topological space and `A, V ⊆ X` with `interior A ∪ interior V = univ`.  Then the inclusion of
pairs `(V, V ∩ A) → (X, A)` induces an isomorphism `H^n(X,A;R) → H^n(V, V∩A;R)` on relative
singular cohomology with coefficients in any commutative ring `R`.

This is the `interior`-hypothesis form of `Work.Cohomology.relComplexMap_excision_isIso` (which
assumes `U, V` *open* with `U ∪ V = univ`) and of `Work.Cohomology.cohomologicalExcision` (which is
not pinned to the inclusion of pairs).  Concretely it is the statement
`Work.Cohomology.dualZMapRelChainsMapIsIso` with the openness hypotheses `hU, hA, hcov` replaced by
`interior A ∪ interior U = univ`; that proof only uses the openness to produce `hcov'` for
`Work.Cohomology.smallChainsHomotopyEquivInt`, which is already stated with the `interior`
hypothesis. -/
theorem isIso_relCohMap_excision_of_interior (R : Type) [CommRing R]
    {X : Type} [TopologicalSpace X] (A V : Set X)
    (hcov : interior A ∪ interior V = Set.univ) (n : ℕ) :
    CategoryTheory.IsIso (Work.Thom.relCohMap
      (⟨Subtype.val, continuous_subtype_val⟩ : C(↥V, X))
      {y : ↥V | (y : X) ∈ A} A (fun x hx => hx) R n) := by
  exact relComplexMap_excision_isIso_of_interior R (TopCat.of X) V A hcov n (fun x hx => hx)

end

end Work.Serre
