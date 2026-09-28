import Mathlib
import Submission.Work.Cohomology.cohomologicalExcision
import Submission.Work.Cohomology.excisionDualZ
import Submission.Work.Cohomology.relComplexIsoDualZ
import Submission.Work.Cohomology.relComplexMapDualZ

/-!
# Excision is induced by the map of pairs (the map-level form of cohomological excision)

`Work.Cohomology.cohomologicalExcision` states excision as the *existence* of an isomorphism
`H^n(X, A; R) ≅ H^n(X ∖ Z, A ∖ Z; R)` whenever `closure Z ⊆ interior A`.  For the applications of
the endgame one needs the stronger, map-level statement: the isomorphism is realised by the map
that the inclusion of pairs `(X ∖ Z, A ∖ Z) ↪ (X, A)` induces on relative singular cohomology, i.e.
by `Work.Cohomology.relComplexMap ℤ` (with `ℤ`-coefficients, which is what the endgame uses).

The file proves this in the form needed:

* `dualZMapRelChainsMapIsIso_of_interior` — the `ℤ`-dual of the inclusion
  `C_*(X ∖ Z, A ∖ Z) ⟶ C_*(X, A)` of relative chain complexes is a quasi-isomorphism.  This is
  `Work.Cohomology.dualZMapRelChainsMapIsIso` with the openness hypotheses on the two sets replaced
  by the (weaker, and here available) hypothesis `interior U ∪ interior A = univ`, which is exactly
  what the small-chains homotopy equivalence `Work.Cohomology.smallChainsHomotopyEquivInt` needs.
* `relPairsChainsMap_subtypeIncl_eq_relChainsMap` — the pair map written through `relMapSub`
  agrees with `relChainsMap`.
* `relComplexMapExcision` — the target: the pair map on relative cochains induced by the inclusion
  is an isomorphism on homology.

The route is: `relComplexMapDualZ` writes the pair map on relative cochains as the conjugation of
the `ℤ`-dual of the pair map on relative chains by the duality isomorphisms `relZIsoComplex` (which
are isomorphisms of complexes, hence isomorphisms on homology), and the `ℤ`-dual of the chain-level
pair map is a quasi-isomorphism by the excision computation with small chains.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology.Endgame

noncomputable section

/-- **Excision for the `ℤ`-dual of the relative chains, as a statement about the induced map.**

For `U, A ⊆ X` with `interior U ∪ interior A = univ` (the conclusion of
`Work.Cohomology.univ_eq_interior_union_compl` when `U` is the complement of `Z` and
`closure Z ⊆ interior A`), the inclusion of pairs `(U, U ∩ A) ⊆ (X, A)` induces an isomorphism on
the cohomology of the `ℤ`-dual complexes `Hom_ℤ(C_•(-), R)`.

This is the `interior`-form of `Work.Cohomology.dualZMapRelChainsMapIsIso`: the only use of the
openness hypotheses there is to rewrite `interior U = U`, `interior A = A` before applying the
small-chains homotopy equivalence. -/
theorem dualZMapRelChainsMapIsIso_of_interior (R : Type) [CommRing R] (X : TopCat) (U A : Set X)
    (hcov : interior U ∪ interior A = Set.univ) (n : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.dualZMap R (Work.Cohomology.relChains (TopCat.of U) {y : U | (y : X) ∈ A})
        (Work.Cohomology.relChains X A) (Work.Cohomology.relChainsMap X U A)) n) := by
  have hcov' : interior A ∪ interior U = Set.univ := by rw [Set.union_comm]; exact hcov
  let A' : Set U := {y : U | (y : X) ∈ A}
  -- the canonical identification of `coker (smallOfU A U)` with `C_*(U, A ∩ U)`
  obtain ⟨e, he⟩ := Work.Cohomology.cokerSmallOfU_iso_relChains_compat X A U
  -- the factorisation `relChainsMap X U A = e.hom ≫ τ`
  have huw' : Work.Cohomology.smallOfU A U ≫ Work.Cohomology.smallToSing A U
      = (𝟙 (Work.Cohomology.singularChains ℤ (TopCat.of A))) ≫ Work.Cohomology.inclChains X A := by
    rw [Category.id_comp]
    exact Work.Cohomology.smallOfU_comp_smallToSing A U
  let τ : cokernel (Work.Cohomology.smallOfU A U) ⟶ Work.Cohomology.relChains X A :=
    cokernel.map (Work.Cohomology.smallOfU A U) (Work.Cohomology.inclChains X A) (𝟙 _)
      (Work.Cohomology.smallToSing A U) huw'
  have hkey : cokernel.π (Work.Cohomology.smallOfU A U) ≫ τ
      = Work.Cohomology.smallToSing A U ≫ cokernel.π (Work.Cohomology.inclChains X A) :=
    Work.Cohomology.cokernel_π_map (Work.Cohomology.smallOfU A U) (Work.Cohomology.inclChains X A)
      (𝟙 _) (Work.Cohomology.smallToSing A U) huw'
  have hfac : Work.Cohomology.relChainsMap X U A = e.hom ≫ τ := by
    apply (cancel_epi (cokernel.π (Work.Cohomology.inclChains (TopCat.of U) A'))).1
    calc cokernel.π (Work.Cohomology.inclChains (TopCat.of U) A')
          ≫ Work.Cohomology.relChainsMap X U A
        = Work.Cohomology.chainMap ℤ (TopCat.of U) X (Work.Cohomology.subtypeIncl X U)
            ≫ cokernel.π (Work.Cohomology.inclChains X A) :=
          Work.Cohomology.cokernel_π_relChainsMap X U A
      _ = Work.Cohomology.inclChains X U ≫ cokernel.π (Work.Cohomology.inclChains X A) := rfl
      _ = (Work.Cohomology.smallOfV A U ≫ Work.Cohomology.smallToSing A U)
            ≫ cokernel.π (Work.Cohomology.inclChains X A) := by
            rw [Work.Cohomology.smallOfV_comp_smallToSing]
      _ = Work.Cohomology.smallOfV A U
            ≫ (Work.Cohomology.smallToSing A U ≫ cokernel.π (Work.Cohomology.inclChains X A)) :=
            Category.assoc _ _ _
      _ = Work.Cohomology.smallOfV A U ≫ (cokernel.π (Work.Cohomology.smallOfU A U) ≫ τ) := by
            rw [hkey]
      _ = (Work.Cohomology.smallOfV A U ≫ cokernel.π (Work.Cohomology.smallOfU A U)) ≫ τ :=
            (Category.assoc _ _ _).symm
      _ = (cokernel.π (Work.Cohomology.inclChains (TopCat.of U) A') ≫ e.hom) ≫ τ := by rw [he]
      _ = cokernel.π (Work.Cohomology.inclChains (TopCat.of U) A') ≫ (e.hom ≫ τ) :=
            Category.assoc _ _ _
  -- the two degreewise split short exact sequences of `ℤ`-chain complexes and a morphism between
  -- them
  let S₁ : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
    ShortComplex.mk (Work.Cohomology.smallOfU A U) (cokernel.π (Work.Cohomology.smallOfU A U))
      (cokernel.condition _)
  have hS₁ : S₁.ShortExact :=
    { exact := ShortComplex.exact_cokernel (Work.Cohomology.smallOfU A U)
      mono_f := Work.Cohomology.mono_smallOfU A U
      epi_g := inferInstance }
  have hs₁ : Work.Cohomology.IsDegreewiseSplit S₁ := Work.Cohomology.isDegreewiseSplit_small X A U
  let S₂ : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) := Work.Cohomology.hPairShort X A
  have hS₂ : S₂.ShortExact := Work.Cohomology.hPairShort_shortExact X A
  have hs₂ : Work.Cohomology.IsDegreewiseSplit S₂ := Work.Cohomology.isDegreewiseSplit_pair X A
  have hcomm1 : (𝟙 (Work.Cohomology.singularChains ℤ (TopCat.of A))) ≫ S₂.f
      = S₁.f ≫ Work.Cohomology.smallToSing A U := by
    show Work.Cohomology.inclChains X A
      = Work.Cohomology.smallOfU A U ≫ Work.Cohomology.smallToSing A U
    rw [Work.Cohomology.smallOfU_comp_smallToSing]
  have hcomm2 : Work.Cohomology.smallToSing A U ≫ S₂.g = S₁.g ≫ τ := hkey.symm
  let φ : S₁ ⟶ S₂ := ShortComplex.homMk (𝟙 _) (Work.Cohomology.smallToSing A U) τ hcomm1 hcomm2
  -- the dualised short exact sequences and the dualised morphism
  have hT₁ : (Work.Cohomology.dualZShort R S₁).ShortExact :=
    Work.Cohomology.dualZSplitExact R hS₁ hs₁
  have hT₂ : (Work.Cohomology.dualZShort R S₂).ShortExact :=
    Work.Cohomology.dualZSplitExact R hS₂ hs₂
  let θ : Work.Cohomology.dualZShort R S₂ ⟶ Work.Cohomology.dualZShort R S₁ :=
    ShortComplex.homMk (Work.Cohomology.dualZMap R S₁.X₃ S₂.X₃ τ)
      (Work.Cohomology.dualZMap R S₁.X₂ S₂.X₂ (Work.Cohomology.smallToSing A U))
      (Work.Cohomology.dualZMap R S₁.X₁ S₂.X₁ (𝟙 _))
      (by
        show Work.Cohomology.dualZMap R S₁.X₃ S₂.X₃ τ
            ≫ Work.Cohomology.dualZMap R S₁.X₂ S₁.X₃ S₁.g
          = Work.Cohomology.dualZMap R S₂.X₂ S₂.X₃ S₂.g
            ≫ Work.Cohomology.dualZMap R S₁.X₂ S₂.X₂ (Work.Cohomology.smallToSing A U)
        rw [← Work.Cohomology.dualZMap_comp, ← Work.Cohomology.dualZMap_comp, hcomm2])
      (by
        show Work.Cohomology.dualZMap R S₁.X₂ S₂.X₂ (Work.Cohomology.smallToSing A U)
            ≫ Work.Cohomology.dualZMap R S₁.X₁ S₁.X₂ S₁.f
          = Work.Cohomology.dualZMap R S₂.X₁ S₂.X₂ S₂.f
            ≫ Work.Cohomology.dualZMap R S₁.X₁ S₂.X₁ (𝟙 _)
        rw [← Work.Cohomology.dualZMap_comp, ← Work.Cohomology.dualZMap_comp, hcomm1])
  -- the middle component is a quasi-isomorphism by the homotopy equivalence `smallToSing A U`
  have hθ₂ : ∀ m, IsIso (HomologicalComplex.homologyMap θ.τ₂ m) := by
    intro m
    have h2 : θ.τ₂ = Work.Cohomology.dualZMap R S₁.X₂ S₂.X₂ (Work.Cohomology.smallToSing A U) := rfl
    rw [h2]
    obtain ⟨e₂, he₂⟩ := Work.Cohomology.smallChainsHomotopyEquivInt (X := X) A U hcov'
    rw [← he₂]
    exact Work.Cohomology.isIso_homologyMap_dualZMap R e₂ m
  -- the third component is the dual of an identity, hence an isomorphism
  have hθ₃ : ∀ m, IsIso (HomologicalComplex.homologyMap θ.τ₃ m) := by
    intro m
    haveI : IsIso θ.τ₃ := by
      rw [show θ.τ₃ = Work.Cohomology.dualZMap R S₁.X₁ S₁.X₁ (𝟙 S₁.X₁) from rfl,
        Work.Cohomology.dualZMap_id]
      exact IsIso.id _
    exact Functor.map_isIso (HomologicalComplex.homologyFunctor (ModuleCat R)
      (ComplexShape.up ℕ) m) θ.τ₃
  -- the dual five lemma
  have hτiso : ∀ m, IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.dualZMap R S₁.X₃ S₂.X₃ τ) m) :=
    Work.Cohomology.isIso_homologyMap_tau1 R θ hT₂ hT₁ hθ₂ hθ₃
  -- assemble along the factorisation
  haveI hτ : IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.dualZMap R (cokernel (Work.Cohomology.smallOfU A U))
        (Work.Cohomology.relChains X A) τ) n) := hτiso n
  have hei : IsIso (Work.Cohomology.dualZMap R (Work.Cohomology.relChains (TopCat.of U) A')
      (cokernel (Work.Cohomology.smallOfU A U)) e.hom) := by
    rw [show Work.Cohomology.dualZMap R (Work.Cohomology.relChains (TopCat.of U) A')
        (cokernel (Work.Cohomology.smallOfU A U)) e.hom
      = (Work.Cohomology.dualZIsoOfIso R e).inv from rfl]
    infer_instance
  haveI := hei
  rw [hfac, Work.Cohomology.dualZMap_comp, HomologicalComplex.homologyMap_comp]
  infer_instance


/-- **Excision is realised by the map induced by the inclusion of pairs.**

For `X : TopCat`, `A Z : Set X` with `closure Z ⊆ interior A`, and `V = X ∖ Z`, the map of relative
cochain complexes induced by the inclusion of pairs `(V, A ∩ V) ↪ (X, A)`,

`C^*(X, A; ℤ) ⟶ C^*(V, A ∩ V; ℤ)`,

is an isomorphism on homology in every degree.

This is the map-level form of `Work.Cohomology.cohomologicalExcision` (with `ℤ`-coefficients): the
inclusion of pairs is (up to the canonical identification of the two complexes with the `ℤ`-duals of
the relative chain complexes, `Work.Cohomology.relComplexMapDualZ`) the `ℤ`-dual of the inclusion
of relative chain complexes, which is a quasi-isomorphism by excision
(`dualZMapRelChainsMapIsIso_of_interior`, whose hypothesis `interior V ∪ interior A = univ` is
exactly `Work.Cohomology.univ_eq_interior_union_compl`). -/
theorem relComplexMapExcision (X : TopCat) (A Z : Set X) (hZ : closure Z ⊆ interior A) (n : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relComplexMap ℤ ((Subtype.val : {x : X | x ∉ Z} → X) ⁻¹' A) A (Work.Cohomology.subtypeIncl X {x : X | x ∉ Z})
        (fun x hx => by simp only [Work.Cohomology.subtypeIncl]; exact hx)) n) := by
  set V : Set X := {x : X | x ∉ Z} with hV
  -- the two interiors cover `X`, so that the small chains of the cover compute the relative chains
  have hcov : interior V ∪ interior A = Set.univ := by
    rw [hV, Set.union_comm]
    exact Work.Cohomology.univ_eq_interior_union_compl A Z hZ
  -- the `ℤ`-dual of the inclusion of relative chain complexes is a quasi-isomorphism
  have hmid : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.dualZMap ℤ (Work.Cohomology.relChains (TopCat.of V) {y : V | (y : X) ∈ A})
        (Work.Cohomology.relChains X A) (Work.Cohomology.relChainsMap X V A)) n) :=
    dualZMapRelChainsMapIsIso_of_interior ℤ X V A hcov n
  -- the duality identifications turn the pair map into the conjugate of the dualised chain map
  rw [Work.Cohomology.relComplexMapDualZ]
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]
  show CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Iso.inv (Work.Cohomology.relZIsoComplex ℤ X A)) n ≫
    HomologicalComplex.homologyMap (Work.Cohomology.dualZMap ℤ
      (Work.Cohomology.relChains (TopCat.of V) {y : V | (y : X) ∈ A})
      (Work.Cohomology.relChains X A) (Work.Cohomology.relChainsMap X V A)) n ≫
    HomologicalComplex.homologyMap
      (Iso.hom (Work.Cohomology.relZIsoComplex ℤ (TopCat.of V) {y : V | (y : X) ∈ A})) n)
  -- the two outer factors are isomorphisms of complexes, hence isomorphisms on homology
  haveI h1 : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Iso.inv (Work.Cohomology.relZIsoComplex ℤ X A)) n) :=
    Functor.map_isIso (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.up ℕ) n)
      (Iso.inv (Work.Cohomology.relZIsoComplex ℤ X A))
  haveI h3 : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Iso.hom (Work.Cohomology.relZIsoComplex ℤ (TopCat.of V) {y : V | (y : X) ∈ A})) n) :=
    Functor.map_isIso (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.up ℕ) n)
      (Iso.hom (Work.Cohomology.relZIsoComplex ℤ (TopCat.of V) {y : V | (y : X) ∈ A}))
  haveI := hmid
  infer_instance

end

end Work.Cohomology.Endgame
