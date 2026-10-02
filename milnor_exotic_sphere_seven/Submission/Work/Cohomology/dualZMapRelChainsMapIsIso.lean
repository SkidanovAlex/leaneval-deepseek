import Mathlib
import Submission.Work.Cohomology.cappedPairDefs
import Submission.Work.Cohomology.excisionDualZ
import Submission.Work.Cohomology.isIso_homologyMap_tau1
import Submission.Work.Cohomology.smallChainsHomotopyEquivInt
import Submission.Work.Cohomology.cokerSmallOfU_iso_relChains_compat
import Submission.Work.Cohomology.localHomology

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The `ℤ`-dual (into `R`) of the inclusion of pairs `(U, U ∩ A) ⊆ (X, A)` is a quasi-isomorphism

For open subsets `U, A ⊆ X` with `U ∪ A = X`, the inclusion of pairs `(U, U ∩ A) ⊆ (X, A)` induces
an isomorphism on relative **cohomology** with coefficients in any commutative ring `R`:

`H^n(Hom_ℤ(C_*(X,A), R)) ≅ H^n(Hom_ℤ(C_*(U, U∩A), R))`.

This is excision for the `ℤ`-dual complexes `dualZ R C = Hom_ℤ(C_•, R)` of
`Submission/Work/Cohomology/dualZ.lean`; the corresponding statement for cohomology with `R`
coefficients (`Work.Cohomology.cohomologicalExcision`) is an immediate consequence.

The proof is the dualised version of `Work.Cohomology.relChainsMap_quasiIso` (the `ℤ`-homological
excision for relative chains):

* the inclusion `relChainsMap X U A` factors as `e.hom ≫ τ` through the cokernel
  `coker (smallOfU A U)` of the map from `C_*(A)` into the *small* chains of the cover `{A, U}`
  (`Work.Cohomology.cokerSmallOfU_iso_relChains_compat`);
* applying the contravariant functor `dualZ R` to the morphism of degreewise split short exact
  sequences `S₁ : 0 → C_*(A) → C^{A,U}_*(X) → coker → 0` and `S₂ : 0 → C_*(A) → C_*(X) → C_*(X,A) → 0`
  gives a morphism `θ : dualZShort R S₂ ⟶ dualZShort R S₁` of short exact sequences of cochain
  complexes whose second component is the dual of the homotopy equivalence `smallToSing A U`
  (`Work.Cohomology.smallChainsHomotopyEquivInt`, using that `A` and `U` are open, so that
  `interior A ∪ interior U = X`) and whose third component is an isomorphism; the dual five lemma
  for `τ₁` (`Work.Cohomology.isIso_homologyMap_tau1`) then shows that `dualZ τ` is a
  quasi-isomorphism;
* the factor `dualZ e.hom` is an isomorphism because `e` is one (`dualZIsoOfIso`).
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

theorem dualZMapRelChainsMapIsIso (R : Type) [CommRing R] (X : TopCat) (U A : Set X)
    (hU : IsOpen U) (hA : IsOpen A) (hcov : U ∪ A = Set.univ) (n : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.dualZMap R (Work.Cohomology.relChains (TopCat.of U) {y : U | (y : X) ∈ A})
        (Work.Cohomology.relChains X A) (Work.Cohomology.relChainsMap X U A)) n) := by
  have hcov' : interior A ∪ interior U = Set.univ := by
    rw [hA.interior_eq, hU.interior_eq, Set.union_comm]
    exact hcov
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
    obtain ⟨e₂, he₂⟩ := smallChainsHomotopyEquivInt (X := X) A U hcov'
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

end

end Work.Cohomology
