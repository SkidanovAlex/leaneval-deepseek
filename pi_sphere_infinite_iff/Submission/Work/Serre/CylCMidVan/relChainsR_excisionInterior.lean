import Mathlib
import Submission.Work.StemsB.RelChainsR
import Submission.Work.Serre.csrExcisionRat
import Submission.Work.Cohomology.relChainsMap_quasiIso
import Submission.Work.Cohomology.smallChains_homology_iso_int

/-!
# Excision for a cover by interiors

`Work.Serre.csrExcisionRat` proves excision over `ℚ` for an **open** cover `U ∪ A = univ`.
Its proof however only uses the openness in one place: to feed the small-simplices theorem
`Work.Cohomology.smallChains_homology_iso`, which is stated for open covers, with the
hypothesis `U ∪ A = univ`.  The classical (Eilenberg–Steenrod) hypothesis is weaker: it suffices
that the *interiors* cover, `interior U ∪ interior A = univ`, and that is exactly the hypothesis of
`Work.Cohomology.smallChains_homology_iso_int` (`= smallChains_homology_iso_int`).

Accordingly this file reproduces the excision argument with the weaker hypothesis, in two steps:

* `relChainsMap_isIso_of_interior` — the integral statement: for `U, A ⊆ X` with
  `interior A ∪ interior U = univ`, the inclusion of pairs `(U, U ∩ A) → (X, A)` is a
  quasi-isomorphism of relative singular chain complexes over `ℤ`.  This is
  `Work.Cohomology.relChainsMap_quasiIso` with `smallChains_homology_iso` replaced by
  `smallChains_homology_iso_int` (everything else in that proof — the factorisation of
  `relChainsMap X U A` through the cokernel of `smallOfU A U`, the two degreewise split short
  exact sequences and the five lemma — uses only the cokernel/small-chains vocabulary, which does
  not see openness);
* `relChainsR_excisionInterior` — the rational statement over `Work.StemsB.relChainsR ℚ`, obtained
  from the integral one by flat base change `- ⊗[ℤ] ℚ`, verbatim as in `Work.Serre.csrExcisionRat`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Serre.CylCMidVan

noncomputable section

open Work.Cohomology

/-- **Excision for relative singular chains, for a cover by interiors (integral coefficients).**

Let `U, A ⊆ X` with `interior A ∪ interior U = univ`.  Then the inclusion of pairs
`(U, U ∩ A) → (X, A)` induces an isomorphism on relative singular homology in every degree.

This is `Work.Cohomology.relChainsMap_quasiIso` (or `Work.Cohomology.excision_relChainsMap_isIso`)
with the openness hypotheses on `U` and `A` replaced by the weaker, classical hypothesis
`interior A ∪ interior U = univ`: the only step of that proof which uses openness is the
small-simplices theorem, and `Work.Cohomology.smallChains_homology_iso_int` is precisely the
small-simplices theorem for a cover by interiors. -/
theorem relChainsMap_isIso_of_interior (X : TopCat) (U A : Set X)
    (hcov : interior A ∪ interior U = Set.univ) (n : ℕ) :
    CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap X U A) n) := by
  let A' : Set U := {x : U | (x : X) ∈ A}
  let u : singularChains ℤ (TopCat.of A) ⟶ smallChains A U := smallOfU A U
  let w : smallChains A U ⟶ singularChains ℤ X := smallToSing A U
  have huw : u ≫ w = inclChains X A := smallOfU_comp_smallToSing A U
  have huw' : u ≫ w = (𝟙 (singularChains ℤ (TopCat.of A))) ≫ inclChains X A := by
    rw [Category.id_comp]; exact huw
  let S₁ : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
    ShortComplex.mk u (cokernel.π u) (cokernel.condition u)
  let S₂ : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) := hPairShort X A
  have hS₁ : S₁.ShortExact :=
    { exact := ShortComplex.exact_cokernel u
      mono_f := mono_smallOfU A U
      epi_g := inferInstance }
  have hS₂ : S₂.ShortExact := hPairShort_shortExact X A
  let τ₃ : S₁.X₃ ⟶ S₂.X₃ := cokernel.map u (inclChains X A) (𝟙 _) w huw'
  have hcomp1 : (𝟙 S₁.X₁) ≫ S₂.f = S₁.f ≫ w := by
    show (𝟙 (singularChains ℤ (TopCat.of A))) ≫ inclChains X A = u ≫ w
    rw [Category.id_comp]; exact huw.symm
  have hcomp2 : w ≫ S₂.g = S₁.g ≫ τ₃ := by
    show w ≫ cokernel.π (inclChains X A)
      = cokernel.π u ≫ cokernel.map u (inclChains X A) (𝟙 _) w huw'
    exact (cokernel_π_map u (inclChains X A) (𝟙 _) w huw').symm
  let φ : S₁ ⟶ S₂ := ShortComplex.homMk (𝟙 S₁.X₁) w τ₃ hcomp1 hcomp2
  have hφ₂ : φ.τ₂ = w := rfl
  have hφ₁ : φ.τ₁ = 𝟙 S₁.X₁ := rfl
  have hτ₃ : IsIso (HomologicalComplex.homologyMap τ₃ n) := by
    refine HomologicalComplex.HomologySequence.isIso_homologyMap_τ₃ φ hS₁ hS₂ n ?_ ?_ ?_ ?_
    · rw [hφ₁, HomologicalComplex.homologyMap_id]; infer_instance
    · rw [hφ₂]; exact smallChains_homology_iso_int A U hcov n
    · intro j _
      rw [hφ₁, HomologicalComplex.homologyMap_id]; infer_instance
    · intro j _
      rw [hφ₂]
      haveI := smallChains_homology_iso_int A U hcov j
      infer_instance
  obtain ⟨e, he⟩ := cokerSmallOfU_iso_relChains_compat X A U
  have key : cokernel.π (smallOfU A U) ≫ τ₃ = w ≫ cokernel.π (inclChains X A) :=
    cokernel_π_map u (inclChains X A) (𝟙 _) w huw'
  have hfac : relChainsMap X U A = e.hom ≫ τ₃ := by
    apply (cancel_epi (cokernel.π (inclChains (TopCat.of U) A'))).1
    calc cokernel.π (inclChains (TopCat.of U) A') ≫ relChainsMap X U A
        = chainMap ℤ (TopCat.of U) X (subtypeIncl X U) ≫ cokernel.π (inclChains X A) :=
          cokernel_π_relChainsMap X U A
      _ = inclChains X U ≫ cokernel.π (inclChains X A) := rfl
      _ = (smallOfV A U ≫ w) ≫ cokernel.π (inclChains X A) := by
            rw [smallOfV_comp_smallToSing]
      _ = smallOfV A U ≫ (w ≫ cokernel.π (inclChains X A)) := Category.assoc _ _ _
      _ = smallOfV A U ≫ (cokernel.π (smallOfU A U) ≫ τ₃) := by rw [key]
      _ = (smallOfV A U ≫ cokernel.π (smallOfU A U)) ≫ τ₃ := (Category.assoc _ _ _).symm
      _ = (cokernel.π (inclChains (TopCat.of U) A') ≫ e.hom) ≫ τ₃ := by rw [he]
      _ = cokernel.π (inclChains (TopCat.of U) A') ≫ (e.hom ≫ τ₃) :=
          Category.assoc _ _ _
  rw [hfac, HomologicalComplex.homologyMap_comp]
  haveI : IsIso (HomologicalComplex.homologyMap e.hom n) :=
    Functor.map_isIso (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n)
      e.hom
  exact inferInstance

theorem relChainsR_excisionInterior {X : Type} [TopologicalSpace X] (U A : Set X)
    (hcov : interior A ∪ interior U = Set.univ) (n : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRInclPairMap (TopCat.of X) U A) n) := by
  -- the integral excision theorem, for a cover by interiors
  have hZ : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsMap (TopCat.of X) U A) n) :=
    relChainsMap_isIso_of_interior (TopCat.of X) U A hcov n
  -- base change commutes with the map of pairs
  have hsq : (Work.Serre.bcRat (TopCat.of ↥U) {x : ↥U | (x : X) ∈ A}).hom
        ≫ Work.Serre.relChainsRInclPairMap (TopCat.of X) U A
      = Work.StemsB.IntRatCM.map (Work.Cohomology.relChainsMap (TopCat.of X) U A)
        ≫ (Work.Serre.bcRat (TopCat.of X) A).hom := by
    rw [show Work.Serre.relChainsRInclPairMap (TopCat.of X) U A
        = Work.Serre.csrRelMapOf (TopCat.of ↥U) (TopCat.of X) {x : ↥U | (x : X) ∈ A} A
            (Work.Cohomology.subtypeIncl (TopCat.of X) U)
            (Work.Cohomology.inclInterA (TopCat.of X) U A)
            (by ext x; rfl) from rfl,
      show Work.Cohomology.relChainsMap (TopCat.of X) U A
        = Work.Cohomology.relChainsMapOf (TopCat.of ↥U) (TopCat.of X)
            {x : ↥U | (x : X) ∈ A} A
            (Work.Cohomology.subtypeIncl (TopCat.of X) U)
            (Work.Cohomology.inclInterA (TopCat.of X) U A)
            (by ext x; rfl) from rfl]
    exact Work.Serre.bcRat_relChainsMapOf (TopCat.of ↥U) (TopCat.of X)
      {x : ↥U | (x : X) ∈ A} A
      (Work.Cohomology.subtypeIncl (TopCat.of X) U)
      (Work.Cohomology.inclInterA (TopCat.of X) U A)
      (by ext x; rfl) (by ext x; rfl)
  -- express the rational inclusion of pairs as the base change of the integral one
  have hψ : Work.Serre.relChainsRInclPairMap (TopCat.of X) U A
      = (Work.Serre.bcRat (TopCat.of ↥U) {x : ↥U | (x : X) ∈ A}).inv
        ≫ Work.StemsB.IntRatCM.map (Work.Cohomology.relChainsMap (TopCat.of X) U A)
        ≫ (Work.Serre.bcRat (TopCat.of X) A).hom := by
    rw [← hsq, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [hψ, HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]
  haveI : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.bcRat (TopCat.of ↥U) {x : ↥U | (x : X) ∈ A}).inv n) := inferInstance
  haveI : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.StemsB.IntRatCM.map (Work.Cohomology.relChainsMap (TopCat.of X) U A)) n) :=
    Work.Serre.isIso_homologyMap_mapHomologicalComplex
      (Work.Cohomology.relChainsMap (TopCat.of X) U A) n hZ
  haveI : CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (Work.Serre.bcRat (TopCat.of X) A).hom n) := inferInstance
  infer_instance

end

end Work.Serre.CylCMidVan
