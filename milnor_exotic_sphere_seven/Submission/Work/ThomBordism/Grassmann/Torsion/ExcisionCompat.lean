import Submission.Work.ThomBordism.Grassmann.Model
import Submission.Work.Cohomology.dualComplexMap_quasiIso
import Submission.Work.Cohomology.localHomology
import Submission.Work.Cohomology.CompatTrans.relComplexIsoDualZ

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-!
# Cohomological excision in the available import island

For open `U, A ⊆ X` with `U ∪ A = X`, the small-chains model of the pair produces a
quasi-isomorphism `C_*(U, U∩A) ⟶ C_*(X,A)` (`Work.Cohomology.excision_relChainsMap_isIso`).  Both
complexes are degreewise projective `ℤ`-modules (`Work.Cohomology.relChainsProjective`), so by
`Work.Cohomology.dualComplexMap_quasiIso` the `ℤ`-dual of this map is again a quasi-isomorphism, and
the identification `Work.Cohomology.relComplexIsoDualZ` of the relative cochain complex with the dual
of the relative chain complex
(`Submission/Work/Cohomology/CompatTrans/relComplexIsoDualZ.lean`) transports it to relative singular
cohomology:

  `H^n(X,A;R) ≅ H^n(U, U∩A;R)`.

The classical form `closure Z ⊆ interior A ⟹ H^n(X,A) ≅ H^n(X∖Z, A∖Z)` follows by taking
`U = X∖Z` and an open second member.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.ThomBordism.Grassmann

noncomputable section

/-- **Relative singular cohomology only depends on the pair up to an open cover of the space.**
For open `U, A ⊆ X` with `U ∪ A = X` there is an isomorphism
`H^n(X,A;R) ≅ H^n(U, U∩A;R)`. -/
theorem relCohomology_iso_of_open_cover (X : TopCat) (U A : Set X)
    (hU : IsOpen U) (hA : IsOpen A) (hcov : U ∪ A = Set.univ) (n : ℕ) :
    Nonempty (Work.Cohomology.relCohomology ℤ X A n ≅
      Work.Cohomology.relCohomology ℤ (TopCat.of ↥U) {y : ↥U | (y : X) ∈ A} n) := by
  obtain ⟨e₁⟩ := Work.Cohomology.relComplexIsoDualZ ℤ X A
  obtain ⟨e₂⟩ := Work.Cohomology.relComplexIsoDualZ ℤ (TopCat.of ↥U) {y : ↥U | (y : X) ∈ A}
  let φ := Work.Cohomology.relChainsMap X U A
  haveI : CategoryTheory.IsIso
      (HomologicalComplex.homologyMap
        (Work.Cohomology.dualComplexMap ℤ (Work.Cohomology.relChains (TopCat.of ↥U)
          {y : ↥U | (y : X) ∈ A}) (Work.Cohomology.relChains X A) φ) n) :=
    Work.Cohomology.dualComplexMap_quasiIso φ
      (fun k => Work.Cohomology.relChainsProjective (TopCat.of ↥U) _ k)
      (fun k => Work.Cohomology.relChainsProjective X A k)
      (fun k => Work.Cohomology.excision_relChainsMap_isIso X U A hU hA hcov k) n
  exact ⟨(HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.up ℕ) n).mapIso e₁
    ≪≫ asIso (HomologicalComplex.homologyMap
        (Work.Cohomology.dualComplexMap ℤ (Work.Cohomology.relChains (TopCat.of ↥U)
          {y : ↥U | (y : X) ∈ A}) (Work.Cohomology.relChains X A) φ) n)
    ≪≫ ((HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.up ℕ) n).mapIso e₂).symm⟩


/-- **A contractible (or acyclic) subspace can be ignored in relative cohomology.**
If the cohomology of `A` vanishes in degrees `m` and `m+1`, then the forgetful map
`H^{m+1}(X,A;ℤ) → H^{m+1}(X;ℤ)` is an isomorphism. -/
theorem relCoh_equiv_cohomology_of_subsingleton (X : Type) [TopologicalSpace X] (A : Set X) (m : ℕ)
    (h₁ : Subsingleton (Work.Thom.Coh ℤ m A)) (h₂ : Subsingleton (Work.Thom.Coh ℤ (m + 1) A)) :
    Nonempty (Work.Thom.RelCoh ℤ (m + 1) X A ≃ₗ[ℤ] Work.Thom.Coh ℤ (m + 1) X) := by
  have hmono : CategoryTheory.Mono (Work.Thom.relToAbs ℤ A (m + 1)) := by
    have hf : (ShortComplex.mk (Work.Thom.pairδC A m) (Work.Thom.relToAbs ℤ A (m + 1))
        (Work.Thom.pairδC_comp_relToAbs A m)).f = 0 :=
      (ModuleCat.isZero_of_subsingleton (Work.Thom.Coh ℤ m ↑A)).eq_of_src _ 0
    exact (ShortComplex.exact_iff_mono _ hf).mp (Work.Thom.pairExact₁ A m)
  have hepi : CategoryTheory.Epi (Work.Thom.relToAbs ℤ A (m + 1)) := by
    have hg : (ShortComplex.mk (Work.Thom.relToAbs ℤ A (m + 1)) (Work.Thom.restrCoh A ℤ (m + 1))
        (Work.Thom.relToAbs_comp_CohMap_subtype ℤ A (m + 1))).g = 0 :=
      (ModuleCat.isZero_of_subsingleton (Work.Thom.Coh ℤ (m + 1) ↑A)).eq_of_tgt _ 0
    exact (ShortComplex.exact_iff_epi _ hg).mp (Work.Thom.pairExact₂ A (m + 1))
  exact ⟨LinearEquiv.ofBijective (Work.Thom.relToAbs ℤ A (m + 1)).hom
    ⟨(ModuleCat.mono_iff_injective _).mp hmono, (ModuleCat.epi_iff_surjective _).mp hepi⟩⟩

/-- **Positive-degree cohomology of a contractible space vanishes**, in the `Subsingleton` form. -/
theorem subsingleton_cohomology_of_contractible {X : TopCat} [ContractibleSpace ↑X] (n : ℕ) :
    Subsingleton ((Work.Cohomology.singularCochainComplex ℤ X).homology (n + 1)) :=
  ModuleCat.subsingleton_of_isZero (Work.Cohomology.contractible ℤ X n)

end

end Work.ThomBordism.Grassmann
