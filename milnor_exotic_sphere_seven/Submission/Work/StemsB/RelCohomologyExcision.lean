import Submission.Work.Cohomology.localHomology
import Submission.Work.Cohomology.relComplexIsoDual
import Submission.Work.Cohomology.dualComplexMap_quasiIso
import Submission.Work.Cohomology.relChainsProjective
import Submission.Work.Cohomology.relCochain_shortExact

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Excision in relative cohomology

For a topological space `X` and two open sets `U, A` with `U ∪ A = X`, the excision theorem for
singular chains gives a quasi-isomorphism

  `Work.Cohomology.relChainsMap X U A : C_*(U, U ∩ A) ⟶ C_*(X, A)`

(`Work.Cohomology.excision_relChainsMap_isIso`).  Its `ℤ`-dual is again a quasi-isomorphism
(`Work.Cohomology.dualComplexMap_quasiIso`, since both complexes are degreewise projective), and the
relative cochain complex is the `ℤ`-dual of the relative chain complex
(`Work.Cohomology.relComplexIsoDual`); hence **excision holds in relative cohomology**:

  `H^n(U, U ∩ A; ℤ) ≅ H^n(X, A; ℤ)`.

This is the cohomological counterpart of the homology statement, and one of the two inputs of the
identification `τ : H^n(E, E|_V) ≅ H^{n-m}(F)` of the Wang sequence.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits

namespace Work.StemsB

noncomputable section

/-- **Excision in relative cohomology.**  For open `U`, `A` with `U ∪ A = X`, the inclusion
`U ↪ X` induces an isomorphism `H^n(U, U ∩ A; ℤ) ≅ H^n(X, A; ℤ)`. -/
theorem relCohomology_excision (X : TopCat) (U A : Set X) (hU : IsOpen U) (hA : IsOpen A)
    (hcov : U ∪ A = Set.univ) (n : ℕ) :
    Nonempty (((Work.Cohomology.relComplex ℤ (TopCat.of U) {y : U | (y : X) ∈ A}).homology n) ≅
      ((Work.Cohomology.relComplex ℤ X A).homology n)) := by
  obtain ⟨e₁⟩ := Work.Cohomology.relComplexIsoDual (TopCat.of U) {y : U | (y : X) ∈ A}
  obtain ⟨e₂⟩ := Work.Cohomology.relComplexIsoDual X A
  haveI hiso : IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.dualComplexMap ℤ
        (Work.Cohomology.relChains (TopCat.of U) {y : U | (y : X) ∈ A})
        (Work.Cohomology.relChains X A) (Work.Cohomology.relChainsMap X U A)) n) :=
    Work.Cohomology.dualComplexMap_quasiIso (Work.Cohomology.relChainsMap X U A)
      (fun k => Work.Cohomology.relChainsProjective (TopCat.of U) {y : U | (y : X) ∈ A} k)
      (fun k => Work.Cohomology.relChainsProjective X A k)
      (fun k => Work.Cohomology.excision_relChainsMap_isIso X U A hU hA hcov k) n
  exact ⟨(HomologicalComplex.homologyMapIso e₁ n).trans
    ((asIso (HomologicalComplex.homologyMap (Work.Cohomology.dualComplexMap ℤ
        (Work.Cohomology.relChains (TopCat.of U) {y : U | (y : X) ∈ A})
        (Work.Cohomology.relChains X A) (Work.Cohomology.relChainsMap X U A)) n)).symm.trans
      (HomologicalComplex.homologyMapIso e₂ n).symm)⟩

/-- **Excision in relative cohomology, for a pair of a subspace.**  This is the form in which the
Wang sequence uses it: the relative cohomology of `(E, E|_A)` is that of `(E|_U, E|_{U∩A})`. -/
theorem relCohomology_excision_preimage {E : Type} [TopologicalSpace E] {B : Type}
    [TopologicalSpace B] (p : C(E, B)) (U A : Set B) (hU : IsOpen U) (hA : IsOpen A)
    (hcov : U ∪ A = Set.univ) (n : ℕ) :
    Nonempty (((Work.Cohomology.relComplex ℤ (TopCat.of ↥(p ⁻¹' U))
        {y : ↥(p ⁻¹' U) | (y : E) ∈ p ⁻¹' A}).homology n) ≅
      ((Work.Cohomology.relComplex ℤ (TopCat.of E) (p ⁻¹' A)).homology n)) := by
  have hU' : IsOpen (p ⁻¹' U) := hU.preimage p.continuous
  have hA' : IsOpen (p ⁻¹' A) := hA.preimage p.continuous
  have hcov' : p ⁻¹' U ∪ p ⁻¹' A = Set.univ := by
    rw [← Set.preimage_union, hcov, Set.preimage_univ]
  exact relCohomology_excision (TopCat.of E) (p ⁻¹' U) (p ⁻¹' A) hU' hA' hcov' n

end

end Work.StemsB
