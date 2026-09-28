import Submission.Work.Cohomology.relComplexIsoDual
import Submission.Work.Cohomology.dualComplexMap_quasiIso
import Submission.Work.Cohomology.relChainsProjective
import Submission.Work.Cohomology.localHomology

/-!
# Transporting relative cohomology along quasi-isomorphisms of relative chain complexes

The relative cochain complex `C^*(X,A)` is the `ℤ`-dual of the relative chain complex `C_*(X,A)`
(`Work.Cohomology.relComplexIsoDual`), and the `ℤ`-dual of a quasi-isomorphism between degreewise
projective chain complexes is a quasi-isomorphism (`Work.Cohomology.dualComplexMap_quasiIso`).  Hence

  **every quasi-isomorphism `C_*(X,A) → C_*(X',A')` of relative chain complexes induces an
  isomorphism `H^n(X',A';ℤ) ≅ H^n(X,A;ℤ)` on relative cohomology.**

This is the cohomological counterpart of the "five lemma" for relative *homology*
(`Work.Cohomology.relChainsMapOf_isIso`), and it is the tool that turns every *homological*
computation of this directory whose map is a **chain map** (excision, the fibrewise triviality, the
collar normalisation, the affine identification of the cube) into a cohomological one.  The
homological computations of `CollarModel.lean`, `EucCollarPair.lean` and `CubePairHomology.lean`
are of this kind *except* for the Mayer–Vietoris induction itself (`cubePair_main`), which produces
homology isomorphisms not induced by chain maps — that is the one place where `CubePairCohomology`
(`SerreCohomologyTargets.lean`) has to be recomputed in cohomology.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits

namespace Work.StemsB

noncomputable section

/-- **Relative cohomology is transported along quasi-isomorphisms of relative chain complexes.**

A quasi-isomorphism `φ : C_*(X,A) → C_*(X',A')` induces an isomorphism
`H^n(X',A';ℤ) ≅ H^n(X,A;ℤ)` (in the direction opposite to `φ`). -/
theorem nonempty_relCohomology_iso_of_relChains_quasiIso {X X' : TopCat} {A : Set X} {A' : Set X'}
    (φ : Work.Cohomology.relChains X A ⟶ Work.Cohomology.relChains X' A')
    (h : ∀ n : ℕ, IsIso (HomologicalComplex.homologyMap φ n)) (n : ℕ) :
    Nonempty ((Work.Cohomology.relComplex ℤ X' A').homology n ≅
      (Work.Cohomology.relComplex ℤ X A).homology n) := by
  obtain ⟨e₁⟩ := Work.Cohomology.relComplexIsoDual X A
  obtain ⟨e₂⟩ := Work.Cohomology.relComplexIsoDual X' A'
  haveI hiso : IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.dualComplexMap ℤ (Work.Cohomology.relChains X A)
        (Work.Cohomology.relChains X' A') φ) n) :=
    Work.Cohomology.dualComplexMap_quasiIso φ
      (fun k => Work.Cohomology.relChainsProjective X A k)
      (fun k => Work.Cohomology.relChainsProjective X' A' k) h n
  exact ⟨(HomologicalComplex.homologyMapIso e₂ n).trans
    ((asIso (HomologicalComplex.homologyMap (Work.Cohomology.dualComplexMap ℤ
        (Work.Cohomology.relChains X A) (Work.Cohomology.relChains X' A') φ) n)).trans
      (HomologicalComplex.homologyMapIso e₁ n).symm)⟩

/-- **Excision in relative cohomology** (the counterpart of
`Work.Cohomology.excision_relChainsMap_isIso`): for open `U`, `A` with `U ∪ A = X`, the relative
cohomology of `(X,A)` is that of `(U, U ∩ A)`. -/
theorem nonempty_relCohomology_iso_excision (X : TopCat) (U A : Set X) (hU : IsOpen U)
    (hA : IsOpen A) (hcov : U ∪ A = Set.univ) (n : ℕ) :
    Nonempty (((Work.Cohomology.relComplex ℤ X A).homology n) ≅
      ((Work.Cohomology.relComplex ℤ (TopCat.of U) {y : U | (y : X) ∈ A}).homology n)) :=
  nonempty_relCohomology_iso_of_relChains_quasiIso
    (Work.Cohomology.relChainsMap X U A)
    (fun k => Work.Cohomology.excision_relChainsMap_isIso X U A hU hA hcov k) n

end

end Work.StemsB
