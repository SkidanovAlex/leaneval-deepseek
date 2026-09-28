import Mathlib
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.relCochain_shortExact
import Submission.Work.Cohomology.DualComplex
import Submission.Work.Cohomology.uctDual
import Submission.Work.Cohomology.relChainsProjective
import Submission.Work.Cohomology.relComplexIsoDual

/-!
# The relative cohomology of a pair is the dual of its relative homology

For a topological space `X` and a subset `A ⊆ X`, the relative singular cochains `C^*(X,A)` are
the kernel of the restriction `C^*(X) ⟶ C^*(A)` (`relComplex`), while the relative singular chains
`C_*(X,A)` are the cokernel of the inclusion `C_*(A) ⟶ C_*(X)` (`relChains`).  Since `Hom_ℤ(-,ℤ)`
carries that cokernel to that kernel (`relComplexIsoDual`), the universal coefficient theorem for
the complex `C_*(X,A)` — whose terms are projective (`relChainsProjective`) and whose homology is
free by hypothesis — identifies the relative cohomology with the `ℤ`-dual of the relative
homology (`uctDual`).
-/

namespace Work.Cohomology

theorem relCohomologyDual (X : TopCat) (A : Set X)
    (h : ∀ k, Module.Free ℤ ↥((relChains X A).homology k)) (n : ℕ) :
    Nonempty ((relComplex ℤ X A).homology n ≅
      ModuleCat.of ℤ (↥((relChains X A).homology n) →ₗ[ℤ] ℤ)) := by
  obtain ⟨e⟩ := uctDual (relChains X A) (fun k => relChainsProjective X A k) h n
  obtain ⟨e'⟩ := relComplexIsoDual X A
  exact ⟨(HomologicalComplex.homologyMapIso e' n).trans e⟩

end Work.Cohomology
