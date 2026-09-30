import Mathlib
import Submission.Work.Serre.sigmaRelChainsIso
import Submission.Work.Serre.homology_coproduct_iso

/-!
# The relative homology of a disjoint union of pairs

For a family of spaces `X i` with subspaces `A i ⊆ X i`, the relative singular chain complex of the
disjoint union `Σ i, X i` relative to `Σ i, A i` is the direct sum of the relative singular chain
complexes of the pairs `(X i, A i)` (`Work.Serre.relChains_coproduct_iso`); the homology functor
carries this coproduct to the coproduct of the homologies
(`Work.Serre.homology_coproduct_iso`), which in `ModuleCat ℤ` is the direct sum
(`Work.Serre.coprod_directSum_iso`).
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Topology
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

/-- The coproduct in `ModuleCat ℤ` is the direct sum. -/
theorem coprod_directSum_iso {ι : Type} (M : ι → ModuleCat ℤ) :
    Nonempty ((∐ M) ≅ ModuleCat.of ℤ (DirectSum ι (fun i => ↑(M i)))) := by
  classical
  refine ⟨(ModuleCat.coprodIsoDirectSum M).trans (eqToIso ?_)⟩
  congr 1
  exact Subsingleton.elim _ _

/-- **The relative homology of a disjoint union of pairs is the direct sum of the relative
homologies of the pieces.**  For a family of spaces `X i` with subspaces `A i`, the relative
singular chain complex of the disjoint union `Σ i, X i` relative to `Σ i, A i` has homology the
direct sum of the homologies of the pairs `(X i, A i)`. -/
theorem sigmaRelHomologyIso {ι : Type} (X : ι → Type) [∀ i, TopologicalSpace (X i)]
    (A : ∀ i, Set (X i)) (n : ℕ) :
    Nonempty (((Work.Cohomology.relChains (TopCat.of (Σ i, X i))
        {x | x.2 ∈ A x.1}).homology n) ≅
      (ModuleCat.of ℤ (DirectSum ι (fun i => ↑((Work.Cohomology.relChains (TopCat.of (X i)) (A i)).homology n))))) := by
  obtain ⟨e1⟩ := relChains_coproduct_iso ι X A
  obtain ⟨e2⟩ := homology_coproduct_iso
    (fun i => Work.Cohomology.relChains (TopCat.of (X i)) (A i)) n
  obtain ⟨e3⟩ := coprod_directSum_iso
    (fun i => (Work.Cohomology.relChains (TopCat.of (X i)) (A i)).homology n)
  exact ⟨(HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapIso e1
    ≪≫ e2 ≪≫ e3⟩

end

end Work.Serre
