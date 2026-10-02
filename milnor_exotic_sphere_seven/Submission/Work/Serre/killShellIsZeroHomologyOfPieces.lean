import Mathlib
import Submission.Work.Serre.CellStep.sigmaHomeo
import Submission.Work.Serre.sigmaChainsIso
import Submission.Work.Serre.homology_coproduct_iso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Vanishing of the singular homology of a space glued from disjoint open pieces

Let `Z` be a topological space covered by a family `Q i` of pairwise disjoint *open* subsets.  Then
`Z` is the topological disjoint union of the pieces `Q i` (`Work.Serre.CellStep.sigmaHomeo`), hence

* the singular chain complex of `Z` is the coproduct of the singular chain complexes of the pieces
  (`Work.Serre.chainSigmaIso`),
* homology of a coproduct of complexes is the coproduct of the homologies
  (`Work.Serre.homology_coproduct_iso`),
* and a coproduct of zero objects is a zero object.

Consequently, if the `k`-th singular homology of *every* piece vanishes, so does the `k`-th
singular homology of `Z`.  This is the "shell killing" input of the Serre/Whitehead chapter: the
homology of a space glued out of disjoint open cells is the sum of the homologies of the cells.

The only category-theoretic input, isolated as `isZero_coproduct_of_isZero`, is that a coproduct of
zero objects of a category with a zero object is a zero object (any cocone with point `0` is a
colimit whenever the diagram is zero, and colimits are unique up to isomorphism).
-/

namespace Work.Serre

noncomputable section

open CategoryTheory CategoryTheory.Limits

/-- **A coproduct of zero objects is a zero object.**  If every object of a family is zero, then the
cocone with point `0` is a colimit cocone, so the coproduct is (isomorphic to) `0`. -/
theorem isZero_coproduct_of_isZero {ι : Type} {C : Type*} [Category C] [HasZeroMorphisms C]
    [HasZeroObject C] [HasCoproductsOfShape ι C] (H : ι → C) (h : ∀ i, IsZero (H i)) :
    IsZero (∐ H) := by
  have hF : IsZero (Discrete.functor H) :=
    Functor.isZero _ (fun X => by rcases X with ⟨i⟩; exact h i)
  exact IsColimit.isZero_pt (colimit.isColimit (Discrete.functor H)) hF

/-- **If the `k`-th singular homology of every piece of a partition of `Z` into disjoint open sets
vanishes, then so does the `k`-th singular homology of `Z`.**

Indeed `Z ≅ Σ i, Q i` (`Work.Serre.CellStep.sigmaHomeo`), the singular chains of a `σ`-type are the
coproduct of the singular chains of the pieces (`Work.Serre.chainSigmaIso`), homology commutes with
coproducts (`Work.Serre.homology_coproduct_iso`), and a coproduct of zero objects is zero
(`isZero_coproduct_of_isZero`). -/
theorem killShellIsZeroHomologyOfPieces {Z : Type} [TopologicalSpace Z] {ι : Type} (Q : ι → Set Z)
    (hopen : ∀ i, IsOpen (Q i)) (hdisj : _root_.Pairwise fun i j => Disjoint (Q i) (Q j))
    (hcover : ⋃ i, Q i = Set.univ) (k : ℕ)
    (h : ∀ i, CategoryTheory.Limits.IsZero
      ((Work.Cohomology.singularChains ℤ (TopCat.of ↥(Q i))).homology k)) :
    CategoryTheory.Limits.IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of Z)).homology k) := by
  classical
  -- `Z` is the disjoint union of the pieces.
  obtain ⟨e, _he⟩ := CellStep.sigmaHomeo Q hopen hdisj hcover
  -- the singular chains of a homeomorphic space have isomorphic homology
  have hHomIso : (Work.Cohomology.singularChains ℤ (TopCat.of Z)).homology k ≅
      (Work.Cohomology.singularChains ℤ (TopCat.of (Σ i, ↥(Q i)))).homology k :=
    HomologicalComplex.homologyMapIso
      (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ ℤ)).mapIso (TopCat.isoOfHomeo e)) k
  -- the chains of the disjoint union are the coproduct of the chains of the pieces
  have hSigIso : (Work.Cohomology.singularChains ℤ (TopCat.of (Σ i, ↥(Q i)))).homology k ≅
      (∐ fun i => Work.Cohomology.singularChains ℤ (TopCat.of ↥(Q i))).homology k :=
    HomologicalComplex.homologyMapIso (chainSigmaIso ℤ ι (fun i => ↥(Q i))) k
  -- homology commutes with coproducts
  obtain ⟨e2⟩ := homology_coproduct_iso
    (fun i => Work.Cohomology.singularChains ℤ (TopCat.of ↥(Q i))) k
  have hfin : (Work.Cohomology.singularChains ℤ (TopCat.of Z)).homology k ≅
      ∐ fun i => (Work.Cohomology.singularChains ℤ (TopCat.of ↥(Q i))).homology k :=
    hHomIso ≪≫ hSigIso ≪≫ e2
  -- a coproduct of zero modules is zero
  refine IsZero.of_iso ?_ hfin
  exact isZero_coproduct_of_isZero
    (fun i => (Work.Cohomology.singularChains ℤ (TopCat.of ↥(Q i))).homology k) h

end

end Work.Serre
