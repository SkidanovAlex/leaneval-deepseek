import Mathlib
import Submission.Work.StemsB.RelChainsR
import Submission.Work.Cohomology.localHomology
import Submission.Work.Serre.DiscPair.cylPairDefs
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# The five lemma for maps of pairs over `ℚ`

The rational counterpart of `Work.Cohomology.relChainsMapOf_homologyMap_isIso`: a map of pairs
whose two components are rational homology isomorphisms induces a homology isomorphism on the
relative chain complexes.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace Work.Serre.DiscPair

noncomputable section

/-- **The morphism of short exact sequences of pairs over `ℚ`** induced by a map of pairs. -/
def relPairShortMapRat {X' Y' : Type} [TopologicalSpace X'] [TopologicalSpace Y']
    (A : Set X') (B : Set Y') (g : C(X', Y')) (hg : Set.MapsTo g A B) :
    Work.StemsB.relChainsRShort ℚ (TopCat.of X') A ⟶
      Work.StemsB.relChainsRShort ℚ (TopCat.of Y') B :=
  ShortComplex.homMk
    (Work.Cohomology.chainMap ℚ (TopCat.of A) (TopCat.of B)
      (TopCat.ofHom (restrictPair A B g hg)))
    (Work.Cohomology.chainMap ℚ (TopCat.of X') (TopCat.of Y') (TopCat.ofHom g))
    (Work.Serre.relChainsRPairMap A B g hg)
    (by
      show Work.Cohomology.chainMap ℚ (TopCat.of A) (TopCat.of B) _ ≫
          Work.StemsB.relChainsRIncl ℚ (TopCat.of Y') B
        = Work.StemsB.relChainsRIncl ℚ (TopCat.of X') A ≫
          Work.Cohomology.chainMap ℚ (TopCat.of X') (TopCat.of Y') _
      simp only [Work.StemsB.relChainsRIncl, Work.Cohomology.chainMap, ← Functor.map_comp]
      rw [show Work.Cohomology.subtypeIncl (TopCat.of X') A ≫ TopCat.ofHom g
          = TopCat.ofHom (restrictPair A B g hg) ≫ Work.Cohomology.subtypeIncl (TopCat.of Y') B from by
        ext x; rfl])
    (by
      show Work.Cohomology.chainMap ℚ (TopCat.of X') (TopCat.of Y') _ ≫
          cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of Y') B)
        = cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of X') A) ≫
          Work.Serre.relChainsRPairMap A B g hg
      rw [Work.Serre.relChainsRPairMap, Work.Serre.csrRelMapOf]
      exact (Work.Cohomology.cokernel_π_map _ _
        (Work.Cohomology.chainMap ℚ (TopCat.of A) (TopCat.of B) _)
        (Work.Cohomology.chainMap ℚ (TopCat.of X') (TopCat.of Y') _) _).symm)

/-- **The five lemma for a map of pairs over `ℚ`.**  If a map of pairs `(X,A) → (Y,B)` induces
isomorphisms on the absolute rational homology of both spaces, then it induces an isomorphism on
the relative rational homology in every degree. -/
theorem relChainsRPairMap_homologyMap_isIso {X' Y' : Type} [TopologicalSpace X']
    [TopologicalSpace Y'] (A : Set X') (B : Set Y') (g : C(X', Y'))
    (hg : Set.MapsTo g A B) (n : ℕ)
    (hf : ∀ k, CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℚ (TopCat.of X') (TopCat.of Y') (TopCat.ofHom g)) k))
    (hA : ∀ k, CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℚ (TopCat.of A) (TopCat.of B)
        (TopCat.ofHom (restrictPair A B g hg))) k)) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRPairMap A B g hg) n) := by
  refine HomologicalComplex.HomologySequence.isIso_homologyMap_τ₃
    (φ := relPairShortMapRat A B g hg)
    (Work.StemsB.relChainsR_shortExact ℚ (TopCat.of X') A)
    (Work.StemsB.relChainsR_shortExact ℚ (TopCat.of Y') B) n ?_ ?_ ?_ ?_
  · change Epi (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℚ (TopCat.of A)
      (TopCat.of B) (TopCat.ofHom (restrictPair A B g hg))) n)
    haveI := hA n
    exact IsIso.epi_of_iso _
  · change CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℚ (TopCat.of X') (TopCat.of Y') (TopCat.ofHom g)) n)
    exact hf n
  · intro j _
    change CategoryTheory.IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℚ
      (TopCat.of A) (TopCat.of B) (TopCat.ofHom (restrictPair A B g hg))) j)
    exact hA j
  · intro j _
    change Mono (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℚ (TopCat.of X') (TopCat.of Y') (TopCat.ofHom g)) j)
    haveI := hf j
    exact IsIso.mono_of_iso _

end

end Work.Serre.DiscPair
