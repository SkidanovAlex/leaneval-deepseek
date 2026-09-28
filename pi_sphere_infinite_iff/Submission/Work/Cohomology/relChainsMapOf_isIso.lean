import Mathlib
import Submission.Work.Cohomology.localHomology

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-- **The morphism of short exact sequences of pairs induced by a map of pairs.**

For `f : X ⟶ Y` and `g : TopCat.of A ⟶ TopCat.of B` compatible in the sense that
`subtypeIncl X A ≫ f = g ≫ subtypeIncl Y B`, this is the morphism of short exact sequences
`0 ⟶ C_*(A) ⟶ C_*(X) ⟶ C_*(X,A) ⟶ 0  ⟶  0 ⟶ C_*(B) ⟶ C_*(Y) ⟶ C_*(Y,B) ⟶ 0`
with components `chainMap ℤ (TopCat.of A) (TopCat.of B) g`, `chainMap ℤ X Y f` and
`relChainsMapOf X Y A B f g w`. -/
def hPairShortMap (X Y : TopCat) (A : Set X) (B : Set Y) (f : X ⟶ Y)
    (g : TopCat.of A ⟶ TopCat.of B)
    (w : subtypeIncl X A ≫ f = g ≫ subtypeIncl Y B) :
    hPairShort X A ⟶ hPairShort Y B :=
  ShortComplex.homMk (chainMap ℤ (TopCat.of A) (TopCat.of B) g) (chainMap ℤ X Y f)
    (relChainsMapOf X Y A B f g w)
    (by
      show chainMap ℤ (TopCat.of A) (TopCat.of B) g ≫ inclChains Y B
        = inclChains X A ≫ chainMap ℤ X Y f
      simp only [inclChains, chainMap, ← Functor.map_comp]
      rw [w])
    (by
      show chainMap ℤ X Y f ≫ cokernel.π (inclChains Y B)
        = cokernel.π (inclChains X A) ≫ relChainsMapOf X Y A B f g w
      rw [relChainsMapOf]
      exact (cokernel_π_map (inclChains X A) (inclChains Y B)
        (chainMap ℤ (TopCat.of A) (TopCat.of B) g) (chainMap ℤ X Y f) _).symm)

/-- A morphism of pairs which is a quasi-isomorphism on both spaces induces a quasi-isomorphism of
the relative chain complexes.

`Work.Cohomology.relChainsMapOf X Y A B f g w : relChains X A ⟶ relChains Y B` is defined in
`Submission/Work/Cohomology/localHomology.lean` for `f : X ⟶ Y` and `g : TopCat.of A ⟶ TopCat.of B`
compatible in the sense that `subtypeIncl X A ≫ f = g ≫ subtypeIncl Y B`.

The two maps `chainMap ℤ X Y f` and `chainMap ℤ (TopCat.of A) (TopCat.of B) g` are assumed to be
quasi-isomorphisms (isomorphisms on homology in every degree); this is the necessary form of the
hypotheses (a five term argument at degree `n` uses the neighbouring degree `n - 1` as well), and it
is what a homeomorphism (or homotopy equivalence) of pairs supplies.

Proof: apply `HomologicalComplex.HomologySequence.isIso_homologyMap_τ₃` to the morphism of short
exact complexes `hPairShort X A ⟶ hPairShort Y B` whose components are
`chainMap ℤ (TopCat.of A) (TopCat.of B) g`, `chainMap ℤ X Y f` and `relChainsMapOf X Y A B f g w`.
The needed compatibility with the projections `cokernel.π` is `cokernel.π_map` (proved in
`localHomology.lean`). -/
theorem relChainsMapOf_isIso {X Y : TopCat} (A : Set X) (B : Set Y) (f : X ⟶ Y)
    (g : TopCat.of A ⟶ TopCat.of B)
    (w : CategoryTheory.CategoryStruct.comp (Work.Cohomology.subtypeIncl X A) f
      = CategoryTheory.CategoryStruct.comp g (Work.Cohomology.subtypeIncl Y B)) (n : ℕ)
    (hf : ∀ k, CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ X Y f) k))
    (hg : ∀ k, CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of A) (TopCat.of B) g) k)) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsMapOf X Y A B f g w) n) := by
  refine HomologicalComplex.HomologySequence.isIso_homologyMap_τ₃
    (hPairShortMap X Y A B f g w) (hPairShort_shortExact X A) (hPairShort_shortExact Y B) n
    ?_ (hf n) ?_ ?_
  · show Epi (HomologicalComplex.homologyMap
      (chainMap ℤ (TopCat.of A) (TopCat.of B) g) n)
    exact IsIso.epi_of_iso _
  · intro j _
    show IsIso (HomologicalComplex.homologyMap
      (chainMap ℤ (TopCat.of A) (TopCat.of B) g) j)
    exact hg j
  · intro j _
    show Mono (HomologicalComplex.homologyMap (chainMap ℤ X Y f) j)
    exact IsIso.mono_of_iso _

end

end Work.Cohomology
