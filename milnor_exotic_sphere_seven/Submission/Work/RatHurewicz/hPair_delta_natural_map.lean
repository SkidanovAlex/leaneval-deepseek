import Mathlib
import Submission.Work.Cohomology.relChainsMapOf_isIso
import Submission.Work.Cohomology.HomologyPairSequence

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.RatHurewicz

/-- **Naturality of the connecting homomorphism of a pair under a map of pairs.**  A map of pairs
`(f, g) : (X,A) → (Y,B)` (compatible in the sense that `A ↪ X ≫ f = g ≫ B ↪ Y`) induces the
commutative square

`H_{n+1}(X,A) --δ_X--> H_n(A)`,   `H_{n+1}(Y,B) --δ_Y--> H_n(B)`

with vertical maps the morphisms on relative resp. absolute homology induced by `f` and `g`, i.e.
`relChainsMapOf … ≫ hPairδ Y B n = hPairδ X A n ≫ homologyMap (chainMap g) n`.

This is the compatibility of the relative Hurewicz map (the push-forward of the relative fundamental
class of the cube) with the long exact sequences of the two pairs, i.e. the "commutes with the
boundary maps" clause in the description of the relative Hurewicz homomorphism.  It follows from
`HomologicalComplex.HomologySequence.δ_naturality` applied to the morphism of short exact complexes
of pairs `hPairShortMap X Y A B f g w` (`Submission/Work/Cohomology/relChainsMapOf_isIso.lean`),
whose three components are the chain maps of `g`, `f` and `relChainsMapOf`.  (The same square, with
a private copy of `hPairShortMap`, is already proved as
`Work.ThreeConnected.Excision.hPairδ_naturality_map`; this module repeats it so that the chapter is
self-contained and fork-neutral.) -/
theorem hPair_delta_natural_map {X Y : TopCat} (A : Set X) (B : Set Y) (f : X ⟶ Y)
    (g : TopCat.of A ⟶ TopCat.of B)
    (w : CategoryTheory.CategoryStruct.comp (Work.Cohomology.subtypeIncl X A) f
      = CategoryTheory.CategoryStruct.comp g (Work.Cohomology.subtypeIncl Y B)) (n : ℕ) :
    CategoryTheory.CategoryStruct.comp
        (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMapOf X Y A B f g w) (n + 1))
        (Work.Cohomology.hPairδ Y B n)
      = CategoryTheory.CategoryStruct.comp (Work.Cohomology.hPairδ X A n)
          (HomologicalComplex.homologyMap
            (Work.Cohomology.chainMap ℤ (TopCat.of A) (TopCat.of B) g) n) :=
  (HomologicalComplex.HomologySequence.δ_naturality
    (Work.Cohomology.hPairShortMap_aux X Y A B f g w)
    (Work.Cohomology.hPairShort_shortExact X A)
    (Work.Cohomology.hPairShort_shortExact Y B) (n + 1) n
    (by simp [ComplexShape.down])).symm

end Work.RatHurewicz
