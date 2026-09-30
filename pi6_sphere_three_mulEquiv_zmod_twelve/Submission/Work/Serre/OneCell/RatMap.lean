import Mathlib
import Submission.Work.Serre.E3aDefs
import Submission.Work.StemsB.RelChainsR
import Submission.Work.Cohomology.localHomology

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The five lemma for a map of pairs over `ℚ`

The `ℚ`-analogues of `Work.Cohomology.relChainsMapOf_homologyMap_isIso`: if a map of pairs
`(X,A) → (Y,B)` is a quasi-isomorphism on both spaces then the induced map of relative chain
complexes `C_*(X,A;ℚ) → C_*(Y,B;ℚ)` is a quasi-isomorphism (`isIso_homologyMap_relChainsRMapOf`);
the degreewise (`≤ n`) version `isIso_homologyMap_relChainsRMapOf_range` is the form used for the
local (per-cell) computations, where the absolute maps are only known to be isomorphisms in the
range.  The key input is the pair sequence `Work.StemsB.relChainsR_exact₁/₂/₃` and
`HomologicalComplex.HomologySequence.isIso_homologyMap_τ₃`.
-/

open CategoryTheory CategoryTheory.Limits
open AlgebraicTopology
open scoped Topology

namespace Work.Serre.OneCell

open Work.Serre

noncomputable section

/-- The map of relative chain complexes over `ℚ` induced by a continuous map of pairs, in the
"subtype" form: `A ⊆ X`, `B ⊆ Y` and `g : C(X,Y)` with `g '' A ⊆ B`. -/
noncomputable def pairMapQ {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (g : C(X, Y)) (hg : Set.MapsTo g A B) :
    Work.StemsB.relChainsR ℚ (TopCat.of X) A ⟶ Work.StemsB.relChainsR ℚ (TopCat.of Y) B :=
  Work.Serre.relChainsRMapOf (R := ℚ) (TopCat.of X) (TopCat.of Y) A B (TopCat.ofHom g)
    (TopCat.ofHom ⟨fun x => ⟨g x.1, hg x.2⟩, by fun_prop⟩) (by ext x; rfl)

/-- The map of short exact sequences of a pair induced by a map of pairs, over `ℚ`. -/
noncomputable def relShortMap {X Y : TopCat} (A : Set X) (B : Set Y) (f : X ⟶ Y)
    (g : TopCat.of A ⟶ TopCat.of B)
    (w : Work.Cohomology.subtypeIncl X A ≫ f = g ≫ Work.Cohomology.subtypeIncl Y B) :
    Work.StemsB.relChainsRShort ℚ X A ⟶ Work.StemsB.relChainsRShort ℚ Y B :=
  ShortComplex.homMk (Work.Cohomology.chainMap ℚ (TopCat.of A) (TopCat.of B) g)
    (Work.Cohomology.chainMap ℚ X Y f)
    (Work.Serre.relChainsRMapOf (R := ℚ) X Y A B f g w)
    (by
      show Work.Cohomology.chainMap ℚ (TopCat.of A) (TopCat.of B) g ≫
          Work.StemsB.relChainsRIncl ℚ Y B
        = Work.StemsB.relChainsRIncl ℚ X A ≫ Work.Cohomology.chainMap ℚ X Y f
      simp only [Work.StemsB.relChainsRIncl, Work.Cohomology.chainMap, ← Functor.map_comp]
      rw [w])
    (by
      show Work.Cohomology.chainMap ℚ X Y f ≫ cokernel.π (Work.StemsB.relChainsRIncl ℚ Y B)
        = cokernel.π (Work.StemsB.relChainsRIncl ℚ X A) ≫
          Work.Serre.relChainsRMapOf (R := ℚ) X Y A B f g w
      unfold Work.Serre.relChainsRMapOf
      exact (Work.Cohomology.cokernel_π_map _ _ _ _ _).symm)

/-- A chain map induced by an isomorphism of spaces is a quasi-isomorphism. -/
theorem isIso_homologyMap_chainMap_of_isIso {X Y : TopCat} (f : X ⟶ Y) [IsIso f] (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℚ X Y f) k) := by
  have h : Work.Cohomology.chainMap ℚ X Y f
      = ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
          (ModuleCat.of ℚ ℚ)).mapIso (asIso f)).hom) := rfl
  rw [h]
  exact (HomologicalComplex.homologyMapIso _ k).isIso_hom

/-- **The five lemma for a map of pairs over `ℚ`.** -/
theorem isIso_homologyMap_relChainsRMapOf {X Y : TopCat} (A : Set X) (B : Set Y) (f : X ⟶ Y)
    (g : TopCat.of A ⟶ TopCat.of B)
    (w : Work.Cohomology.subtypeIncl X A ≫ f = g ≫ Work.Cohomology.subtypeIncl Y B) (n : ℕ)
    (hf : ∀ k, IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℚ X Y f) k))
    (hg : ∀ k, IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℚ (TopCat.of A) (TopCat.of B) g) k)) :
    IsIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRMapOf (R := ℚ) X Y A B f g w) n) := by
  refine HomologicalComplex.HomologySequence.isIso_homologyMap_τ₃
    (relShortMap A B f g w) (Work.StemsB.relChainsR_shortExact ℚ X A)
    (Work.StemsB.relChainsR_shortExact ℚ Y B) n ?_ (hf n) ?_ ?_
  · haveI := hg n
    show Epi (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℚ (TopCat.of A) (TopCat.of B) g) n)
    exact IsIso.epi_of_iso _
  · intro j _
    exact hg j
  · intro j _
    haveI := hf j
    show Mono (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℚ X Y f) j)
    exact IsIso.mono_of_iso _

/-- **The degreewise (`≤ n`) five lemma for a map of pairs over `ℚ`.** -/
theorem isIso_homologyMap_relChainsRMapOf_range {X Y : TopCat} (A : Set X) (B : Set Y) (f : X ⟶ Y)
    (g : TopCat.of A ⟶ TopCat.of B)
    (w : Work.Cohomology.subtypeIncl X A ≫ f = g ≫ Work.Cohomology.subtypeIncl Y B) (n : ℕ)
    (hf : ∀ k, k ≤ n → IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℚ X Y f) k))
    (hg : ∀ k, k ≤ n → IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℚ (TopCat.of A) (TopCat.of B) g) k)) :
    IsIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRMapOf (R := ℚ) X Y A B f g w) n) := by
  refine HomologicalComplex.HomologySequence.isIso_homologyMap_τ₃
    (relShortMap A B f g w) (Work.StemsB.relChainsR_shortExact ℚ X A)
    (Work.StemsB.relChainsR_shortExact ℚ Y B) n ?_ (hf n le_rfl) ?_ ?_
  · haveI := hg n le_rfl
    show Epi (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℚ (TopCat.of A) (TopCat.of B) g) n)
    exact IsIso.epi_of_iso _
  · intro j hj
    exact hg j (by rw [← hj]; exact Nat.le_succ j)
  · intro j hj
    haveI := hf j (by rw [← hj]; exact Nat.le_succ j)
    show Mono (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℚ X Y f) j)
    exact IsIso.mono_of_iso _

end

end Work.Serre.OneCell
