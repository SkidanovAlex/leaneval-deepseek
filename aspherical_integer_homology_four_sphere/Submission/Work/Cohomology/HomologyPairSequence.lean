import Mathlib
import Submission.Work.Cohomology.homologyPairShortExact

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The long exact sequence of a pair (singular homology)

For a topological space `X` and a subset `A ⊆ X`, the inclusion of singular chains
`C_*(A) ⟶ C_*(X)` is degreewise a split monomorphism (`mono_chainMap_subtypeIncl`), so

`0 ⟶ C_*(A) ⟶ C_*(X) ⟶ C_*(X,A) ⟶ 0`,

with `C_*(X,A)` the cokernel of the inclusion, is a short exact sequence of chain complexes.  This
file packages the cokernel sequence as a `ShortComplex`, proves that it is short exact, and records
the resulting long exact sequence of the pair

`⋯ ⟶ Hₙ(A) ⟶ Hₙ(X) ⟶ Hₙ(X,A) ⟶ Hₙ₋₁(A) ⟶ ⋯`.

## Main results

* `hPairShort`, `hPairShort_shortExact` — the short exact sequence of a pair;
* `hPairδ`, `hPairδ_comp`, `hPair_comp_δ` — the connecting homomorphism;
* `hPair_exact₁`, `hPair_exact₂`, `hPair_exact₃` — exactness at the three terms.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-- The inclusion `C_*(A) ⟶ C_*(X)` of singular chains induced by `A ⊆ X`. -/
abbrev inclChains (X : TopCat) (A : Set X) :
    singularChains ℤ (TopCat.of A) ⟶ singularChains ℤ X :=
  chainMap ℤ (TopCat.of A) X (subtypeIncl X A)

/-- **The short complex of a pair in homology**: `0 ⟶ C_*(A) ⟶ C_*(X) ⟶ C_*(X,A) ⟶ 0`, with
`C_*(X,A)` the cokernel of the inclusion. -/
def hPairShort (X : TopCat) (A : Set X) : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk (inclChains X A) (cokernel.π (inclChains X A)) (cokernel.condition _)

/-- **The short complex of a pair is short exact.** -/
theorem hPairShort_shortExact (X : TopCat) (A : Set X) : (hPairShort X A).ShortExact where
  exact := ShortComplex.exact_cokernel (inclChains X A)
  mono_f := mono_chainMap_subtypeIncl X A
  epi_g := show Epi (cokernel.π (inclChains X A)) from inferInstance

/-- The relative singular chain complex `C_*(X,A)`. -/
abbrev relChains (X : TopCat) (A : Set X) : ChainComplex (ModuleCat ℤ) ℕ :=
  (hPairShort X A).X₃

/-- The connecting homomorphism `Hₙ₊₁(X,A) ⟶ Hₙ(A)` of the long exact sequence of the pair. -/
def hPairδ (X : TopCat) (A : Set X) (n : ℕ) :
    (relChains X A).homology (n + 1) ⟶ (singularChains ℤ (TopCat.of A)).homology n :=
  (hPairShort_shortExact X A).δ (n + 1) n (by simp [ComplexShape.down])

/-- The connecting homomorphism followed by the map to `Hₙ(X)` is zero. -/
theorem hPairδ_comp (X : TopCat) (A : Set X) (n : ℕ) :
    CategoryTheory.CategoryStruct.comp (hPairδ X A n)
      (HomologicalComplex.homologyMap (inclChains X A) n) = 0 :=
  (hPairShort_shortExact X A).δ_comp (n + 1) n (by simp [ComplexShape.down])

/-- The map `Hₙ₊₁(X) ⟶ Hₙ₊₁(X,A)` followed by the connecting homomorphism is zero. -/
theorem hPair_comp_δ (X : TopCat) (A : Set X) (n : ℕ) :
    CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (cokernel.π (inclChains X A)) (n + 1))
      (hPairδ X A n) = 0 :=
  (hPairShort_shortExact X A).comp_δ (n + 1) n (by simp [ComplexShape.down])

/-- Exactness of the long exact sequence of the pair at `Hₙ(A)`. -/
theorem hPair_exact₁ (X : TopCat) (A : Set X) (n : ℕ) :
    (ShortComplex.mk (hPairδ X A n) (HomologicalComplex.homologyMap (inclChains X A) n)
      (hPairδ_comp X A n)).Exact :=
  (hPairShort_shortExact X A).homology_exact₁ (n + 1) n (by simp [ComplexShape.down])

/-- Exactness of the long exact sequence of the pair at `Hₙ(X)`. -/
theorem hPair_exact₂ (X : TopCat) (A : Set X) (n : ℕ) :
    (ShortComplex.mk (HomologicalComplex.homologyMap (inclChains X A) n)
      (HomologicalComplex.homologyMap (cokernel.π (inclChains X A)) n)
      (by rw [← HomologicalComplex.homologyMap_comp, cokernel.condition,
        HomologicalComplex.homologyMap_zero])).Exact :=
  (hPairShort_shortExact X A).homology_exact₂ n

/-- Exactness of the long exact sequence of the pair at `Hₙ(X,A)`. -/
theorem hPair_exact₃ (X : TopCat) (A : Set X) (n : ℕ) :
    (ShortComplex.mk (HomologicalComplex.homologyMap (cokernel.π (inclChains X A)) (n + 1))
      (hPairδ X A n) (hPair_comp_δ X A n)).Exact :=
  (hPairShort_shortExact X A).homology_exact₃ (n + 1) n (by simp [ComplexShape.down])

end

end Work.Cohomology
