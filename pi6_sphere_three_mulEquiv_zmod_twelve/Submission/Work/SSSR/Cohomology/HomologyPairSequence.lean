import Mathlib
import Submission.Work.SSSR.Cohomology.homologyPairShortExact
import Submission.Work.SSSR.Cohomology.Chains
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

open Work.Cohomology
variable {R : Type} [CommRing R] [Nontrivial R]

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
namespace Work.SSSR.Cohomology

noncomputable section

/-- The inclusion `C_*(A) ⟶ C_*(X)` of singular chains induced by `A ⊆ X`. -/
abbrev inclChains (R : Type) [CommRing R] [Nontrivial R] (X : TopCat) (A : Set X) :
    singularChains R (TopCat.of A) ⟶ singularChains R X :=
  chainMap R (TopCat.of A) X (subtypeIncl X A)

/-- **The short complex of a pair in homology**: `0 ⟶ C_*(A) ⟶ C_*(X) ⟶ C_*(X,A) ⟶ 0`, with
`C_*(X,A)` the cokernel of the inclusion. -/
def hPairShort (R : Type) [CommRing R] [Nontrivial R] (X : TopCat) (A : Set X) : ShortComplex (ChainComplex (ModuleCat R) ℕ) :=
  ShortComplex.mk (inclChains R X A) (cokernel.π (inclChains R X A)) (cokernel.condition _)

/-- **The short complex of a pair is short exact.** -/
theorem hPairShort_shortExact (X : TopCat) (A : Set X) : (hPairShort R X A).ShortExact where
  exact := ShortComplex.exact_cokernel (inclChains R X A)
  mono_f := mono_chainMap_subtypeIncl X A
  epi_g := show Epi (cokernel.π (inclChains R X A)) from inferInstance

/-- The relative singular chain complex `C_*(X,A)`. -/
abbrev relChains (R : Type) [CommRing R] [Nontrivial R] (X : TopCat) (A : Set X) : ChainComplex (ModuleCat R) ℕ :=
  (hPairShort R X A).X₃

/-- The connecting homomorphism `Hₙ₊₁(X,A) ⟶ Hₙ(A)` of the long exact sequence of the pair. -/
def hPairδ (X : TopCat) (A : Set X) (n : ℕ) :
    (relChains R X A).homology (n + 1) ⟶ (singularChains R (TopCat.of A)).homology n :=
  (hPairShort_shortExact X A).δ (n + 1) n (by simp [ComplexShape.down])

/-- The connecting homomorphism followed by the map to `Hₙ(X)` is zero. -/
theorem hPairδ_comp (X : TopCat) (A : Set X) (n : ℕ) :
    CategoryTheory.CategoryStruct.comp (hPairδ X A n)
      (HomologicalComplex.homologyMap (inclChains R X A) n) = 0 :=
  (hPairShort_shortExact X A).δ_comp (n + 1) n (by simp [ComplexShape.down])

/-- Exactness of the long exact sequence of the pair at `Hₙ(A)`. -/
theorem hPair_exact₁ (X : TopCat) (A : Set X) (n : ℕ) :
    (ShortComplex.mk (hPairδ X A n) (HomologicalComplex.homologyMap (inclChains R X A) n)
      (hPairδ_comp X A n)).Exact :=
  (hPairShort_shortExact X A).homology_exact₁ (n + 1) n (by simp [ComplexShape.down])

/-- Exactness of the long exact sequence of the pair at `Hₙ(X)`. -/
theorem hPair_exact₂ (X : TopCat) (A : Set X) (n : ℕ) :
    (ShortComplex.mk (HomologicalComplex.homologyMap (inclChains R X A) n)
      (HomologicalComplex.homologyMap (cokernel.π (inclChains R X A)) n)
      (by rw [← HomologicalComplex.homologyMap_comp, cokernel.condition,
        HomologicalComplex.homologyMap_zero])).Exact :=
  (hPairShort_shortExact X A).homology_exact₂ n

end

end Work.SSSR.Cohomology
