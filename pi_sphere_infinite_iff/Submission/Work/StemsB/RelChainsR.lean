import Mathlib
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.relCochain_shortExact

/-!
# The relative singular chain complex with coefficients in a commutative ring, and its pair sequence

`Submission/Work/Cohomology/HomologyPairSequence.lean` constructs the relative singular chain
complex `C_*(X,A)` and the long exact sequence of a pair **with `ℤ` coefficients**.  The only
input of that construction is that the inclusion of chains `C_*(A) ⟶ C_*(X)` is a monomorphism,
which is proved by exhibiting an explicit retraction; the retraction `Work.Cohomology.chainRetract`
and its computation rule `chainRetract_spec` are already stated for an arbitrary commutative ring
`R` (`Submission/Work/Cohomology/relCochain_shortExact.lean`).  This file therefore generalises the
whole pair chapter to coefficients in an arbitrary commutative ring:

* `Work.StemsB.injective_chainMap_subtypeIncl_ring`, `mono_chainMap_subtypeIncl_ring`;
* `Work.StemsB.relChainsR R X A`, `relChainsRIncl R X A` — the relative chains and the inclusion;
* `Work.StemsB.relChainsR_shortExact` — `0 → C_*(A;R) → C_*(X;R) → C_*(X,A;R) → 0` is short exact;
* `Work.StemsB.relChainsRδ` and `relChainsR_exact₁/₂/₃` — the long exact sequence of the pair

  `⋯ → H_n(A;R) → H_n(X;R) → H_n(X,A;R) → H_{n-1}(A;R) → ⋯`.

Route B's sphere-specific route to the crux (`CONTRACTS.md` §F, Step I) applies the pair sequence
of `(PSⁿ, p⁻¹D)` with `R = ℚ`; this is what this file provides.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.StemsB

noncomputable section

variable (R : Type) [CommRing R]

/-- The inclusion `C_*(A;R) ⟶ C_*(X;R)` of singular chains induced by `A ⊆ X`, with coefficients
in `R`. -/
abbrev relChainsRIncl (X : TopCat) (A : Set X) :
    Work.Cohomology.singularChains R (TopCat.of A) ⟶ Work.Cohomology.singularChains R X :=
  Work.Cohomology.chainMap R (TopCat.of A) X (Work.Cohomology.subtypeIncl X A)

/-- The **relative singular chain complex** `C_*(X,A;R)`: the cokernel of the inclusion of chains.
For `R = ℤ` this is `Work.Cohomology.relChains`. -/
abbrev relChainsR (X : TopCat) (A : Set X) : ChainComplex (ModuleCat R) ℕ :=
  cokernel (relChainsRIncl R X A)

/-- The chain map `C_*(A;R) ⟶ C_*(X;R)` induced by the inclusion of a subspace is degreewise
injective, for any coefficient ring: it is a split monomorphism, with the splitting
`Work.Cohomology.chainRetract`. -/
theorem injective_chainMap_subtypeIncl_ring (X : TopCat) (A : Set X) (n : ℕ) :
    Function.Injective
      (ConcreteCategory.hom
        ((SSet.chainComplexMap (TopCat.toSSet.map (Work.Cohomology.subtypeIncl X A))
          (ModuleCat.of R R)).f n)) := by
  intro x y hxy
  have h := Work.Cohomology.chainRetract_spec R X A n
  have h2 : (Work.Cohomology.chainRetract R X A n).hom.comp
      ((SSet.chainComplexMap (TopCat.toSSet.map (Work.Cohomology.subtypeIncl X A))
        (ModuleCat.of R R)).f n).hom = LinearMap.id := by
    have hh := congrArg ModuleCat.Hom.hom h
    rw [ModuleCat.hom_comp, ModuleCat.hom_id] at hh
    exact hh
  have hgen : ∀ z, (Work.Cohomology.chainRetract R X A n).hom
      (((SSet.chainComplexMap (TopCat.toSSet.map (Work.Cohomology.subtypeIncl X A))
        (ModuleCat.of R R)).f n).hom z) = z := by
    intro z
    have hz := LinearMap.congr_fun h2 z
    rwa [LinearMap.comp_apply, LinearMap.id_apply] at hz
  rw [← hgen x, hxy, hgen y]

/-- The inclusion of the singular chains of a subspace is a monomorphism of chain complexes, for
any coefficient ring. -/
theorem mono_chainMap_subtypeIncl_ring (X : TopCat) (A : Set X) :
    Mono (relChainsRIncl R X A) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  rw [ModuleCat.mono_iff_injective]
  exact injective_chainMap_subtypeIncl_ring R X A n

/-- **The short complex of a pair**, `0 → C_*(A;R) → C_*(X;R) → C_*(X,A;R) → 0`. -/
def relChainsRShort (X : TopCat) (A : Set X) : ShortComplex (ChainComplex (ModuleCat R) ℕ) :=
  ShortComplex.mk (relChainsRIncl R X A) (cokernel.π (relChainsRIncl R X A))
    (cokernel.condition _)

/-- **The short complex of a pair is short exact**, for any coefficient ring. -/
theorem relChainsR_shortExact (X : TopCat) (A : Set X) :
    (relChainsRShort R X A).ShortExact where
  exact := ShortComplex.exact_cokernel (relChainsRIncl R X A)
  mono_f := mono_chainMap_subtypeIncl_ring R X A
  epi_g := show Epi (cokernel.π (relChainsRIncl R X A)) from inferInstance

/-- The connecting homomorphism `H_{n+1}(X,A;R) ⟶ H_n(A;R)` of the long exact sequence of the
pair. -/
def relChainsRδ (X : TopCat) (A : Set X) (n : ℕ) :
    (relChainsR R X A).homology (n + 1) ⟶
      (Work.Cohomology.singularChains R (TopCat.of A)).homology n :=
  (relChainsR_shortExact R X A).δ (n + 1) n (by simp [ComplexShape.down])

/-- The connecting homomorphism followed by the map induced by `A ↪ X` is zero. -/
theorem relChainsRδ_comp (X : TopCat) (A : Set X) (n : ℕ) :
    relChainsRδ R X A n ≫ HomologicalComplex.homologyMap (relChainsRIncl R X A) n = 0 :=
  (relChainsR_shortExact R X A).δ_comp (n + 1) n (by simp [ComplexShape.down])

/-- The map induced by `A ↪ X` followed by the map to the relative homology, then by the connecting
homomorphism, is zero. -/
theorem relChainsR_comp_δ (X : TopCat) (A : Set X) (n : ℕ) :
    HomologicalComplex.homologyMap (cokernel.π (relChainsRIncl R X A)) (n + 1) ≫
      relChainsRδ R X A n = 0 :=
  (relChainsR_shortExact R X A).comp_δ (n + 1) n (by simp [ComplexShape.down])

/-- Exactness of the long exact sequence of the pair at `H_n(A;R)`. -/
theorem relChainsR_exact₁ (X : TopCat) (A : Set X) (n : ℕ) :
    (ShortComplex.mk (relChainsRδ R X A n)
      (HomologicalComplex.homologyMap (relChainsRIncl R X A) n)
      (relChainsRδ_comp R X A n)).Exact :=
  (relChainsR_shortExact R X A).homology_exact₁ (n + 1) n (by simp [ComplexShape.down])

/-- Exactness of the long exact sequence of the pair at `H_n(X;R)`. -/
theorem relChainsR_exact₂ (X : TopCat) (A : Set X) (n : ℕ) :
    (ShortComplex.mk (HomologicalComplex.homologyMap (relChainsRIncl R X A) n)
      (HomologicalComplex.homologyMap (cokernel.π (relChainsRIncl R X A)) n)
      (by rw [← HomologicalComplex.homologyMap_comp, cokernel.condition,
        HomologicalComplex.homologyMap_zero])).Exact :=
  (relChainsR_shortExact R X A).homology_exact₂ n

/-- Exactness of the long exact sequence of the pair at `H_n(X,A;R)`. -/
theorem relChainsR_exact₃ (X : TopCat) (A : Set X) (n : ℕ) :
    (ShortComplex.mk (HomologicalComplex.homologyMap (cokernel.π (relChainsRIncl R X A)) (n + 1))
      (relChainsRδ R X A n) (relChainsR_comp_δ R X A n)).Exact :=
  (relChainsR_shortExact R X A).homology_exact₃ (n + 1) n (by simp [ComplexShape.down])

/-- **Relative homology vanishes when the inclusion is a homology epimorphism in the top degree and
a monomorphism one degree below.**  This is the exactness chase in the long exact sequence of the
pair `(X,A)`: `H_{n+1}(A) → H_{n+1}(X) → H_{n+1}(X,A) → H_n(A) → H_n(X)`, with the first map
epimorphic and the last monomorphic, forces `H_{n+1}(X,A) = 0`. -/
theorem isZero_relChainsR_homology_succ_of_epi_mono (X : TopCat) (A : Set X) (n : ℕ)
    (h1 : Epi (HomologicalComplex.homologyMap (relChainsRIncl R X A) (n + 1)))
    (h2 : Mono (HomologicalComplex.homologyMap (relChainsRIncl R X A) n)) :
    CategoryTheory.Limits.IsZero ((relChainsR R X A).homology (n + 1)) := by
  have hS₂ := relChainsR_exact₂ R X A (n + 1)
  have hS₁ := relChainsR_exact₁ R X A n
  have hS₃ := relChainsR_exact₃ R X A n
  exact hS₃.isZero_X₂ (hS₂.epi_f_iff.mp h1) (hS₁.mono_g_iff.mp h2)

/-- **Relative homology vanishes when the inclusion is an isomorphism on homology** in the top
degree and one degree below.  (For instance when the inclusion is a homotopy equivalence, e.g. a
deformation retraction.) -/
theorem isZero_relChainsR_homology_succ_of_isIso (X : TopCat) (A : Set X) (n : ℕ)
    (h1 : IsIso (HomologicalComplex.homologyMap (relChainsRIncl R X A) (n + 1)))
    (h2 : IsIso (HomologicalComplex.homologyMap (relChainsRIncl R X A) n)) :
    CategoryTheory.Limits.IsZero ((relChainsR R X A).homology (n + 1)) := by
  haveI := h1
  haveI := h2
  exact isZero_relChainsR_homology_succ_of_epi_mono R X A n inferInstance inferInstance

end

end Work.StemsB
