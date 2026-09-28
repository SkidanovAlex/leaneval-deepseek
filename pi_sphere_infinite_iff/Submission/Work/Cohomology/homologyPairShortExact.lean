import Mathlib
import Submission.Work.Cohomology.relCochain_shortExact
import Submission.Work.Cohomology.Pullback
import Submission.Work.Cohomology.PairSequence

/-!
# The short exact sequence of singular chains of a pair (homology)

For a topological space `X` and a subset `A ⊆ X`, the inclusion `A ⊆ X` induces a chain map

`C_*(A) ⟶ C_*(X)`

on singular chains (with coefficients in `ℤ`).  This file constructs the **relative singular chain
complex** `C_*(X,A)` as the cokernel of this inclusion, so that

`0 ⟶ C_*(A) ⟶ C_*(X) ⟶ C_*(X,A) ⟶ 0`

is a short exact sequence of chain complexes of `ℤ`-modules.  Passing to homology yields the
long exact sequence of the pair `(X,A)`.

The only non-trivial input is that the inclusion of chains is a monomorphism, i.e. that it is
degreewise injective.  This is proved by exhibiting an explicit retraction of the chain map at each
degree (a singular simplex of `X` which comes from `A` is sent back to its unique preimage, and
every other simplex is sent to `0`), see `Work.Cohomology.chainRetract_spec`.  A split monomorphism
is a monomorphism, so the short complex `0 ⟶ C_*(A) ⟶ C_*(X) ⟶ cokernel ⟶ 0` is short exact.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-- The chain map `C_*(A) ⟶ C_*(X)` induced by the inclusion of a subspace is degreewise injective.

This is the `ModuleCat`-level form of `Work.Cohomology.chainRetract_spec`: the retraction of the
chain map at degree `n` exhibits the `n`-th component of the inclusion of chains as a split
monomorphism of `ℤ`-modules, hence an injective linear map. -/
theorem injective_chainComplexMap_subtypeIncl (X : TopCat) (A : Set X) (n : ℕ) :
    Function.Injective
      (ConcreteCategory.hom ((SSet.chainComplexMap
        (TopCat.toSSet.map (subtypeIncl X A)) (ModuleCat.of ℤ ℤ)).f n)) := by
  intro x y hxy
  have h := chainRetract_spec ℤ X A n
  have h2 : (chainRetract ℤ X A n).hom.comp
      ((SSet.chainComplexMap (TopCat.toSSet.map (subtypeIncl X A))
        (ModuleCat.of ℤ ℤ)).f n).hom = LinearMap.id := by
    have hh := congrArg ModuleCat.Hom.hom h
    rw [ModuleCat.hom_comp, ModuleCat.hom_id] at hh
    exact hh
  have hgen : ∀ z, (chainRetract ℤ X A n).hom
      (((SSet.chainComplexMap (TopCat.toSSet.map (subtypeIncl X A))
        (ModuleCat.of ℤ ℤ)).f n).hom z) = z := by
    intro z
    have hz := LinearMap.congr_fun h2 z
    rwa [LinearMap.comp_apply, LinearMap.id_apply] at hz
  rw [← hgen x, hxy, hgen y]

/-- The inclusion of the singular chains of a subspace is a monomorphism of chain complexes: it
is degreewise a split monomorphism, hence degreewise injective. -/
theorem mono_chainMap_subtypeIncl (X : TopCat) (A : Set X) :
    Mono (chainMap ℤ (TopCat.of A) X (subtypeIncl X A)) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  rw [ModuleCat.mono_iff_injective]
  exact injective_chainComplexMap_subtypeIncl X A n

/-- **The short exact sequence of singular chains of a pair.**

For a topological space `X` and a subset `A ⊆ X` there is a chain complex `C_*(X,A)` (the cokernel
of the inclusion `C_*(A) ⟶ C_*(X)`) such that

`0 ⟶ C_*(A) ⟶ C_*(X) ⟶ C_*(X,A) ⟶ 0`

is a short exact sequence of chain complexes of `ℤ`-modules. -/
theorem homologyPairShortExact (X : TopCat) (A : Set X) :
    ∃ (Crel : ChainComplex (ModuleCat ℤ) ℕ)
      (g : Work.Cohomology.singularChains ℤ X ⟶ Crel)
      (w : CategoryTheory.CategoryStruct.comp
        (Work.Cohomology.chainMap ℤ (TopCat.of A) X (Work.Cohomology.subtypeIncl X A)) g = 0),
      (CategoryTheory.ShortComplex.mk
        (Work.Cohomology.chainMap ℤ (TopCat.of A) X (Work.Cohomology.subtypeIncl X A)) g w).ShortExact := by
  let f := chainMap ℤ (TopCat.of A) X (subtypeIncl X A)
  have hf : Mono f := mono_chainMap_subtypeIncl X A
  refine ⟨cokernel f, cokernel.π f, cokernel.condition f, ?_⟩
  exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f))
    hf inferInstance

end

end Work.Cohomology
