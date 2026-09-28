import Mathlib
import Submission.Work.Cohomology.RelCupTransfer
import Submission.Work.Cohomology.PairSequence

namespace Work.Cohomology

open CategoryTheory CategoryTheory.Limits

/-- **The inclusion of the relative cochains is an isomorphism in degree `n+1` when the cohomology
of `A` vanishes in degrees `n` and `n+1`.**

The long exact cohomology sequence of the pair `(X,A)`

`Hⁿ(X) ⟶ Hⁿ(A) --δ--> Hⁿ⁺¹(X,A) ⟶ Hⁿ⁺¹(X) ⟶ Hⁿ⁺¹(A)`

has `δ = 0` because `Hⁿ(A) = 0`, which makes `Hⁿ⁺¹(X,A) ⟶ Hⁿ⁺¹(X)` injective; and the next map
`Hⁿ⁺¹(X) ⟶ Hⁿ⁺¹(A)` is `0` because `Hⁿ⁺¹(A) = 0`, which makes it surjective.  In a module
category a mono-epimorphism is an isomorphism. -/
theorem pairIsoOfTrivial (R : Type) [CommRing R] (X : TopCat) (A : Set X) (n : ℕ)
    (h₁ : Subsingleton (Work.Cohomology.singularCohomology R n (TopCat.of A)))
    (h₂ : Subsingleton (Work.Cohomology.singularCohomology R (n + 1) (TopCat.of A))) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relIncl R X A) (n + 1)) := by
  have i1 : IsZero (singularCohomology R n (TopCat.of A)) :=
    ModuleCat.isZero_iff_subsingleton.mpr h₁
  have i2 : IsZero (singularCohomology R (n + 1) (TopCat.of A)) :=
    ModuleCat.isZero_iff_subsingleton.mpr h₂
  have hmono : Mono (HomologicalComplex.homologyMap (relIncl R X A) (n + 1)) := by
    have hf : (ShortComplex.mk (pairδ R X A n)
        (HomologicalComplex.homologyMap (relIncl R X A) (n + 1))
        (pairδ_comp R X A n)).f = 0 := i1.eq_of_src _ 0
    exact (ShortComplex.exact_iff_mono _ hf).mp (pair_exact₁ R X A n)
  have hepi : Epi (HomologicalComplex.homologyMap (relIncl R X A) (n + 1)) := by
    have hg : (ShortComplex.mk (HomologicalComplex.homologyMap (relIncl R X A) (n + 1))
        (HomologicalComplex.homologyMap (restr R X A) (n + 1))
        (by rw [← HomologicalComplex.homologyMap_comp, relIncl_comp_restr,
          HomologicalComplex.homologyMap_zero])).g = 0 := i2.eq_of_tgt _ 0
    exact (ShortComplex.exact_iff_epi _ hg).mp (pair_exact₂ R X A (n + 1))
  exact isIso_of_mono_of_epi _

end Work.Cohomology
