import Mathlib
import Submission.Work.CWIND.Basic

namespace Work.CWIND.Cofibrant

open CategoryTheory CategoryTheory.Limits LightCondensed LightProfinite
open LightCondensed.Solid Submission.Blueprint
open scoped Simplicial

/-!
# `CWIND/T12`: the singular chain complex of a space is solid-cofibrant

This file proves `Work.CWIND.Cofibrant.C_solidCofibrant`: the integral singular chain complex
`C_sing(X)` of a topological space `X`, viewed as a cochain complex of light condensed abelian
groups concentrated in degrees `≤ 0`, is solid-cofibrant.

The proof is formal and does not use any topology of `X`: the `n`-th term of the singular chain
complex is a coproduct of copies of `ℤ` indexed by the set of `n`-simplices of `X`, hence, after
applying the discrete functor, is projective by `DiscProp`. A complex concentrated in degrees
`≤ 0` with projective terms is K-projective (`CochainComplex.isKProjective_of_projective`), and
`ResolutionProp` says that K-projective complexes are solid-cofibrant.
-/

noncomputable section

/-- The `m`-th term of the integral singular chain complex of `X`, as a `ℤ`-module, is the free
module on the set of `m`-simplices of `X`.

Mathlib builds `m`-chains as the coproduct (indexed by the `m`-simplices) of copies of `ℤ`; the
free module `J →₀ ℤ` is another model of the same coproduct, and both are colimits of the same
diagram, see `SSet.isColimitChainComplexXCofan` and `ModuleCat.finsuppCoconeIsColimit`. -/
def singChainIso (X : TopCat.{0}) (m : ℕ) :
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)).obj X).X m
      ≅ ModuleCat.of ℤ (((TopCat.toSSet.obj X) _⦋m⦌) →₀ ℤ) :=
  (SSet.isColimitChainComplexXCofan (TopCat.toSSet.obj X) (ModuleCat.of ℤ ℤ) m).coconePointUniqueUpToIso
    (ModuleCat.finsuppCoconeIsColimit ℤ ℤ ((TopCat.toSSet.obj X) _⦋m⦌))

/-- The integral singular chain complex of `X`, with discrete light condensed coefficients,
before extending the homological indexing to `ℤ`. -/
abbrev singChainComplexLightCond (X : TopCat.{0}) : ChainComplex LightCondAb ℕ :=
  ((LightCondensed.discrete (ModuleCat ℤ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)).obj X)

/-- Every term of the singular chain complex of `X` is a coproduct of copies of `ℤ`, hence its image
under the discrete functor is projective by `DiscProp`. -/
lemma projective_singChains_disc (hDisc : DiscProp) (X : TopCat.{0}) (m : ℕ) :
    Projective ((singChainComplexLightCond X).X m) :=
  Projective.of_iso (((LightCondensed.discrete (ModuleCat ℤ)).mapIso (singChainIso X m)).symm)
    (hDisc.2 _)

/-- Every term of `C_sing(X)`, placed in cohomological degree `n : ℤ`, is projective.
In degrees `n ≤ 0` this is the corresponding term of the homological complex, and in degrees
`n > 0` the complex vanishes. -/
lemma projective_X (hDisc : DiscProp) (X : TopCat.{0}) (n : ℤ) :
    Projective ((singularChainsLightCondAbComplexFunctor.obj X).X n) := by
  change Projective ((singChainComplexLightCond X).extend ComplexShape.embeddingDownNat |>.X n)
  by_cases hn : n ≤ 0
  · have hm : (((-n).toNat : ℕ) : ℤ) = -n := Int.toNat_of_nonneg (by omega)
    have h : ComplexShape.embeddingDownNat.f ((-n).toNat) = n := by
      rw [ComplexShape.embeddingDownNat_f]; omega
    exact Projective.of_iso
      (HomologicalComplex.extendXIso _ ComplexShape.embeddingDownNat h).symm
      (projective_singChains_disc hDisc X ((-n).toNat))
  · exact Projective.of_iso
      (CochainComplex.isZero_of_isStrictlyLE
        ((singChainComplexLightCond X).extend ComplexShape.embeddingDownNat) 0 n (by omega)).isoZero.symm
      inferInstance

/-- **CWIND/T12.**  The integral singular chain complex `C_sing(X)`, viewed as a cochain complex of
light condensed abelian groups concentrated in degrees `≤ 0`, is solid-cofibrant.  Each of its terms
is discrete, hence projective by `DiscProp`, and the complex is bounded above, so it is K-projective;
`ResolutionProp.2` then gives solid-cofibrancy. -/
theorem C_solidCofibrant (hDisc : DiscProp) (hRes : ResolutionProp) (X : TopCat.{0}) :
    SolidCofibrant (singularChainsLightCondAbComplexFunctor.obj X) := by
  have hK : singularChainsLightCondAbComplexFunctor.obj X
      = (singChainComplexLightCond X).extend ComplexShape.embeddingDownNat := rfl
  rw [hK]
  have hP : ∀ (n : ℤ), Projective (((singChainComplexLightCond X).extend
      ComplexShape.embeddingDownNat).X n) :=
    fun n => projective_X hDisc X n
  exact hRes.2 _ (CochainComplex.isKProjective_of_projective _ 0)

end

end Work.CWIND.Cofibrant
