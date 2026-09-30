import Mathlib
import Submission.Work.SSSR.Cohomology.relCochain_shortExact
import Submission.Work.SSSR.Cohomology.Pullback
import Submission.Work.Cohomology.PairSequence
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

open Work.Cohomology
variable {R : Type} [CommRing R] [Nontrivial R]

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
namespace Work.SSSR.Cohomology

noncomputable section

/-- The chain map `C_*(A) ⟶ C_*(X)` induced by the inclusion of a subspace is degreewise injective.

This is the `ModuleCat`-level form of `Work.Cohomology.chainRetract_spec`: the retraction of the
chain map at degree `n` exhibits the `n`-th component of the inclusion of chains as a split
monomorphism of `ℤ`-modules, hence an injective linear map. -/
theorem injective_chainComplexMap_subtypeIncl (X : TopCat) (A : Set X) (n : ℕ) :
    Function.Injective
      (ConcreteCategory.hom ((SSet.chainComplexMap
        (TopCat.toSSet.map (subtypeIncl X A)) (ModuleCat.of R R)).f n)) := by
  intro x y hxy
  have h := chainRetract_spec R X A n
  have h2 : (chainRetract R X A n).hom.comp
      ((SSet.chainComplexMap (TopCat.toSSet.map (subtypeIncl X A))
        (ModuleCat.of R R)).f n).hom = LinearMap.id := by
    have hh := congrArg ModuleCat.Hom.hom h
    rw [ModuleCat.hom_comp, ModuleCat.hom_id] at hh
    exact hh
  have hgen : ∀ z, (chainRetract R X A n).hom
      (((SSet.chainComplexMap (TopCat.toSSet.map (subtypeIncl X A))
        (ModuleCat.of R R)).f n).hom z) = z := by
    intro z
    have hz := LinearMap.congr_fun h2 z
    rwa [LinearMap.comp_apply, LinearMap.id_apply] at hz
  rw [← hgen x, hxy, hgen y]

/-- The inclusion of the singular chains of a subspace is a monomorphism of chain complexes: it
is degreewise a split monomorphism, hence degreewise injective. -/
theorem mono_chainMap_subtypeIncl (X : TopCat) (A : Set X) :
    Mono (chainMap R (TopCat.of A) X (subtypeIncl X A)) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  rw [ModuleCat.mono_iff_injective]
  exact injective_chainComplexMap_subtypeIncl X A n

end

end Work.SSSR.Cohomology
