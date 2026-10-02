import Mathlib
import Submission.Work.Cohomology.Singular
import Submission.Work.Cohomology.Pullback
import Submission.Work.Cohomology.singularCohomology_zero
import Submission.Work.Cohomology.cupNaturalH

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Degree zero: the pullback `H⁰(Y;ℤ) ⟶ H⁰(X;ℤ)` is an epimorphism

For a path-connected space `X` and an arbitrary continuous map `f : X ⟶ Y`, the induced map

`f* : H⁰(Y; ℤ) ⟶ H⁰(X; ℤ)`

on singular cohomology in degree `0` is surjective.  This is the degree-`0` case of the fact that
the degree-`0` part of the cohomology of a space `Z` is the ring of locally constant functions
`π₀ Z → ℤ`: if `X` is path-connected then `H⁰(X;ℤ) ≅ ℤ` (`Work.Cohomology.singularCohomology_zero`)
and `H⁰(Y;ℤ) ⟶ H⁰(X;ℤ)` is the evaluation at the component of `f (X)`, which is onto.

Concretely, the proof reduces — through `Work.Cohomology.singularCohomologyMap_classOf`, which
computes `f*` on the class of a cocycle — to the following statement at the cochain level:

> every `0`-cocycle `α` of `X` is the pullback along `f` of some `0`-cocycle `β` of `Y`.

Take `λ := α (sgen s₀)` for a chosen base point of `X` and `β := λ • unitCochain`, the
multiple of the augmentation of `Y`.  Then `β` is a cocycle (the augmentation is), and the
pullback of `β` is `α`: on the generators `sgen s` of the zeroth chains of `X`, the value of the
pullback is `β (sgen (f s)) = λ`, while `α (sgen s) = λ` because `α` is constant on generators
(`Work.Cohomology.eval_constancy`, which uses the path-connectedness of `X`); two `0`-cocycles
agreeing on all generators are equal.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology

namespace Work.Cohomology

/-- **Degree zero pullback.**  For a path-connected space `X` and any continuous map
`f : X ⟶ Y`, the induced map `H⁰(Y; ℤ) ⟶ H⁰(X; ℤ)` is an epimorphism. -/
theorem epi_singularCohomologyMap_zero {X Y : TopCat} [PathConnectedSpace X] (f : X ⟶ Y) :
    CategoryTheory.Epi (Work.Cohomology.singularCohomologyMap ℤ X Y f 0) := by
  rw [ModuleCat.epi_iff_surjective]
  intro x
  -- every cohomology class in degree `0` is the class of a `0`-cocycle `α`
  obtain ⟨α, hα, rfl⟩ := Work.Cohomology.exists_cohomologyClassOf ℤ (TopCat.toSSet.obj X) 0 x
  -- the value of `α` at the base generator, the scalar by which we scale the augmentation
  let lam : ℤ := Work.Cohomology.genEval ℤ (TopCat.toSSet.obj X) α (Work.Cohomology.baseSimplex X)
  -- the candidate preimage at the cochain level: `lam` times the augmentation of `Y`
  let β : ((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℤ ℤ)).X 0 →ₗ[ℤ] ℤ :=
    lam • Work.Cohomology.unitCochain ℤ (TopCat.toSSet.obj Y)
  -- the candidate is a cocycle, because the augmentation is and `cochainDiff` is linear
  have hβ : Work.Cohomology.cochainDiff ℤ (TopCat.toSSet.obj Y) β = 0 := by
    have hlin : Work.Cohomology.cochainDiff ℤ (TopCat.toSSet.obj Y)
        (lam • Work.Cohomology.unitCochain ℤ (TopCat.toSSet.obj Y))
        = lam • Work.Cohomology.cochainDiff ℤ (TopCat.toSSet.obj Y)
            (Work.Cohomology.unitCochain ℤ (TopCat.toSSet.obj Y)) := by
      rw [← Work.Cohomology.cochainDiffLM_apply ℤ (TopCat.toSSet.obj Y) 0
            (lam • Work.Cohomology.unitCochain ℤ (TopCat.toSSet.obj Y)),
        map_smul, Work.Cohomology.cochainDiffLM_apply]
    rw [show β = lam • Work.Cohomology.unitCochain ℤ (TopCat.toSSet.obj Y) from rfl, hlin,
      Work.Cohomology.cochainDiff_unitCochain ℤ (TopCat.toSSet.obj Y), smul_zero]
  -- the pullback of the candidate is `α`: the two agree on the generators `sgen _
  have hkey : (((SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℤ ℤ)).f 0).hom).dualMap β
      = α := by
    apply Work.Cohomology.genEval_ext
    intro s
    rw [Work.Cohomology.genEval, Work.Cohomology.genEval, LinearMap.dualMap_apply]
    -- the chain map sends the generator of a `0`-simplex to the generator of its image
    have h1 : ((SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℤ ℤ)).f 0)
        ((SSet.ιChainComplex (TopCat.toSSet.obj X) (R := ModuleCat.of ℤ ℤ) s).hom 1)
        = (SSet.ιChainComplex (TopCat.toSSet.obj Y) (R := ModuleCat.of ℤ ℤ)
            ((TopCat.toSSet.map f).app _ s)).hom 1 := by
      have h := congrArg (fun (m : ModuleCat.of ℤ ℤ ⟶
          ((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℤ ℤ)).X 0) => (ModuleCat.Hom.hom m) 1)
        (SSet.ι_chainComplexMap_f (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y) (TopCat.toSSet.map f)
          (ModuleCat.of ℤ ℤ) s)
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h
    rw [h1]
    -- the value of `β` at the image generator is `lam`
    have hunit : Work.Cohomology.unitCochain ℤ (TopCat.toSSet.obj Y)
        ((SSet.ιChainComplex (TopCat.toSSet.obj Y) (R := ModuleCat.of ℤ ℤ)
          ((TopCat.toSSet.map f).app _ s)).hom 1) = 1 :=
      Work.Cohomology.genEval_unitCochain ℤ (TopCat.toSSet.obj Y) ((TopCat.toSSet.map f).app _ s)
    -- the value of `α` at every generator is `lam`, by constancy along paths in `X`
    have hα' : α.comp (ModuleCat.Hom.hom ((Work.Cohomology.singularChains ℤ X).d 1 0)) = 0 := hα
    have hconst : α ((SSet.ιChainComplex (TopCat.toSSet.obj X) (R := ModuleCat.of ℤ ℤ) s).hom 1)
        = α ((SSet.ιChainComplex (TopCat.toSSet.obj X) (R := ModuleCat.of ℤ ℤ)
            (Work.Cohomology.baseSimplex X)).hom 1) :=
      Work.Cohomology.eval_constancy ℤ X α hα' s
    rw [show β = lam • Work.Cohomology.unitCochain ℤ (TopCat.toSSet.obj Y) from rfl,
      LinearMap.smul_apply, hunit, smul_eq_mul, mul_one, hconst]
    rfl
  refine ⟨Work.Cohomology.cohomologyClassOf ℤ (TopCat.toSSet.obj Y) β hβ, ?_⟩
  change (HomologicalComplex.homologyMap (Work.Cohomology.dualChainMap ℤ X Y f) 0).hom
      (Work.Cohomology.cohomologyClassOf ℤ (TopCat.toSSet.obj Y) β hβ) =
    Work.Cohomology.cohomologyClassOf ℤ (TopCat.toSSet.obj X) α hα
  rw [Work.Cohomology.singularCohomologyMap_classOf ℤ f β hβ]
  exact Work.Cohomology.cohomologyClassOf_congr ℤ (TopCat.toSSet.obj X) hkey _ hα

end Work.Cohomology
