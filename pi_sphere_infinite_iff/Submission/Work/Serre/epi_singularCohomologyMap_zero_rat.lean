import Mathlib
import Submission.Work.Cohomology.epi_singularCohomologyMap_zero

/-!
# Degree zero, rational coefficients: the pullback `H⁰(Y;ℚ) ⟶ H⁰(X;ℚ)` is an epimorphism

This is the rational-coefficient companion of
`Work.Cohomology.epi_singularCohomologyMap_zero`.  Every ingredient of that proof
(`exists_cohomologyClassOf`, `genEval`/`genEval_ext`, `unitCochain` and its being a cocycle,
`eval_constancy`, `cohomologyClassOf`, `singularCohomologyMap_classOf`) is stated for an arbitrary
commutative coefficient ring `R`, so the same argument applies verbatim with `ℚ` in place of `ℤ`:
every `0`-cocycle of `X` is a scalar multiple of the augmentation of `X`, and since `X` is
path-connected that scalar is its value on any `0`-simplex, in particular on the image of one; a
suitable scalar multiple of the augmentation of `Y` is therefore a preimage.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology

namespace Work.Serre

/-- **Degree zero pullback, rational coefficients.**  For a path-connected space `X` and any
continuous map `f : X ⟶ Y`, the induced map `H⁰(Y; ℚ) ⟶ H⁰(X; ℚ)` is an epimorphism. -/
theorem epi_singularCohomologyMap_zero_rat {X Y : TopCat} [PathConnectedSpace X]
    (f : X ⟶ Y) :
    CategoryTheory.Epi (Work.Cohomology.singularCohomologyMap ℚ X Y f 0) := by
  rw [ModuleCat.epi_iff_surjective]
  intro x
  -- every cohomology class in degree `0` is the class of a `0`-cocycle `α`
  obtain ⟨α, hα, rfl⟩ := Work.Cohomology.exists_cohomologyClassOf ℚ (TopCat.toSSet.obj X) 0 x
  -- the value of `α` at the base generator, the scalar by which we scale the augmentation
  let lam : ℚ := Work.Cohomology.genEval ℚ (TopCat.toSSet.obj X) α (Work.Cohomology.baseSimplex X)
  -- the candidate preimage at the cochain level: `lam` times the augmentation of `Y`
  let β : ((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)).X 0 →ₗ[ℚ] ℚ :=
    lam • Work.Cohomology.unitCochain ℚ (TopCat.toSSet.obj Y)
  -- the candidate is a cocycle, because the augmentation is and `cochainDiff` is linear
  have hβ : Work.Cohomology.cochainDiff ℚ (TopCat.toSSet.obj Y) β = 0 := by
    have hlin : Work.Cohomology.cochainDiff ℚ (TopCat.toSSet.obj Y)
        (lam • Work.Cohomology.unitCochain ℚ (TopCat.toSSet.obj Y))
        = lam • Work.Cohomology.cochainDiff ℚ (TopCat.toSSet.obj Y)
            (Work.Cohomology.unitCochain ℚ (TopCat.toSSet.obj Y)) := by
      rw [← Work.Cohomology.cochainDiffLM_apply ℚ (TopCat.toSSet.obj Y) 0
            (lam • Work.Cohomology.unitCochain ℚ (TopCat.toSSet.obj Y)),
        map_smul, Work.Cohomology.cochainDiffLM_apply]
    rw [show β = lam • Work.Cohomology.unitCochain ℚ (TopCat.toSSet.obj Y) from rfl, hlin,
      Work.Cohomology.cochainDiff_unitCochain ℚ (TopCat.toSSet.obj Y), smul_zero]
  -- the pullback of the candidate is `α`: the two agree on the generators `sgen _`
  have hkey : (((SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ)).f 0).hom).dualMap β
      = α := by
    apply Work.Cohomology.genEval_ext
    intro s
    rw [Work.Cohomology.genEval, Work.Cohomology.genEval, LinearMap.dualMap_apply]
    -- the chain map sends the generator of a `0`-simplex to the generator of its image
    have h1 : ((SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ)).f 0)
        ((SSet.ιChainComplex (TopCat.toSSet.obj X) (R := ModuleCat.of ℚ ℚ) s).hom 1)
        = (SSet.ιChainComplex (TopCat.toSSet.obj Y) (R := ModuleCat.of ℚ ℚ)
            ((TopCat.toSSet.map f).app _ s)).hom 1 := by
      have h := congrArg (fun (m : ModuleCat.of ℚ ℚ ⟶
          ((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)).X 0) => (ModuleCat.Hom.hom m) 1)
        (SSet.ι_chainComplexMap_f (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y) (TopCat.toSSet.map f)
          (ModuleCat.of ℚ ℚ) s)
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h
    rw [h1]
    -- the value of `β` at the image generator is `lam`
    have hunit : Work.Cohomology.unitCochain ℚ (TopCat.toSSet.obj Y)
        ((SSet.ιChainComplex (TopCat.toSSet.obj Y) (R := ModuleCat.of ℚ ℚ)
          ((TopCat.toSSet.map f).app _ s)).hom 1) = 1 :=
      Work.Cohomology.genEval_unitCochain ℚ (TopCat.toSSet.obj Y) ((TopCat.toSSet.map f).app _ s)
    -- the value of `α` at every generator is `lam`, by constancy along paths in `X`
    have hα' : α.comp (ModuleCat.Hom.hom ((Work.Cohomology.singularChains ℚ X).d 1 0)) = 0 := hα
    have hconst : α ((SSet.ιChainComplex (TopCat.toSSet.obj X) (R := ModuleCat.of ℚ ℚ) s).hom 1)
        = α ((SSet.ιChainComplex (TopCat.toSSet.obj X) (R := ModuleCat.of ℚ ℚ)
            (Work.Cohomology.baseSimplex X)).hom 1) :=
      Work.Cohomology.eval_constancy ℚ X α hα' s
    rw [show β = lam • Work.Cohomology.unitCochain ℚ (TopCat.toSSet.obj Y) from rfl,
      LinearMap.smul_apply, hunit, smul_eq_mul, mul_one, hconst]
    rfl
  refine ⟨Work.Cohomology.cohomologyClassOf ℚ (TopCat.toSSet.obj Y) β hβ, ?_⟩
  change (HomologicalComplex.homologyMap (Work.Cohomology.dualChainMap ℚ X Y f) 0).hom
      (Work.Cohomology.cohomologyClassOf ℚ (TopCat.toSSet.obj Y) β hβ) =
    Work.Cohomology.cohomologyClassOf ℚ (TopCat.toSSet.obj X) α hα
  rw [Work.Cohomology.singularCohomologyMap_classOf ℚ f β hβ]
  exact Work.Cohomology.cohomologyClassOf_congr ℚ (TopCat.toSSet.obj X) hkey _ hα

end Work.Serre
