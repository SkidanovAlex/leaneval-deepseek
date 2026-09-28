import Mathlib
import Submission.Work.StemsB.Rat.H0EvalRat

namespace Work.StemsB.Rat

/-!
# The unit group of `H⁰(X;ℚ)`

`H⁰(X;ℚ)` is the ring of locally constant `ℚ`-valued functions on `X` (evaluated at the points of
`X` by `Work.StemsB.Rat.h0EvQ`): a `0`-cocycle on `X` is constant on the connected components of
`X`, so all the information it carries is a function `π₀ X → ℚ`, and conversely any function
`π₀ X → ℚ` is realized by a `0`-cocycle.

The point of this file is the accompanying *algebraic* fact: a class all of whose point evaluations
are non-zero is a unit of the ring `H⁰(X;ℚ)`.  We only ask here for a right inverse under the cup
product, which is what the collar development needs.

The construction is the following.  A `0`-cocycle `α` is a linear functional on the degree-`0`
chains which kills the differential `d 1 0`; hence it factors as `π₀.fromChainComplexXZero ≫ h`
through the cokernel `∐_{c : π₀ X} ℚ` of `d 1 0`.  On the `c`-th summand `h` acts as multiplication
by a scalar `φ c` (it is an endomorphism of `ℚ`), and `α (h0GenQ X s) = φ (π₀.mk s)`.  If all the
`α (h0GenQ X s)` are non-zero, then all the `φ c` are, and replacing each `φ c` by `φ c⁻¹` defines
another `0`-cocycle `β` with `α (h0GenQ X s) * β (h0GenQ X s) = 1`.  By multiplicativity of the
evaluation `h0EvQ_cup` and the fact that the evaluations separate classes (`h0EvQ_ext`), the class
of `β` is a right inverse of the class of `α`.
-/

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

/-- The factorisation of a `0`-cocycle `α` through the cokernel `∐_{c : π₀ X} ℚ` of the first
differential of the chain complex of `X`. -/
noncomputable def pi0Factor (Xs : SSet) (α : Work.Cohomology.Cochain ℚ Xs 0)
    (hα : Work.Cohomology.cochainDiff ℚ Xs α = 0) :
    (∐ (fun _ : SSet.π₀ Xs => ModuleCat.of ℚ ℚ)) ⟶ ModuleCat.of ℚ ℚ :=
  (CokernelCofork.IsColimit.desc'
    (SSet.isColimitCokernelCoforkChainComplexDOneZero Xs (ModuleCat.of ℚ ℚ))
    (ModuleCat.ofHom α) (by
      apply ModuleCat.hom_ext
      rw [ModuleCat.hom_comp, ModuleCat.hom_zero, ModuleCat.hom_ofHom]
      exact hα)).1

/-- The defining factorisation property of `pi0Factor`. -/
theorem pi0Factor_fac (Xs : SSet) (α : Work.Cohomology.Cochain ℚ Xs 0)
    (hα : Work.Cohomology.cochainDiff ℚ Xs α = 0) :
    Cofork.π (CokernelCofork.ofπ (SSet.π₀.fromChainComplexXZero Xs (ModuleCat.of ℚ ℚ))
        (SSet.π₀.d_fromChainComplexXZero Xs (ModuleCat.of ℚ ℚ) 1)) ≫ pi0Factor Xs α hα
      = ModuleCat.ofHom α := by
  unfold pi0Factor
  exact (CokernelCofork.IsColimit.desc' _ _ _).2

/-- The scalar by which a `0`-cocycle acts on the connected component `c` of `X`. -/
noncomputable def pScal (Xs : SSet) (α : Work.Cohomology.Cochain ℚ Xs 0)
    (hα : Work.Cohomology.cochainDiff ℚ Xs α = 0) (c : SSet.π₀ Xs) : ℚ :=
  (ModuleCat.Hom.hom (pi0Factor Xs α hα))
    ((ModuleCat.Hom.hom (Sigma.ι (fun _ : SSet.π₀ Xs => ModuleCat.of ℚ ℚ) c)) 1)

/-- The value of the `0`-cocycle `α` on a generator is its scalar on the connected component of
the generator. -/
theorem genEval_pi0Factor (Xs : SSet) (α : Work.Cohomology.Cochain ℚ Xs 0)
    (hα : Work.Cohomology.cochainDiff ℚ Xs α = 0) (s : Xs _⦋0⦌) :
    α (h0GenQ Xs s) = pScal Xs α hα (SSet.π₀.mk s) := by
  have hπ : (ModuleCat.Hom.hom (Sigma.ι (fun _ : SSet.π₀ Xs => ModuleCat.of ℚ ℚ)
          (SSet.π₀.mk s))) 1
      = (ModuleCat.Hom.hom (SSet.π₀.fromChainComplexXZero Xs (ModuleCat.of ℚ ℚ)))
        ((ModuleCat.Hom.hom (Xs.ιChainComplex (R := ModuleCat.of ℚ ℚ) s)) 1) := by
    have hh := congrArg (fun k => (ModuleCat.Hom.hom k) 1)
      (SSet.π₀.comp_fromChainComplexXZero (X := Xs) (R := ModuleCat.of ℚ ℚ) s)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hh.symm
  have h2 := congrArg ModuleCat.Hom.hom (pi0Factor_fac Xs α hα)
  rw [CokernelCofork.π_ofπ, ModuleCat.hom_comp, ModuleCat.hom_ofHom] at h2
  have h3 := LinearMap.congr_fun h2
    ((ModuleCat.Hom.hom (Xs.ιChainComplex (R := ModuleCat.of ℚ ℚ) s)) 1)
  rw [LinearMap.comp_apply] at h3
  show _ = (ModuleCat.Hom.hom (pi0Factor Xs α hα))
    ((ModuleCat.Hom.hom (Sigma.ι (fun _ : SSet.π₀ Xs => ModuleCat.of ℚ ℚ) (SSet.π₀.mk s))) 1)
  rw [hπ]
  exact h3.symm

/-- The morphism `∐_{c : π₀ X} ℚ ⟶ ℚ` which inverts the scalars of the factorisation of `α`. -/
noncomputable def invMor (Xs : SSet) (α : Work.Cohomology.Cochain ℚ Xs 0)
    (hα : Work.Cohomology.cochainDiff ℚ Xs α = 0) :
    (∐ (fun _ : SSet.π₀ Xs => ModuleCat.of ℚ ℚ)) ⟶ ModuleCat.of ℚ ℚ :=
  Sigma.desc (fun c : SSet.π₀ Xs =>
    ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ ℚ (pScal Xs α hα c)⁻¹))

/-- The `0`-cochain whose values are the inverses of the values of `α`: the pointwise inverse
`0`-cochain. -/
noncomputable def invCocycle (Xs : SSet) (α : Work.Cohomology.Cochain ℚ Xs 0)
    (hα : Work.Cohomology.cochainDiff ℚ Xs α = 0) : Work.Cohomology.Cochain ℚ Xs 0 :=
  ModuleCat.Hom.hom (SSet.π₀.fromChainComplexXZero Xs (ModuleCat.of ℚ ℚ) ≫ invMor Xs α hα)

/-- The pointwise inverse of a `0`-cocycle is a `0`-cocycle. -/
theorem invCocycle_cocycle (Xs : SSet) (α : Work.Cohomology.Cochain ℚ Xs 0)
    (hα : Work.Cohomology.cochainDiff ℚ Xs α = 0) :
    Work.Cohomology.cochainDiff ℚ Xs (invCocycle Xs α hα) = 0 := by
  have h : (Xs.chainComplex (ModuleCat.of ℚ ℚ)).d 1 0 ≫
      (SSet.π₀.fromChainComplexXZero Xs (ModuleCat.of ℚ ℚ) ≫ invMor Xs α hα) = 0 := by
    rw [← Category.assoc, SSet.π₀.d_fromChainComplexXZero, zero_comp]
  have h2 := congrArg ModuleCat.Hom.hom h
  rw [ModuleCat.hom_comp, ModuleCat.hom_zero] at h2
  exact h2

/-- The pointwise inverse of `α` really is the pointwise inverse: on a generator the two values
multiply to `1`, provided the value of `α` there is non-zero. -/
theorem invCocycle_genEval (Xs : SSet) (α : Work.Cohomology.Cochain ℚ Xs 0)
    (hα : Work.Cohomology.cochainDiff ℚ Xs α = 0) (s : Xs _⦋0⦌)
    (hne : α (h0GenQ Xs s) ≠ 0) :
    α (h0GenQ Xs s) * invCocycle Xs α hα (h0GenQ Xs s) = 1 := by
  have hval : invCocycle Xs α hα (h0GenQ Xs s) = (pScal Xs α hα (SSet.π₀.mk s))⁻¹ := by
    have hπ : (ModuleCat.Hom.hom (Sigma.ι (fun _ : SSet.π₀ Xs => ModuleCat.of ℚ ℚ)
            (SSet.π₀.mk s))) 1
        = (ModuleCat.Hom.hom (SSet.π₀.fromChainComplexXZero Xs (ModuleCat.of ℚ ℚ)))
          ((ModuleCat.Hom.hom (Xs.ιChainComplex (R := ModuleCat.of ℚ ℚ) s)) 1) := by
      have hh := congrArg (fun k => (ModuleCat.Hom.hom k) 1)
        (SSet.π₀.comp_fromChainComplexXZero (X := Xs) (R := ModuleCat.of ℚ ℚ) s)
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hh.symm
    show (ModuleCat.Hom.hom (SSet.π₀.fromChainComplexXZero Xs (ModuleCat.of ℚ ℚ) ≫
        invMor Xs α hα)) ((Xs.ιChainComplex (R := ModuleCat.of ℚ ℚ) s).hom 1) = _
    rw [ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [← hπ]
    rw [invMor]
    have h := congrArg (fun k => (ModuleCat.Hom.hom k) 1)
      (Sigma.ι_desc (fun c : SSet.π₀ Xs =>
        ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ ℚ (pScal Xs α hα c)⁻¹)) (SSet.π₀.mk s))
    rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    rw [h]
    simp [LinearMap.toSpanSingleton_apply, smul_eq_mul]
  have ha : pScal Xs α hα (SSet.π₀.mk s) ≠ 0 := by
    rw [← genEval_pi0Factor Xs α hα s]
    exact hne
  rw [genEval_pi0Factor Xs α hα s, hval]
  exact mul_inv_cancel₀ ha

/-! `H⁰(X;ℚ)` is the ring of locally constant `ℚ`-valued functions on `X` (evaluated at the points
of `X` by `Work.StemsB.Rat.h0EvQ`), so a class all of whose point evaluations are non-zero is a unit
of the ring `H⁰(X;ℚ)`; here we only ask for a right inverse under the cup product.

Suggested route: write `u` as the class of a rational `0`-cocycle `α`
(`Work.Cohomology.exists_cohomologyClassOf`), use `Work.StemsB.Rat.h0EvQ_classOf` to see that `α`
takes non-zero values on the generators of the `ℚ`-chains, factor `α` through the cokernel of
`d 1 0` (`SSet.isColimitCokernelCoforkChainComplexDOneZero`, cf.
`Work.Cohomology.tcc_sgen_congr_of_pi0`), giving a function `φ : π₀ X → ℚ` with
`α (h0GenQ X s) = φ (SSet.π₀.mk s)`, and build the inverse cocycle `β` as
`SSet.π₀.fromChainComplexXZero X (ModuleCat.of ℚ ℚ) ≫ Sigma.desc (fun c => φ c)⁻¹` (which is a
cocycle because `SSet.π₀.d_fromChainComplexXZero`), so that
`α (h0GenQ X s) * β (h0GenQ X s) = 1`.  Finish with `h0EvQ_cup`, `h0EvQ_oneH` and `h0EvQ_ext`. -/
theorem H0UnitRat {X : Type} [TopologicalSpace X] (u : Work.Thom.Coh ℚ 0 X)
    (hu : ∀ s : (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk 0)),
      Work.StemsB.Rat.h0EvQ (TopCat.toSSet.obj (TopCat.of X)) s u ≠ 0) :
    ∃ v : Work.Thom.Coh ℚ 0 X,
      Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (TopCat.of X)) 0 0 u v
        = Work.Cohomology.oneH ℚ (TopCat.toSSet.obj (TopCat.of X)) := by
  classical
  obtain ⟨α, hα, hαu⟩ := Work.Cohomology.exists_cohomologyClassOf ℚ
    (TopCat.toSSet.obj (TopCat.of X)) 0 u
  refine ⟨Work.Cohomology.cohomologyClassOf ℚ (TopCat.toSSet.obj (TopCat.of X))
    (invCocycle _ α hα) (invCocycle_cocycle _ α hα), ?_⟩
  apply h0EvQ_ext
  intro s
  have hvalα : h0EvQ (TopCat.toSSet.obj (TopCat.of X)) s u
      = α (h0GenQ (TopCat.toSSet.obj (TopCat.of X)) s) := by
    rw [← hαu]
    exact h0EvQ_classOf _ s α hα
  have hvalβ : h0EvQ (TopCat.toSSet.obj (TopCat.of X)) s
        (Work.Cohomology.cohomologyClassOf ℚ (TopCat.toSSet.obj (TopCat.of X))
          (invCocycle _ α hα) (invCocycle_cocycle _ α hα))
      = invCocycle (TopCat.toSSet.obj (TopCat.of X)) α hα
          (h0GenQ (TopCat.toSSet.obj (TopCat.of X)) s) :=
    h0EvQ_classOf _ s _ _
  rw [h0EvQ_cup, h0EvQ_oneH, hvalα, hvalβ]
  exact invCocycle_genEval _ α hα s (by rw [← hvalα]; exact hu s)

end

end Work.StemsB.Rat
