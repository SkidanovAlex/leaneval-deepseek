import Mathlib
import Submission.Work.Thom.MixedCup
import Submission.Work.Cohomology.CupRing
import Submission.Work.Cohomology.cupNaturalH
import Submission.Work.Cohomology.h0Evaluation

set_option autoImplicit false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Work.StemsB

open CategoryTheory CategoryTheory.Limits
open scoped Topology Simplicial

noncomputable section

/-! ## The degree-zero evaluation facts -/

/-- Two classes of `H⁰(X;ℤ)` agreeing on every `0`-simplex are equal. -/
theorem h0Ev_ext' {X : Type} [TopologicalSpace X] {x y : Work.Thom.Coh ℤ 0 X}
    (h : ∀ s : (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk 0)),
      Work.Cohomology.h0Ev (TopCat.toSSet.obj (TopCat.of X)) s x
        = Work.Cohomology.h0Ev (TopCat.toSSet.obj (TopCat.of X)) s y) : x = y := by
  obtain ⟨α, hα, hx⟩ := Work.Cohomology.exists_cohomologyClassOf ℤ
    (TopCat.toSSet.obj (TopCat.of X)) 0 x
  obtain ⟨β, hβ, hy⟩ := Work.Cohomology.exists_cohomologyClassOf ℤ
    (TopCat.toSSet.obj (TopCat.of X)) 0 y
  rw [← hx, ← hy]
  apply Work.Cohomology.cohomologyClassOf_congr
  apply Work.Cohomology.genEval_ext
  intro s
  have hs := h s
  rw [← hx, ← hy, Work.Cohomology.h0Ev_classOf, Work.Cohomology.h0Ev_classOf] at hs
  simpa [Work.Cohomology.genEval, Work.Cohomology.h0Gen] using hs

/-- A class of `H⁰(X;ℤ)` all of whose evaluations vanish is zero. -/
theorem h0Ev_eq_zero' {X : Type} [TopologicalSpace X] (y : Work.Thom.Coh ℤ 0 X)
    (hy : ∀ s : (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk 0)),
      Work.Cohomology.h0Ev (TopCat.toSSet.obj (TopCat.of X)) s y = 0) : y = 0 := by
  refine h0Ev_ext' (y := 0) (fun s => ?_)
  rw [hy s]
  exact (map_zero (Work.Cohomology.h0Ev (TopCat.toSSet.obj (TopCat.of X)) s)).symm

/-- The evaluation of the unit class is `1`. -/
theorem h0Ev_oneH' {X : Type} [TopologicalSpace X]
    (s : (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk 0))) :
    Work.Cohomology.h0Ev (TopCat.toSSet.obj (TopCat.of X)) s
      (Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of X))) = 1 := by
  rw [Work.Cohomology.oneH, Work.Cohomology.h0Ev_classOf]
  exact Work.Cohomology.genEval_unitCochain ℤ (TopCat.toSSet.obj (TopCat.of X)) s

/-- The `0`-simplex of the singular simplicial set associated with a point is natural. -/
theorem toSSetObj₀Equiv_map' {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y))
    (s : (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk 0))) :
    TopCat.toSSetObj₀Equiv ((TopCat.toSSet.map (TopCat.ofHom f)).app
        (Opposite.op (SimplexCategory.mk 0)) s) = f (TopCat.toSSetObj₀Equiv s) := by
  simp only [TopCat.toSSetObj₀Equiv_apply]
  rfl

/-- **Naturality of the evaluation `h0Ev` under a pullback.** -/
theorem h0Ev_CohMap' {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    (s : (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk 0)))
    (y : Work.Thom.Coh ℤ 0 Y) :
    Work.Cohomology.h0Ev (TopCat.toSSet.obj (TopCat.of X)) s
        ((Work.Thom.CohMap f ℤ 0).hom y)
      = Work.Cohomology.h0Ev (TopCat.toSSet.obj (TopCat.of Y))
          ((TopCat.toSSet.map (TopCat.ofHom f)).app (Opposite.op (SimplexCategory.mk 0)) s) y := by
  obtain ⟨α, hα, hx⟩ := Work.Cohomology.exists_cohomologyClassOf ℤ
    (TopCat.toSSet.obj (TopCat.of Y)) 0 y
  subst hx
  show Work.Cohomology.h0Ev (TopCat.toSSet.obj (TopCat.of X)) s
      ((HomologicalComplex.homologyMap
        (Work.Cohomology.dualChainMap ℤ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f)) 0).hom
        (Work.Cohomology.cohomologyClassOf ℤ (TopCat.toSSet.obj (TopCat.of Y)) α hα))
    = Work.Cohomology.h0Ev (TopCat.toSSet.obj (TopCat.of Y))
        ((TopCat.toSSet.map (TopCat.ofHom f)).app (Opposite.op (SimplexCategory.mk 0)) s)
        (Work.Cohomology.cohomologyClassOf ℤ (TopCat.toSSet.obj (TopCat.of Y)) α hα)
  rw [Work.Cohomology.singularCohomologyMap_classOf ℤ (TopCat.ofHom f) α hα]
  rw [Work.Cohomology.h0Ev_classOf, Work.Cohomology.h0Ev_classOf]
  show (((SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f))
        (ModuleCat.of ℤ ℤ)).f 0).hom.dualMap α)
      (Work.Cohomology.h0Gen (TopCat.toSSet.obj (TopCat.of X)) s)
    = α (Work.Cohomology.h0Gen (TopCat.toSSet.obj (TopCat.of Y))
        ((TopCat.toSSet.map (TopCat.ofHom f)).app (Opposite.op (SimplexCategory.mk 0)) s))
  rw [LinearMap.dualMap_apply]
  congr 1
  have h2 := congrArg (fun (g : ModuleCat.of ℤ ℤ ⟶
      ((TopCat.toSSet.obj (TopCat.of Y)).chainComplex (ModuleCat.of ℤ ℤ)).X 0) =>
      (ModuleCat.Hom.hom g) 1)
    (SSet.ι_chainComplexMap_f (TopCat.toSSet.obj (TopCat.of X))
      (TopCat.toSSet.obj (TopCat.of Y)) (TopCat.toSSet.map (TopCat.ofHom f))
      (ModuleCat.of ℤ ℤ) s)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  exact h2

/-- **The pointwise evaluations are multiplicative in degree zero.** -/
theorem h0Ev_cup' {X : Type} [TopologicalSpace X]
    (s : (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk 0)))
    (x y : Work.Thom.Coh ℤ 0 X) :
    Work.Cohomology.h0Ev (TopCat.toSSet.obj (TopCat.of X)) s
        (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of X)) 0 0 x y)
      = Work.Cohomology.h0Ev (TopCat.toSSet.obj (TopCat.of X)) s x *
        Work.Cohomology.h0Ev (TopCat.toSSet.obj (TopCat.of X)) s y := by
  obtain ⟨α, hα, rfl⟩ := Work.Cohomology.exists_cohomologyClassOf ℤ
    (TopCat.toSSet.obj (TopCat.of X)) 0 x
  obtain ⟨β, hβ, rfl⟩ := Work.Cohomology.exists_cohomologyClassOf ℤ
    (TopCat.toSSet.obj (TopCat.of X)) 0 y
  rw [Work.Cohomology.cupH'_apply' ℤ _ α β hα hβ, Work.Cohomology.h0Ev_classOf,
    Work.Cohomology.h0Ev_classOf, Work.Cohomology.h0Ev_classOf]
  show Work.Cohomology.genEval ℤ (TopCat.toSSet.obj (TopCat.of X))
      (Work.Cohomology.cup ℤ (TopCat.toSSet.obj (TopCat.of X)) α β) s =
    Work.Cohomology.genEval ℤ (TopCat.toSSet.obj (TopCat.of X)) α s *
      Work.Cohomology.genEval ℤ (TopCat.toSSet.obj (TopCat.of X)) β s
  rw [Work.Cohomology.cup_apply]
  rw [show Work.Cohomology.frontFace (TopCat.toSSet.obj (TopCat.of X)) 0 (0 + 0)
      (Nat.le_add_right 0 0) s = s from by
    haveI : Subsingleton (⦋0⦌ ⟶ ⦋0+0⦌) := (inferInstance : Subsingleton (⦋0⦌ ⟶ ⦋0⦌))
    have h : Work.Cohomology.frontIncl 0 (0+0) (Nat.le_add_right 0 0) =
        𝟙 (⦋0⦌ : SimplexCategory) := Subsingleton.elim _ _
    rw [Work.Cohomology.frontFace, h, op_id]
    simp]
  rw [show Work.Cohomology.backFace (TopCat.toSSet.obj (TopCat.of X)) 0 0 s = s from by
    haveI : Subsingleton (⦋0⦌ ⟶ ⦋0+0⦌) := (inferInstance : Subsingleton (⦋0⦌ ⟶ ⦋0⦌))
    have h : Work.Cohomology.backIncl 0 0 = 𝟙 (⦋0⦌ : SimplexCategory) := Subsingleton.elim _ _
    rw [Work.Cohomology.backFace, h, op_id]
    simp]

end

end Work.StemsB
