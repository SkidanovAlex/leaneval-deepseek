import Mathlib
import Submission.Work.Thom.MixedCup
import Submission.Work.Cohomology.CupRing
import Submission.Work.Cohomology.cupNaturalH
import Submission.Work.Cohomology.h0Evaluation

/-!
# Evaluation of rational degree-zero cohomology classes at a point

The `ℚ`-coefficient analogue of `Submission/Work/Cohomology/h0Evaluation.lean`
(`Work.Cohomology.h0Ev`) together with the evaluation lemmas of
`Submission/Work/StemsB/collarSqEval.lean` (which are `ℤ`-only at that path).

For a simplicial set `X` and a `0`-simplex `s`, we build

* `h0GenQ X s` — the generator of the degree-`0` chains associated with `s`;
* `h0CycIsoQ X` — the canonical identification `H⁰(X;ℚ) ≅ Z⁰(X;ℚ)`;
* `h0EvQ X s : H⁰(X;ℚ) →ₗ[ℚ] ℚ` — evaluation at `s`,

with the computation rule `h0EvQ_classOf`, its naturality under pullback `h0EvQ_CohMap`, its
multiplicativity `h0EvQ_cup` and the unit evaluation `h0EvQ_oneH`, plus the separation statements
`h0EvQ_ext` and `h0EvQ_eq_zero`.

This is the tool used by the `Work.StemsB.Rat` collar development (the "unit transfer" of the
Thom class of the collar pair), where the values of a class of `H⁰(Y;ℚ)` at the points of `Y`
have to be produced over `ℚ` instead of over `ℤ`.
-/

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

set_option autoImplicit false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Work.StemsB.Rat

noncomputable section

/-! ## The evaluation functional -/

/-- The `0`-chain associated with a `0`-simplex: the generator of the degree-zero rational
chains. -/
noncomputable def h0GenQ (X : SSet) (s : X _⦋0⦌) : (X.chainComplex (ModuleCat.of ℚ ℚ)).X 0 :=
  (X.ιChainComplex (R := ModuleCat.of ℚ ℚ) s).hom 1

/-- The zeroth rational cohomology is the module of `0`-cocycles: the canonical identification of
`H⁰` with the cycles in degree `0`, the inverse of `homologyπ`. -/
noncomputable def h0CycIsoQ (X : SSet) :
    (Work.Cohomology.SSetCochainComplex ℚ X).homology 0 ≅
      (Work.Cohomology.SSetCochainComplex ℚ X).cycles 0 :=
  (ShortComplex.asIsoHomologyπ ((Work.Cohomology.SSetCochainComplex ℚ X).sc 0) rfl).symm

/-- Evaluation of a rational `0`-cochain at a `0`-simplex, as a linear functional on the
cochains. -/
noncomputable def h0CochainEvalQ (X : SSet) (s : X _⦋0⦌) :
    Work.Cohomology.Cochain ℚ X 0 →ₗ[ℚ] ℚ where
  toFun α := α (h0GenQ X s)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Evaluation of a rational `0`-cocycle at a `0`-simplex. -/
noncomputable def h0EvCycQ (X : SSet) (s : X _⦋0⦌) :
    (Work.Cohomology.SSetCochainComplex ℚ X).cycles 0 →ₗ[ℚ] ℚ :=
  (h0CochainEvalQ X s).comp ((Work.Cohomology.SSetCochainComplex ℚ X).iCycles 0).hom

/-- **Evaluation of a rational degree-zero cohomology class at a `0`-simplex.** -/
noncomputable def h0EvQ (X : SSet) (s : X _⦋0⦌) :
    (Work.Cohomology.SSetCochainComplex ℚ X).homology 0 →ₗ[ℚ] ℚ :=
  (h0EvCycQ X s).comp (h0CycIsoQ X).hom.hom

@[simp]
theorem h0EvQCyc_apply (X : SSet) (s : X _⦋0⦌)
    (z : (Work.Cohomology.SSetCochainComplex ℚ X).cycles 0) :
    h0EvCycQ X s z
      = h0CochainEvalQ X s
          ((ModuleCat.Hom.hom ((Work.Cohomology.SSetCochainComplex ℚ X).iCycles 0)) z) := rfl

@[simp]
theorem h0EvQ_apply_iso (X : SSet) (s : X _⦋0⦌)
    (z : (Work.Cohomology.SSetCochainComplex ℚ X).cycles 0) :
    h0EvQ X s ((h0CycIsoQ X).inv z) = h0EvCycQ X s z := by
  have h := congrArg (fun (g : (Work.Cohomology.SSetCochainComplex ℚ X).cycles 0 ⟶
      (Work.Cohomology.SSetCochainComplex ℚ X).cycles 0) => ModuleCat.Hom.hom g z)
    (Iso.inv_hom_id (h0CycIsoQ X))
  simp only [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply, LinearMap.id_apply] at h
  show h0EvCycQ X s (ModuleCat.Hom.hom (h0CycIsoQ X).hom
    (ModuleCat.Hom.hom (h0CycIsoQ X).inv z)) = h0EvCycQ X s z
  rw [h]

/-- `homologyπ` is inverse to `h0CycIsoQ` on the cohomology. -/
theorem homologyπ_h0CycIsoQ_hom (X : SSet)
    (x : (Work.Cohomology.SSetCochainComplex ℚ X).homology 0) :
    ModuleCat.Hom.hom (HomologicalComplex.homologyπ
        (Work.Cohomology.SSetCochainComplex ℚ X) 0)
        (ModuleCat.Hom.hom (h0CycIsoQ X).hom x) = x := by
  have hcomp := ShortComplex.asIsoHomologyπ_inv_comp_homologyπ
    (S := (Work.Cohomology.SSetCochainComplex ℚ X).sc 0) rfl
  have h3 := congrArg (fun (g : (Work.Cohomology.SSetCochainComplex ℚ X).homology 0 ⟶
      (Work.Cohomology.SSetCochainComplex ℚ X).homology 0) => ModuleCat.Hom.hom g x) hcomp
  simp only [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply, LinearMap.id_apply] at h3
  exact h3

/-- The class of a rational cocycle is sent by `h0CycIsoQ` to the associated cycle. -/
theorem h0CycIsoQ_classOf (X : SSet) (α : Work.Cohomology.Cochain ℚ X 0)
    (hα : Work.Cohomology.cochainDiff ℚ X α = 0) :
    (h0CycIsoQ X).hom (Work.Cohomology.cohomologyClassOf ℚ X α hα) =
      Work.Cohomology.cocycleOf ℚ X α hα := by
  have hcomp := ShortComplex.homologyπ_comp_asIsoHomologyπ_inv
    (S := (Work.Cohomology.SSetCochainComplex ℚ X).sc 0) rfl
  have h3 := congrArg (fun (g : (Work.Cohomology.SSetCochainComplex ℚ X).cycles 0 ⟶
      (Work.Cohomology.SSetCochainComplex ℚ X).cycles 0) =>
        ModuleCat.Hom.hom g (Work.Cohomology.cocycleOf ℚ X α hα)) hcomp
  simp only [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply, LinearMap.id_apply] at h3
  rw [show Work.Cohomology.cohomologyClassOf ℚ X α hα =
    ModuleCat.Hom.hom (HomologicalComplex.homologyπ
      (Work.Cohomology.SSetCochainComplex ℚ X) 0)
      (Work.Cohomology.cocycleOf ℚ X α hα) from rfl]
  exact h3

/-- **The computation rule for `h0EvQ`.**  The evaluation of the class of a rational cocycle `α` at
a `0`-simplex `s` is the value of `α` on the associated generator. -/
theorem h0EvQ_classOf (X : SSet) (s : X _⦋0⦌) (α : Work.Cohomology.Cochain ℚ X 0)
    (hα : Work.Cohomology.cochainDiff ℚ X α = 0) :
    h0EvQ X s (Work.Cohomology.cohomologyClassOf ℚ X α hα) = α (h0GenQ X s) := by
  rw [show h0EvQ X s (Work.Cohomology.cohomologyClassOf ℚ X α hα) =
      h0EvCycQ X s ((h0CycIsoQ X).hom (Work.Cohomology.cohomologyClassOf ℚ X α hα)) from rfl,
    h0CycIsoQ_classOf X α hα]
  rw [h0EvQCyc_apply, Work.Cohomology.iCycles_cocycleOf]
  rfl

/-- **Every cohomology class is the class of the cocycle underlying its representing cycle.** -/
theorem h0ClassOf_iCyclesQ (X : SSet)
    (x : (Work.Cohomology.SSetCochainComplex ℚ X).homology 0) :
    Work.Cohomology.cohomologyClassOf ℚ X
        (((Work.Cohomology.SSetCochainComplex ℚ X).iCycles 0) ((h0CycIsoQ X).hom x))
        (Work.Cohomology.cochainDiff_iCycles ℚ X 0 ((h0CycIsoQ X).hom x)) = x := by
  rw [Work.Cohomology.cohomologyClassOf_eq_homologyπ]
  exact homologyπ_h0CycIsoQ_hom X x

/-! ## The evaluation lemmas -/

/-- Two classes of `H⁰(X;ℚ)` agreeing on every `0`-simplex are equal. -/
theorem h0EvQ_ext {X : Type} [TopologicalSpace X] {x y : Work.Thom.Coh ℚ 0 X}
    (h : ∀ s : (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk 0)),
      h0EvQ (TopCat.toSSet.obj (TopCat.of X)) s x
        = h0EvQ (TopCat.toSSet.obj (TopCat.of X)) s y) : x = y := by
  obtain ⟨α, hα, hx⟩ := Work.Cohomology.exists_cohomologyClassOf ℚ
    (TopCat.toSSet.obj (TopCat.of X)) 0 x
  obtain ⟨β, hβ, hy⟩ := Work.Cohomology.exists_cohomologyClassOf ℚ
    (TopCat.toSSet.obj (TopCat.of X)) 0 y
  rw [← hx, ← hy]
  apply Work.Cohomology.cohomologyClassOf_congr
  apply Work.Cohomology.genEval_ext
  intro s
  have hs := h s
  rw [← hx, ← hy, h0EvQ_classOf, h0EvQ_classOf] at hs
  simpa [Work.Cohomology.genEval, h0GenQ] using hs

/-- A class of `H⁰(X;ℚ)` all of whose evaluations vanish is zero. -/
theorem h0EvQ_eq_zero {X : Type} [TopologicalSpace X] (y : Work.Thom.Coh ℚ 0 X)
    (hy : ∀ s : (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk 0)),
      h0EvQ (TopCat.toSSet.obj (TopCat.of X)) s y = 0) : y = 0 := by
  refine h0EvQ_ext (y := 0) (fun s => ?_)
  rw [hy s]
  exact (map_zero (h0EvQ (TopCat.toSSet.obj (TopCat.of X)) s)).symm

/-- The evaluation of the unit class is `1`. -/
theorem h0EvQ_oneH {X : Type} [TopologicalSpace X]
    (s : (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk 0))) :
    h0EvQ (TopCat.toSSet.obj (TopCat.of X)) s
      (Work.Cohomology.oneH ℚ (TopCat.toSSet.obj (TopCat.of X))) = 1 := by
  rw [Work.Cohomology.oneH, h0EvQ_classOf]
  exact Work.Cohomology.genEval_unitCochain ℚ (TopCat.toSSet.obj (TopCat.of X)) s

/-- The `0`-simplex of the singular simplicial set associated with a point is natural. -/
theorem toSSetObj₀Equiv_mapQ {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y))
    (s : (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk 0))) :
    TopCat.toSSetObj₀Equiv ((TopCat.toSSet.map (TopCat.ofHom f)).app
        (Opposite.op (SimplexCategory.mk 0)) s) = f (TopCat.toSSetObj₀Equiv s) := by
  simp only [TopCat.toSSetObj₀Equiv_apply]
  rfl

/-- **Naturality of the evaluation `h0EvQ` under a pullback.** -/
theorem h0EvQ_CohMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    (s : (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk 0)))
    (y : Work.Thom.Coh ℚ 0 Y) :
    h0EvQ (TopCat.toSSet.obj (TopCat.of X)) s ((Work.Thom.CohMap f ℚ 0).hom y)
      = h0EvQ (TopCat.toSSet.obj (TopCat.of Y))
          ((TopCat.toSSet.map (TopCat.ofHom f)).app (Opposite.op (SimplexCategory.mk 0)) s) y := by
  obtain ⟨α, hα, hx⟩ := Work.Cohomology.exists_cohomologyClassOf ℚ
    (TopCat.toSSet.obj (TopCat.of Y)) 0 y
  subst hx
  show h0EvQ (TopCat.toSSet.obj (TopCat.of X)) s
      ((HomologicalComplex.homologyMap
        (Work.Cohomology.dualChainMap ℚ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f)) 0).hom
        (Work.Cohomology.cohomologyClassOf ℚ (TopCat.toSSet.obj (TopCat.of Y)) α hα))
    = h0EvQ (TopCat.toSSet.obj (TopCat.of Y))
        ((TopCat.toSSet.map (TopCat.ofHom f)).app (Opposite.op (SimplexCategory.mk 0)) s)
        (Work.Cohomology.cohomologyClassOf ℚ (TopCat.toSSet.obj (TopCat.of Y)) α hα)
  rw [Work.Cohomology.singularCohomologyMap_classOf ℚ (TopCat.ofHom f) α hα]
  rw [h0EvQ_classOf, h0EvQ_classOf]
  show (((SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f))
        (ModuleCat.of ℚ ℚ)).f 0).hom.dualMap α)
      (h0GenQ (TopCat.toSSet.obj (TopCat.of X)) s)
    = α (h0GenQ (TopCat.toSSet.obj (TopCat.of Y))
        ((TopCat.toSSet.map (TopCat.ofHom f)).app (Opposite.op (SimplexCategory.mk 0)) s))
  rw [LinearMap.dualMap_apply]
  congr 1
  have h2 := congrArg (fun (g : ModuleCat.of ℚ ℚ ⟶
      ((TopCat.toSSet.obj (TopCat.of Y)).chainComplex (ModuleCat.of ℚ ℚ)).X 0) =>
      (ModuleCat.Hom.hom g) 1)
    (SSet.ι_chainComplexMap_f (TopCat.toSSet.obj (TopCat.of X))
      (TopCat.toSSet.obj (TopCat.of Y)) (TopCat.toSSet.map (TopCat.ofHom f))
      (ModuleCat.of ℚ ℚ) s)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  exact h2

/-- **The pointwise evaluations are multiplicative in degree zero.** -/
theorem h0EvQ_cup {X : Type} [TopologicalSpace X]
    (s : (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk 0)))
    (x y : Work.Thom.Coh ℚ 0 X) :
    h0EvQ (TopCat.toSSet.obj (TopCat.of X)) s
        (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (TopCat.of X)) 0 0 x y)
      = h0EvQ (TopCat.toSSet.obj (TopCat.of X)) s x *
        h0EvQ (TopCat.toSSet.obj (TopCat.of X)) s y := by
  obtain ⟨α, hα, rfl⟩ := Work.Cohomology.exists_cohomologyClassOf ℚ
    (TopCat.toSSet.obj (TopCat.of X)) 0 x
  obtain ⟨β, hβ, rfl⟩ := Work.Cohomology.exists_cohomologyClassOf ℚ
    (TopCat.toSSet.obj (TopCat.of X)) 0 y
  rw [Work.Cohomology.cupH'_apply' ℚ _ α β hα hβ, h0EvQ_classOf, h0EvQ_classOf, h0EvQ_classOf]
  show Work.Cohomology.genEval ℚ (TopCat.toSSet.obj (TopCat.of X))
      (Work.Cohomology.cup ℚ (TopCat.toSSet.obj (TopCat.of X)) α β) s =
    Work.Cohomology.genEval ℚ (TopCat.toSSet.obj (TopCat.of X)) α s *
      Work.Cohomology.genEval ℚ (TopCat.toSSet.obj (TopCat.of X)) β s
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

end Work.StemsB.Rat
