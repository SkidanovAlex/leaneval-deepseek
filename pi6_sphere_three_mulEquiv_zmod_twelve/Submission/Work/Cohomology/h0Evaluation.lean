import Mathlib
import Submission.Work.Cohomology.Singular
import Submission.Work.Cohomology.AlexanderWhitney
import Submission.Work.Cohomology.CupRing
import Submission.Work.Cohomology.singularCohomology_zero

/-!
# Evaluating a degree-zero cohomology class at a simplex

For a simplicial set `X`, the zeroth cohomology `H⁰(X; ℤ)` is the module of `0`-cocycles, i.e. of
those linear functionals on the `0`-chains which vanish on the first differential.  In particular
such a functional may be *evaluated at a generator* `h0Gen X s` (`s` a `0`-simplex), and this
evaluation depends only on the cohomology class.

Because `H⁰ = ker d⁰` (there is nothing in degree `-1`), there is a canonical isomorphism
`h0CycIso X : H⁰(X;ℤ) ≅ Z⁰(X;ℤ)`, the inverse of `homologyπ`; this file uses it to define, for a
`0`-simplex `s`, the linear functional

`h0Ev X s : H⁰(X; ℤ) →ₗ[ℤ] ℤ`,  `x ↦ (cycle representing x)(s)`,

whose basic computational rule is `h0Ev_classOf`:
`h0Ev X s (class of a cocycle α) = α (h0Gen X s)`.

This is the degree-zero part of the statement that `H⁰` is the module of locally constant
functions on the space (with values in `ℤ`); it is the tool with which the cokernel of a pullback
`H⁰(Y) → H⁰(X)` is computed when `X` has two path components.

* `Work.Cohomology.h0Gen` — the `0`-chain of a `0`-simplex;
* `Work.Cohomology.h0CycIso` — `H⁰(X;ℤ) ≅ Z⁰(X;ℤ)`;
* `Work.Cohomology.h0Ev` — evaluation of a degree-zero cohomology class at a `0`-simplex;
* `Work.Cohomology.h0Ev_classOf`, `Work.Cohomology.h0ClassOf_iCycles` — its computation rules.
-/

open CategoryTheory AlgebraicTopology Limits Simplicial
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-- The `0`-chain associated with a `0`-simplex: the generator of the degree-zero chains. -/
noncomputable def h0Gen (X : SSet) (s : X _⦋0⦌) : (X.chainComplex (ModuleCat.of ℤ ℤ)).X 0 :=
  (X.ιChainComplex (R := ModuleCat.of ℤ ℤ) s).hom 1

/-- The zeroth cohomology is the module of `0`-cocycles: the canonical identification of `H⁰` with
the cycles in degree `0`, the inverse of `homologyπ`. -/
noncomputable def h0CycIso (X : SSet) :
    (SSetCochainComplex ℤ X).homology 0 ≅ (SSetCochainComplex ℤ X).cycles 0 :=
  (ShortComplex.asIsoHomologyπ ((SSetCochainComplex ℤ X).sc 0) rfl).symm

/-- Evaluation of a `0`-cochain at a `0`-simplex, as a linear functional on the cochains. -/
noncomputable def h0CochainEval (X : SSet) (s : X _⦋0⦌) : Cochain ℤ X 0 →ₗ[ℤ] ℤ where
  toFun α := α (h0Gen X s)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Evaluation of a `0`-cocycle at a `0`-simplex. -/
noncomputable def h0EvCyc (X : SSet) (s : X _⦋0⦌) : (SSetCochainComplex ℤ X).cycles 0 →ₗ[ℤ] ℤ :=
  (h0CochainEval X s).comp ((SSetCochainComplex ℤ X).iCycles 0).hom

/-- **Evaluation of a degree-zero cohomology class at a `0`-simplex.** -/
noncomputable def h0Ev (X : SSet) (s : X _⦋0⦌) : (SSetCochainComplex ℤ X).homology 0 →ₗ[ℤ] ℤ :=
  (h0EvCyc X s).comp (h0CycIso X).hom.hom

@[simp]
theorem h0EvCyc_apply (X : SSet) (s : X _⦋0⦌) (z : (SSetCochainComplex ℤ X).cycles 0) :
    h0EvCyc X s z
      = h0CochainEval X s ((ModuleCat.Hom.hom ((SSetCochainComplex ℤ X).iCycles 0)) z) := rfl

@[simp]
theorem h0Ev_apply_iso (X : SSet) (s : X _⦋0⦌) (z : (SSetCochainComplex ℤ X).cycles 0) :
    h0Ev X s ((h0CycIso X).inv z) = h0EvCyc X s z := by
  have h := congrArg (fun (g : (SSetCochainComplex ℤ X).cycles 0 ⟶
      (SSetCochainComplex ℤ X).cycles 0) => ModuleCat.Hom.hom g z)
    (Iso.inv_hom_id (h0CycIso X))
  simp only [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply, LinearMap.id_apply] at h
  show h0EvCyc X s (ModuleCat.Hom.hom (h0CycIso X).hom
    (ModuleCat.Hom.hom (h0CycIso X).inv z)) = _
  rw [h]

/-- `homologyπ` is inverse to `h0CycIso` on the cohomology. -/
theorem homologyπ_h0CycIso_hom (X : SSet) (x : (SSetCochainComplex ℤ X).homology 0) :
    ModuleCat.Hom.hom (HomologicalComplex.homologyπ (SSetCochainComplex ℤ X) 0)
        (ModuleCat.Hom.hom (h0CycIso X).hom x) = x := by
  have hcomp := ShortComplex.asIsoHomologyπ_inv_comp_homologyπ
    (S := (SSetCochainComplex ℤ X).sc 0) rfl
  have h3 := congrArg (fun (g : (SSetCochainComplex ℤ X).homology 0 ⟶
      (SSetCochainComplex ℤ X).homology 0) => ModuleCat.Hom.hom g x) hcomp
  simp only [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply, LinearMap.id_apply] at h3
  exact h3

/-- The class of a cocycle is sent by `h0CycIso` to the associated cycle. -/
theorem h0CycIso_classOf (X : SSet) (α : Cochain ℤ X 0) (hα : cochainDiff ℤ X α = 0) :
    (h0CycIso X).hom (cohomologyClassOf ℤ X α hα) = cocycleOf ℤ X α hα := by
  have hcomp := ShortComplex.homologyπ_comp_asIsoHomologyπ_inv
    (S := (SSetCochainComplex ℤ X).sc 0) rfl
  have h3 := congrArg (fun (g : (SSetCochainComplex ℤ X).cycles 0 ⟶
      (SSetCochainComplex ℤ X).cycles 0) => ModuleCat.Hom.hom g (cocycleOf ℤ X α hα)) hcomp
  simp only [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply, LinearMap.id_apply] at h3
  rw [show cohomologyClassOf ℤ X α hα =
    ModuleCat.Hom.hom (HomologicalComplex.homologyπ (SSetCochainComplex ℤ X) 0)
      (cocycleOf ℤ X α hα) from rfl]
  exact h3

/-- **The computation rule for `h0Ev`.**  The evaluation of the class of a cocycle `α` at a
`0`-simplex `s` is the value of `α` on the associated generator. -/
theorem h0Ev_classOf (X : SSet) (s : X _⦋0⦌) (α : Cochain ℤ X 0)
    (hα : cochainDiff ℤ X α = 0) :
    h0Ev X s (cohomologyClassOf ℤ X α hα) = α (h0Gen X s) := by
  rw [show h0Ev X s (cohomologyClassOf ℤ X α hα) =
      h0EvCyc X s ((h0CycIso X).hom (cohomologyClassOf ℤ X α hα)) from rfl,
    h0CycIso_classOf X α hα]
  rw [h0EvCyc_apply, iCycles_cocycleOf]
  rfl

/-- **Every cohomology class is the class of the cocycle underlying its representing cycle.** -/
theorem h0ClassOf_iCycles (X : SSet) (x : (SSetCochainComplex ℤ X).homology 0) :
    cohomologyClassOf ℤ X
        (((SSetCochainComplex ℤ X).iCycles 0) ((h0CycIso X).hom x))
        (cochainDiff_iCycles ℤ X 0 ((h0CycIso X).hom x)) = x := by
  rw [cohomologyClassOf_eq_homologyπ]
  exact homologyπ_h0CycIso_hom X x

end

end Work.Cohomology
