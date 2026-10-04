import Mathlib
import Submission.Diff.Alg

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The chain rule for a `Curv4`-valued map followed by a smooth `F : Curv4 n → Curv4 n`

This module provides the two ingredients of the chain rule
`mvfderiv_F_rmFrameField`:

* the component/evaluation map `proj4 i j k l : Curv4 n →L[ℝ] ℝ` and its `fderiv`
  (`fderiv_comp_curv4`, `fderiv_comp_curv4_apply`), and
* `mvfderiv_comp_curv4`: for a smooth `F : Curv4 n → Curv4 n` and a map
  `R : M → Curv4 n` differentiable at `x`,
  `mvfderiv I (fun y => (F (R y)) i j k l) x v
     = (fderiv ℝ F (R x) (mvfderiv I R x v)) i j k l`.

The proof is the chain rule `mvfderiv_comp_apply` applied to
`R` and to the component function `fun X => (F X) i j k l`, then
`mvfderiv_eq_fderiv` and the fact that the derivative of a component of `F` is
the corresponding component of `fderiv ℝ F`.  Nothing here mentions the frame
field `rmFrameField`; the differentiability of `R` is a hypothesis.

Note on the types: `TangentSpace 𝓘(ℝ, Curv4 n) (R x)` is a (non-reducible) type
synonym for `Curv4 n`, so the `fromTangentSpace` identifications used below are
definitional; this is why the `show`/`rw` sequence below is stated with the
*explicit* model `𝓘(ℝ, Curv4 n)` rather than relying on the `d%`/`mfderiv%`
notations (which cannot infer a model with corners for a `Π`-type).
-/

open Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE.covRxnA

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M]

/-- Evaluation of a curvature array at a multi-index, as a continuous linear map. -/
def proj4 {n : ℕ} (i j k l : Fin n) : Curv4 n →L[ℝ] ℝ where
  toFun X := X i j k l
  map_add' a b := rfl
  map_smul' c a := rfl

lemma proj4_apply {n : ℕ} (i j k l : Fin n) (X : Curv4 n) :
    proj4 i j k l X = X i j k l := rfl

/-- The derivative of the `(i,j,k,l)` component of a map: it is the `(i,j,k,l)`
component of the derivative. -/
lemma fderiv_comp_curv4 {n : ℕ} (F : Curv4 n → Curv4 n) {z : Curv4 n}
    (hF : DifferentiableAt ℝ F z) (i j k l : Fin n) :
    fderiv ℝ (fun X : Curv4 n => (F X) i j k l) z = (proj4 i j k l).comp (fderiv ℝ F z) := by
  have h : HasFDerivAt (fun X : Curv4 n => proj4 i j k l (F X))
      ((proj4 i j k l).comp (fderiv ℝ F z)) z :=
    (proj4 i j k l).hasFDerivAt.comp z hF.hasFDerivAt
  have h2 := h.fderiv
  simpa only [proj4_apply] using h2

/-- Evaluated form of `fderiv_comp_curv4`. -/
lemma fderiv_comp_curv4_apply {n : ℕ} (F : Curv4 n → Curv4 n) {z : Curv4 n}
    (hF : DifferentiableAt ℝ F z) (i j k l : Fin n) (w : Curv4 n) :
    fderiv ℝ (fun X : Curv4 n => (F X) i j k l) z w = (fderiv ℝ F z w) i j k l := by
  rw [fderiv_comp_curv4 F hF i j k l, ContinuousLinearMap.comp_apply, proj4_apply]

lemma differentiableAt_comp_curv4 {n : ℕ} (F : Curv4 n → Curv4 n) {z : Curv4 n}
    (hF : DifferentiableAt ℝ F z) (i j k l : Fin n) :
    DifferentiableAt ℝ (fun X : Curv4 n => (F X) i j k l) z := by
  have h1 : DifferentiableAt ℝ (fun X : Curv4 n => proj4 i j k l (F X)) z :=
    (proj4 i j k l).differentiableAt.comp z hF
  simpa only [proj4_apply] using h1

/-- **Chain rule for the components of `F ∘ R`.**  For a smooth `F : Curv4 n → Curv4 n` and a map
`R : M → Curv4 n` differentiable at `x`, the derivative of the `(i,j,k,l)` component of
`y ↦ F (R y)` is the `(i,j,k,l)` component of `fderiv ℝ F` at `R x`, applied to the derivative of
`R`. -/
theorem mvfderiv_comp_curv4
    {n : ℕ} (F : Curv4 n → Curv4 n) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (x : M) (v : TangentSpace I x) {R : M → Curv4 n}
    (hR : MDifferentiableAt I 𝓘(ℝ, Curv4 n) R x) (i j k l : Fin n) :
    mvfderiv I (fun y : M => (F (R y)) i j k l) x v
      = (fderiv ℝ F (R x) (mvfderiv I R x v)) i j k l := by
  have hFd : DifferentiableAt ℝ F (R x) := (hF.differentiable (by simp)).differentiableAt
  have hG' : DifferentiableAt ℝ (fun X : Curv4 n => (F X) i j k l) (R x) :=
    differentiableAt_comp_curv4 F hFd i j k l
  have hG : MDifferentiableAt 𝓘(ℝ, Curv4 n) 𝓘(ℝ, ℝ)
      (fun X : Curv4 n => (F X) i j k l) (R x) := hG'.mdifferentiableAt
  show mvfderiv I ((fun X : Curv4 n => (F X) i j k l) ∘ R) x v
      = (fderiv ℝ F (R x) (mvfderiv I R x v)) i j k l
  rw [mvfderiv_comp_apply (𝕜 := ℝ) (I := 𝓘(ℝ, Curv4 n)) (I' := I)
    (f := R) (g := fun X : Curv4 n => (F X) i j k l) x hG hR v]
  rw [mvfderiv_eq_fderiv (f := fun X : Curv4 n => (F X) i j k l) (x := R x)]
  show (fderiv ℝ (fun X : Curv4 n => (F X) i j k l) (R x)) (mvfderiv I R x v)
      = (fderiv ℝ F (R x) (mvfderiv I R x v)) i j k l
  rw [fderiv_comp_curv4_apply F hFd i j k l]

end Work.Diff.GE.covRxnA
