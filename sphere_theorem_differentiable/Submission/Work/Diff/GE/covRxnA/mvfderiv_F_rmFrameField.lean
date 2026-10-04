import Mathlib
import Submission.Work.Diff.GE.covRxn.Defs
import Submission.Work.Diff.GE.dRmPhi

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The chain rule for the component of `F` applied to the curvature array in a frame field

`Work.Diff.GE.covRxnA.mvfderiv_F_rmFrameField` computes the derivative of the `(i,j,k,l)` component
of `y ↦ F (rmFrameField g W y)`.

The proof has two parts.

* The differentiability of the array-valued map `y ↦ rmFrameField g W y`: each component
  `y ↦ rmP g y (W y i) (W y j) (W y k) (W y l)` is `C^∞` by `Work.Diff.GE.rmP_fields_smooth`
  (`Submission/Work/Diff/GE/dRmPhi.lean`, which unlike `Work.Diff.GE.contMDiff_rmP_fields` does not
  need `[I.Boundaryless]`), and the four-fold packaging into the `Curv4 n = Fin n → … → ℝ`-valued
  map is Mathlib's `contMDiffAt_pi_space` (`Work.Diff.GE.covRxnA.contMDiffAt_rmFrameField` in
  `Submission/Work/Diff/GE/covRxn/mvfderiv_rmFrameField.lean` proves the same statement).
* The chain rule for the component, which is the `private` helper `mvfderiv_comp_curv4` below: the
  chain rule `mvfderiv_comp_apply` applied to `R = fun y ↦ rmFrameField g W y` and to the component
  function `fun X ↦ (F X) i j k l`, followed by `mvfderiv_eq_fderiv` (for the self model with
  corners `𝓘(ℝ, Curv4 n)` the `fromTangentSpace` identifications are definitional) and by the
  pointwise form `fderiv_comp_curv4_apply` of `fderiv ℝ (fun X ↦ (F X) i j k l) = proj4 ∘ fderiv ℝ F`.
  Note `mvfderiv I R x v` is kept as it is.
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

/-! ## Helpers for the chain rule -/

/-- Evaluation of a curvature array at a multi-index, as a continuous linear map. -/
private noncomputable def proj4 {n : ℕ} (i j k l : Fin n) : Curv4 n →L[ℝ] ℝ where
  toFun X := X i j k l
  map_add' a b := rfl
  map_smul' c a := rfl

private lemma proj4_apply {n : ℕ} (i j k l : Fin n) (X : Curv4 n) :
    proj4 i j k l X = X i j k l := rfl

/-- The derivative of the `(i,j,k,l)` component of a map is the `(i,j,k,l)` component of its
derivative, as continuous linear maps. -/
private lemma fderiv_comp_curv4 {n : ℕ} (F : Curv4 n → Curv4 n) {z : Curv4 n}
    (hF : DifferentiableAt ℝ F z) (i j k l : Fin n) :
    fderiv ℝ (fun X : Curv4 n => (F X) i j k l) z = (proj4 i j k l).comp (fderiv ℝ F z) := by
  have h : HasFDerivAt (fun X : Curv4 n => proj4 i j k l (F X))
      ((proj4 i j k l).comp (fderiv ℝ F z)) z :=
    (proj4 i j k l).hasFDerivAt.comp z hF.hasFDerivAt
  have h2 := h.fderiv
  simpa only [proj4_apply] using h2

/-- Evaluated form of `fderiv_comp_curv4`. -/
private lemma fderiv_comp_curv4_apply {n : ℕ} (F : Curv4 n → Curv4 n) {z : Curv4 n}
    (hF : DifferentiableAt ℝ F z) (i j k l : Fin n) (w : Curv4 n) :
    fderiv ℝ (fun X : Curv4 n => (F X) i j k l) z w = (fderiv ℝ F z w) i j k l := by
  rw [fderiv_comp_curv4 F hF i j k l, ContinuousLinearMap.comp_apply, proj4_apply]

/-- Each component of `F` is differentiable where `F` is. -/
private lemma differentiableAt_comp_curv4 {n : ℕ} (F : Curv4 n → Curv4 n) {z : Curv4 n}
    (hF : DifferentiableAt ℝ F z) (i j k l : Fin n) :
    DifferentiableAt ℝ (fun X : Curv4 n => (F X) i j k l) z := by
  have h1 : DifferentiableAt ℝ (fun X : Curv4 n => proj4 i j k l (F X)) z :=
    (proj4 i j k l).differentiableAt.comp z hF
  simpa only [proj4_apply] using h1

/-- **Chain rule for the components of `F ∘ R`.**  For a smooth `F : Curv4 n → Curv4 n` and a map
`R : M → Curv4 n` differentiable at `x`, the derivative of the `(i,j,k,l)` component of `y ↦ F (R y)`
is the `(i,j,k,l)` component of `fderiv ℝ F` at `R x`, applied to the derivative of `R`. -/
private theorem mvfderiv_comp_curv4
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

/-- **Chain rule for the component of `F` applied to the curvature array in a frame field.**
For smooth `F : Curv4 n → Curv4 n` (`ContDiff ℝ (⊤ : ℕ∞) F`, i.e. `C^∞`) and smooth fields `W i`,
the derivative of the `(i,j,k,l)` component of `y ↦ F (rmFrameField g W y)` is the corresponding
component of `fderiv ℝ F` at the array, applied to the derivative of the array.

Proof route: the function is `(phi ↦ phi i j k l) ∘ F ∘ R` with `R y = rmFrameField g W y`; use
`mvfderiv_comp_apply` (resp. the chain rule `mvfderiv_comp`) twice, `mvfderiv_eq_fderiv` and
`mfderiv_eq_fderiv`, and evaluate the evaluation map's derivative with
`ContinuousLinearMap.proj_apply`.  Its `MDiffAt` should be obtained from
`(show DifferentiableAt ℝ (fun phi : Curv4 (Module.finrank ℝ E) => phi i j k l) (R x) from by
fun_prop).mdifferentiableAt` — do NOT call `ContinuousLinearMap.mdifferentiableAt` directly on
`ContinuousLinearMap.proj` (the `ℝ` semiring instances do not unify).  The smoothness of `R` as a map
into the normed space `Curv4 n` (whence its `MDifferentiableAt`) follows from
`Work.Diff.GE.rmP_fields_smooth` (`Submission/Work/Diff/GE/dRmPhi.lean`) applied to each component,
packaged with `ContMDiff.pi`/`contMDiff_pi`.  Note `mvfderiv I R x v` must be kept as it is (do not
try to identify it here). -/
theorem mvfderiv_F_rmFrameField
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    (hLC : Submission.Diff.LCSmooth I M)
    (F : Submission.Diff.Alg.Curv4 (Module.finrank ℝ E) →
      Submission.Diff.Alg.Curv4 (Module.finrank ℝ E))
    (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (g : Submission.Diff.SMet I M)
    (W : Π y : M, Fin (Module.finrank ℝ E) → TangentSpace I y)
    (hW : ∀ i, Work.Diff.GE.Rxn.SmoothField (fun y : M => W y i))
    (x : M) (v : TangentSpace I x) (i j k l : Fin (Module.finrank ℝ E)) :
    mvfderiv I (fun y : M => (F (Work.Diff.GE.Rxn.rmFrameField g W y)) i j k l) x v
      = (fderiv ℝ F (Work.Diff.GE.Rxn.rmFrameField g W x)
          (mvfderiv I (fun y : M => Work.Diff.GE.Rxn.rmFrameField g W y) x v)) i j k l := by
  -- the frame-field curvature array is a smooth `Curv4`-valued map, hence differentiable
  have hR : MDifferentiableAt I 𝓘(ℝ, Curv4 (Module.finrank ℝ E))
      (fun y : M => Work.Diff.GE.Rxn.rmFrameField g W y) x := by
    have hsm : ContMDiffAt I 𝓘(ℝ, Curv4 (Module.finrank ℝ E)) ∞
        (fun y : M => Work.Diff.GE.Rxn.rmFrameField g W y) x := by
      rw [contMDiffAt_pi_space]
      intro i
      rw [contMDiffAt_pi_space]
      intro j
      rw [contMDiffAt_pi_space]
      intro k
      rw [contMDiffAt_pi_space]
      intro l
      exact (Work.Diff.GE.rmP_fields_smooth hLC g (hW i) (hW j) (hW k) (hW l)).contMDiffAt
    exact hsm.mdifferentiableAt (by simp)
  exact mvfderiv_comp_curv4 F hF x v hR i j k l

end Work.Diff.GE.covRxnA
