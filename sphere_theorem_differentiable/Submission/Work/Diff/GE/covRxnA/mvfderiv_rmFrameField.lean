import Mathlib
import Submission.Work.Diff.GE.covRxn.Defs
import Submission.Work.Diff.GE.kato_covRm_field

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The derivative of the curvature array in a frame field

For smooth fields `W i` the array-valued function
`y ↦ rmFrameField g W y = (fun i j k l => rmP g y (W y i) (W y j) (W y k) (W y l))`
has derivative the array of `∇Rm` on the values at `x` plus the four frame-rotation corrections.

The proof has three ingredients:

* `mvfderiv_pi_apply'` : the `i`-th component of the derivative of an array-valued function is the
  derivative of the `i`-th component (needs the function to be differentiable), proved with
  `MDifferentiableAt.mvfderiv` on both sides and `fderivWithin_apply` (Mathlib);
* `mvfderiv_curv4_apply` : its four-fold iterate for `Curv4`-valued functions;
* `mvfderiv_rmP_fields` : the scalar identity for one component, which is exactly the Leibniz form of
  `covRm` for arbitrary smooth fields `Work.Diff.GE.kato_covRm_field`.

The smoothness of `y ↦ rmFrameField g W y` (needed to make the component identity apply) is
`contMDiffAt_rmFrameField`, from `rmP_fields_smooth` (the smoothness of `y ↦ rmP g y (A y) …` for
smooth `A … D`; note this does not need `[I.Boundaryless]`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE.covRxnA

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M]

/-- The `i`-th component of the derivative of an array-valued function is the derivative of the
`i`-th component, for a function that is differentiable at `x`.

(Without the differentiability hypothesis this is false: `mfderiv` is `0` at points where the
function is not differentiable.)  Both sides are rewritten with `MDifferentiableAt.mvfderiv` into
`fderivWithin ℝ` of the chart representation; the chart representation of the `i`-th component is
the `i`-th component of the chart representation (the target chart is the identity:
`ext_chart_model_space_apply`), and `fderivWithin_apply` computes the `i`-th component of the
derivative of a `Π`-valued function. -/
theorem mvfderiv_pi_apply'
    {ι : Type*} [Fintype ι] {Fi : ι → Type*} [∀ i, NormedAddCommGroup (Fi i)]
    [∀ i, NormedSpace ℝ (Fi i)]
    (θ : M → Π i, Fi i) (x : M) (v : TangentSpace I x) (i : ι)
    (hθ : MDifferentiableAt I (modelWithCornersSelf ℝ (Π i, Fi i)) θ x) :
    mvfderiv I (fun y : M => θ y i) x v = mvfderiv I θ x v i := by
  have hproj : MDifferentiableAt 𝓘(ℝ, Π i, Fi i) 𝓘(ℝ, Fi i)
      (fun w : Π i, Fi i => w i) (θ x) :=
    (differentiableAt_apply (𝕜 := ℝ) i (θ x)).mdifferentiableAt
  have hL : MDifferentiableAt I 𝓘(ℝ, Fi i) (fun y : M => θ y i) x := hproj.comp x hθ
  have h1 := hθ.mvfderiv
  have h2 := hL.mvfderiv
  have hΦ : DifferentiableWithinAt ℝ
      (writtenInExtChartAt I 𝓘(ℝ, Π i, Fi i) x θ) (Set.range I) ((extChartAt I x) x) := by
    have h := hθ.mdifferentiableWithinAt.differentiableWithinAt_writtenInExtChartAt
      (I' := 𝓘(ℝ, Π i, Fi i)) (s := Set.univ)
    simpa only [Set.preimage_univ, Set.univ_inter] using h
  have hs : UniqueDiffWithinAt ℝ (Set.range I) ((extChartAt I x) x) := by
    have h := UniqueMDiffOn.uniqueDiffWithinAt_range_inter (I := I) (s := Set.univ)
      (uniqueMDiffOn_univ) x ((extChartAt I x) x)
      ⟨(extChartAt I x).map_source (mem_extChartAt_source x), trivial⟩
    simpa only [Set.preimage_univ, Set.inter_univ] using h
  rw [h2, h1]
  have hΨ : writtenInExtChartAt I 𝓘(ℝ, Fi i) x (fun y : M => θ y i)
      = fun z => writtenInExtChartAt I 𝓘(ℝ, Π i, Fi i) x θ z i := by
    funext z
    simp only [writtenInExtChartAt, Function.comp_apply, ext_chart_model_space_apply]
  rw [hΨ, fderivWithin_apply hΦ hs i]
  rfl

/-- The four components of the derivative of a `Curv4`-valued function are the derivatives of the
four components. -/
theorem mvfderiv_curv4_apply {n : ℕ} (f : M → Curv4 n) (x : M) (v : TangentSpace I x)
    (hm : MDifferentiableAt I 𝓘(ℝ, Curv4 n) f x) :
    mvfderiv I f x v = fun i j k l => mvfderiv I (fun y : M => f y i j k l) x v := by
  funext i j k l
  have hd1 : MDifferentiableAt I 𝓘(ℝ, Fin n → Fin n → Fin n → ℝ) (fun y : M => f y i) x :=
    ((differentiableAt_apply (𝕜 := ℝ) i (f x)).mdifferentiableAt).comp x hm
  have hd2 : MDifferentiableAt I 𝓘(ℝ, Fin n → Fin n → ℝ) (fun y : M => f y i j) x :=
    ((differentiableAt_apply (𝕜 := ℝ) j (f x i)).mdifferentiableAt).comp x hd1
  have hd3 : MDifferentiableAt I 𝓘(ℝ, Fin n → ℝ) (fun y : M => f y i j k) x :=
    ((differentiableAt_apply (𝕜 := ℝ) k (f x i j)).mdifferentiableAt).comp x hd2
  rw [← mvfderiv_pi_apply' (θ := f) x v i hm]
  rw [← mvfderiv_pi_apply' (θ := fun y : M => f y i) x v j hd1]
  rw [← mvfderiv_pi_apply' (θ := fun y : M => (fun y : M => f y i) y j) x v k hd2]
  rw [← mvfderiv_pi_apply' (θ := fun y : M => (fun y : M => (fun y : M => f y i) y j) y k)
    x v l hd3]

/-- `y ↦ rmP g y (A y) (B y) (C y) (D y)` is `C^∞` for smooth fields `A B C D` and a smooth metric
`g`.  This differs from `Work.Diff.GE.contMDiff_rmP_fields` only in that it does not carry the
(here unnecessary) hypothesis `[I.Boundaryless]`. -/
theorem rmP_fields_smooth
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    {A B C D : Π y : M, TangentSpace I y}
    (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C))
    (hD : CMDiff ∞ (T% D)) :
    CMDiff ∞ (fun y : M => rmP g y (A y) (B y) (C y) (D y)) := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  have hcov : ContMDiffCovariantDerivative (lcOf g) ∞ := (hLC g).1.some
  have hcurv : CMDiff ∞ (T% (fun y : M => curv (lcOf g) A B D y)) :=
    Work.Diff.GE.contMDiff_curv_fields (lcOf g) hcov hA hB hD
  have hfun : (fun y : M => rmP g y (A y) (B y) (C y) (D y))
      = fun y : M => inner ℝ (curv (lcOf g) A B D y) (C y) := by
    funext y
    show (g.inner y (rmVec (lcOf g) y (A y) (B y) (D y))) (C y) = _
    rw [Work.Diff.GE.rmVec_eq_curvVec (lcOf g) hcov y (A y) (B y) (D y),
      Submission.CurvatureVec.curvVec_eq (lcOf g) hcov hA hB hD rfl rfl rfl]
    rfl
  rw [hfun]
  exact ContMDiff.inner_bundle (IB := I) (b := id) (v := fun y : M => curv (lcOf g) A B D y)
    (w := C) hcurv hC

/-- The frame-field curvature array is `C^∞` at `x` when the fields `W i` are smooth. -/
theorem contMDiffAt_rmFrameField
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (W : Π y : M, Fin (Module.finrank ℝ E) → TangentSpace I y)
    (hW : ∀ i, Work.Diff.GE.Rxn.SmoothField (fun y : M => W y i)) (x : M) :
    ContMDiffAt I 𝓘(ℝ, Curv4 (Module.finrank ℝ E)) ∞
      (fun y : M => Work.Diff.GE.Rxn.rmFrameField g W y) x := by
  rw [contMDiffAt_pi_space]
  intro i
  rw [contMDiffAt_pi_space]
  intro j
  rw [contMDiffAt_pi_space]
  intro k
  rw [contMDiffAt_pi_space]
  intro l
  exact rmP_fields_smooth hLC g (hW i) (hW j) (hW k) (hW l) x

/-- The scalar identity for one component: for smooth fields `W i`, the derivative of
`y ↦ rmP g y (W y i) (W y j) (W y k) (W y l)` along `v` is `∇Rm` on the values at `x` plus the four
frame-rotation corrections.  This is `Work.Diff.GE.kato_covRm_field` with the direction field
`smoothExt x v`. -/
theorem mvfderiv_rmP_fields
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (W : Π y : M, Fin (Module.finrank ℝ E) → TangentSpace I y)
    (hW : ∀ i, Work.Diff.GE.Rxn.SmoothField (fun y : M => W y i))
    (x : M) (v : TangentSpace I x) (i j k l : Fin (Module.finrank ℝ E)) :
    mvfderiv I (fun y : M => rmP g y (W y i) (W y j) (W y k) (W y l)) x v
      = covRm g x v (W x i) (W x j) (W x k) (W x l)
          + rmP g x (lcOf g (fun y : M => W y i) x v) (W x j) (W x k) (W x l)
          + rmP g x (W x i) (lcOf g (fun y : M => W y j) x v) (W x k) (W x l)
          + rmP g x (W x i) (W x j) (lcOf g (fun y : M => W y k) x v) (W x l)
          + rmP g x (W x i) (W x j) (W x k) (lcOf g (fun y : M => W y l) x v) := by
  have h := (Work.Diff.GE.kato_covRm_field (I := I) (M := M) hLC g x (smoothExt x v)
    (fun y : M => W y i) (fun y : M => W y j) (fun y : M => W y k) (fun y : M => W y l)
    (Work.Diff.GE.smoothExt_cmdiff x v) (hW i) (hW j) (hW k) (hW l)).1
  simp only [Work.Diff.GE.smoothExt_apply] at h
  linarith

/-- **The derivative of the curvature array in a frame field.**  For smooth fields `W i` the
array-valued function `y ↦ rmFrameField g W y = (fun i j k l => rmP g y (W y i) (W y j) (W y k) (W y l))`
has derivative the array of `∇Rm` on the values at `x` plus the four frame-rotation corrections.

Proof route: `funext` in `i j k l`; each component is
`(mvfderiv I (fun y => rmFrameField g W y) x v) i j k l`, which is
`mvfderiv I (fun y => rmP g y (W y i) (W y j) (W y k) (W y l)) x v` by the component identity — see
`Work.Diff.GE.covRxnA.mvfderiv_pi_apply` in the sibling module
`Submission.Work.Diff.GE.covRxnA.mvfderiv_pi_apply` IF it is already proved (then import it and cite
it), otherwise establish that component identity yourself (e.g. via `MDifferentiableAt.mvfderiv` +
`fderivWithin_apply`, or via `mvfderiv_comp_apply` with the evaluation `phi ↦ phi i j k l`, whose
`MDiffAt` follows from `(show DifferentiableAt ℝ (fun phi : Curv4 n => phi i j k l) phi from by
fun_prop).mdifferentiableAt`).  The scalar identity for each component is
`Work.Diff.GE.Rxn.mvfderiv_rmP_fields` (in the imported module). -/
theorem mvfderiv_rmFrameField
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (W : Π y : M, Fin (Module.finrank ℝ E) → TangentSpace I y)
    (hW : ∀ i, Work.Diff.GE.Rxn.SmoothField (fun y : M => W y i))
    (x : M) (v : TangentSpace I x) :
    mvfderiv I (fun y : M => Work.Diff.GE.Rxn.rmFrameField g W y) x v
      = fun i j k l =>
          Submission.Diff.covRm g x v (W x i) (W x j) (W x k) (W x l)
          + Submission.Diff.rmP g x (Submission.Diff.lcOf g (fun y : M => W y i) x v)
              (W x j) (W x k) (W x l)
          + Submission.Diff.rmP g x (W x i)
              (Submission.Diff.lcOf g (fun y : M => W y j) x v) (W x k) (W x l)
          + Submission.Diff.rmP g x (W x i) (W x j)
              (Submission.Diff.lcOf g (fun y : M => W y k) x v) (W x l)
          + Submission.Diff.rmP g x (W x i) (W x j) (W x k)
              (Submission.Diff.lcOf g (fun y : M => W y l) x v) := by
  have hm : MDifferentiableAt I 𝓘(ℝ, Curv4 (Module.finrank ℝ E))
      (fun y : M => Work.Diff.GE.Rxn.rmFrameField g W y) x :=
    (contMDiffAt_rmFrameField hLC g W hW x).mdifferentiableAt (by simp)
  rw [mvfderiv_curv4_apply (f := fun y : M => Work.Diff.GE.Rxn.rmFrameField g W y) x v hm]
  funext i j k l
  simp only [Work.Diff.GE.Rxn.rmFrameField]
  exact mvfderiv_rmP_fields hLC g W hW x v i j k l

end Work.Diff.GE.covRxnA
