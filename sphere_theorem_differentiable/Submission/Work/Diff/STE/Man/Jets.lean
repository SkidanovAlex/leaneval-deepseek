/-
# The manifold layer: Clairaut's theorem and the jets of a real solution

The C1 bridge needs two elementary facts about the flat jets `Work.Diff.STE.Flat.jetM` of a solution:

* the second jet is **symmetric in the two derivative slots** (`pdM c (pdM d u) = pdM d (pdM c u)`,
  Clairaut/Schwarz) — this is the hypothesis `hB1` of `Work.Diff.STE.Man.chartNonlin_eq_pPhi`;
* for a **real-valued** solution, the flat jets commute with taking real parts — this is what makes
  the `reMatE` of the jets of `u` the jets of the real matrix `reMatE ∘ u`, which is the chart
  matrix of the local metric.
-/
import Mathlib
import Submission.Work.Diff.STE.Man.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE.Man

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

noncomputable section

open Work.Diff.STE.Flat Work.Diff.STE.DeTurck Work.Diff.EXT Work.Diff.STE.deTurck

/-- **Clairaut's theorem for the partial derivatives `pd`**: the second partial derivatives commute
for a function that is `C²` (indeed `C^∞`) at the point. -/
theorem pd_pd_comm {ι : Type*} [Fintype ι] [DecidableEq ι] {f : (ι → ℝ) → ℂ} {x : ι → ℝ}
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f x) (c d : ι) :
    pd c (pd d f) x = pd d (pd c f) x := by
  have hda : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)
  have h1 : pd c (pd d f) x
      = (fderiv ℝ (fderiv ℝ f) x) (Pi.single c 1) (Pi.single d 1) := by
    change (fderiv ℝ (fun y : ι → ℝ => (fderiv ℝ f y) (Pi.single d 1)) x) (Pi.single c 1) = _
    rw [fderiv_clm_apply (c := fderiv ℝ f)
      (u := fun _ : ι → ℝ => Pi.single d 1) hda (differentiableAt_const _)]
    simp
  have h2 : pd d (pd c f) x
      = (fderiv ℝ (fderiv ℝ f) x) (Pi.single d 1) (Pi.single c 1) := by
    change (fderiv ℝ (fun y : ι → ℝ => (fderiv ℝ f y) (Pi.single c 1)) x) (Pi.single d 1) = _
    rw [fderiv_clm_apply (c := fderiv ℝ f)
      (u := fun _ : ι → ℝ => Pi.single c 1) hda (differentiableAt_const _)]
    simp
  rw [h1, h2]
  exact (hf.isSymmSndFDerivAt (by simp)).eq _ _

/-- **Clairaut's theorem for the second jet of a matrix-valued function.** -/
theorem pdM_pdM_comm {u : Torus (dim E)} {x : Fin (dim E) → ℝ}
    (hu : ContDiffAt ℝ (⊤ : ℕ∞) u x) (c d : Fin (dim E)) :
    pdM c (pdM d u) x = pdM d (pdM c u) x := by
  have hentry : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Fin (dim E) → ℝ => u y) x := hu
  funext i j
  have hfd : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Fin (dim E) → ℝ => u y i j) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hentry i) j
  exact pd_pd_comm hfd c d

/-- **The derivative of a locally real-valued function is real**: if `f` has no imaginary part near
`x`, then so has its `c`-th partial derivative at `x`. -/
lemma im_pd_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι] {f : (ι → ℝ) → ℂ} {x : ι → ℝ}
    (hd : DifferentiableAt ℝ f x) (h : ∀ᶠ y in 𝓝 x, (f y).im = 0) (c : ι) :
    (pd c f x).im = 0 := by
  have heq : f =ᶠ[𝓝 x] (fun y => ((f y).re : ℂ)) := by
    filter_upwards [h] with y hy
    exact Complex.ext rfl (by simpa using hy)
  change (fderiv ℝ f x (Pi.single c 1)).im = 0
  rw [heq.fderiv_eq]
  rw [show (fun y : ι → ℝ => ((f y).re : ℂ))
      = Complex.ofRealCLM ∘ (Complex.reCLM ∘ f) from rfl]
  rw [fderiv_comp x Complex.ofRealCLM.differentiableAt
    (Complex.reCLM.differentiableAt.comp x hd)]
  rw [fderiv_comp x Complex.reCLM.differentiableAt hd]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.fderiv,
    Complex.ofRealCLM_apply, Complex.reCLM_apply]
  exact Complex.ofReal_im _

end

end Work.Diff.STE.Man