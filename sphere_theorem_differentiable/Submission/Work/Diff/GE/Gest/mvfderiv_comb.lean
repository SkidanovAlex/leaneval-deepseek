import Mathlib
import Submission.Work.Diff.GE.Gest.Base

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE.Gest

open scoped Manifold ContDiff Bundle Topology in
open Submission.Diff Submission.Diff.Alg Bundle ContDiff Set VectorField CovariantDerivative Metric in
theorem mvfderiv_comb
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    (a b c : ℝ) {f g h : M → ℝ} (hf : CMDiff ∞ f) (hg : CMDiff ∞ g) (hh : CMDiff ∞ h)
    (x : M) (v : TangentSpace I x) :
    mvfderiv I (fun y => a * f y + b * g y + c * h y) x v
      = a * mvfderiv I f x v + b * mvfderiv I g x v + c * mvfderiv I h x v := by
  have hf' : MDiffAt f x := hf.contMDiffAt.mdifferentiableAt (by simp)
  have hg' : MDiffAt g x := hg.contMDiffAt.mdifferentiableAt (by simp)
  have hh' : MDiffAt h x := hh.contMDiffAt.mdifferentiableAt (by simp)
  have hconst : ∀ r : ℝ, MDiffAt (fun _ : M => r) x := fun r => mdifferentiableAt_const
  have H : (fun y => a * f y + b * g y + c * h y)
      = (fun _ : M => a) • f + ((fun _ : M => b) • g + (fun _ : M => c) • h) := by
    ext y; simp only [Pi.add_apply, Pi.mul_apply, smul_eq_mul]; ring
  rw [H]
  rw [mvfderiv_add ((hconst a).smul hf') (((hconst b).smul hg').add ((hconst c).smul hh')),
      mvfderiv_add ((hconst b).smul hg') ((hconst c).smul hh'),
      mvfderiv_smul (hconst a) hf', mvfderiv_smul (hconst b) hg', mvfderiv_smul (hconst c) hh']
  simp [mvfderiv_const, smul_eq_mul]
  ring

end Work.Diff.GE.Gest
