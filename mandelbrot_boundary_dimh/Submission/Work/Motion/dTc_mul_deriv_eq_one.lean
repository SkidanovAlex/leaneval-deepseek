import Mathlib
import Submission.Work.Motion.pertSetup

namespace Work.Motion

open LeanEval.Dynamics.MandelbrotBoundary
open Filter

theorem dTc_mul_deriv_eq_one (m : ℕ) (c : ℂ) {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z)
    (hfix : Filter.Eventually (fun y => Work.Motion.Pert.TcIter m (c, f y) = y) (nhds z)) :
    Work.Motion.Pert.dTc m (c, f z) * deriv f z = 1 := by
  set F : ℂ → ℂ := (Tc c)^[m] with hFdef
  have hdiffF : DifferentiableAt ℂ F (f z) := by
    rw [hFdef]
    exact ((Pert.differentiable_Tc c).iterate m).differentiableAt
  have hFderiv : deriv F (f z) = Pert.dTc m (c, f z) := by
    rw [hFdef]
    exact Pert.deriv_TcIter m c (f z)
  have h1 : (fun y => Pert.TcIter m (c, f y)) =ᶠ[nhds z] (F ∘ f) := by
    filter_upwards with y
    rw [hFdef]
    simp only [Function.comp_apply]
    exact Pert.TcIter_eq m c (f y)
  have hfix' : (fun y => Pert.TcIter m (c, f y)) =ᶠ[nhds z] id := hfix
  have heq : F ∘ f =ᶠ[nhds z] id := h1.symm.trans hfix'
  have hderiv1 : deriv (F ∘ f) z = 1 := by
    rw [heq.deriv_eq, deriv_id]
  have hchain : deriv (F ∘ f) z = deriv F (f z) * deriv f z :=
    deriv_comp z hdiffF hf
  rw [hchain, hFderiv] at hderiv1
  exact hderiv1

end Work.Motion
