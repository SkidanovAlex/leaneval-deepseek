import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.L62.cylinder_model
import Submission.Work.L62.ratio_bound_family
import Submission.Work.L62.l62c_end
import Submission.Work.Horn.piExp_hasDerivAt

/-!
# L62 — the lift/cylinder derivative identity (NOTES_L62f, formula (F5))

For `f, F : ℂ → ℂ` with `π (f u) = F (π u)` (`π = piExp`), the chain rule for `π` gives

  `deriv f w = deriv F (π w) * π w / π (f w)`,

so `‖deriv (ĥ^[j]) w‖` is the Koenigs ratio `‖deriv ((H β)^[j]) (π w) * π w / ((H β)^[j]) (π w)‖`
of `Work.L62.ratio_bound_family`.  This is what turns the contract's `deriv_bd` on the *head* into
the uniform ratio bound.
-/

namespace Work.L62

open MandelDim Set Filter Topology
open scoped Topology

noncomputable section

/-- `π = piExp` has derivative `2πi π` (restated here from `Work.Horn.piExp_hasDerivAt`). -/
theorem deriv_piExp_l62 (w : ℂ) :
    deriv piExp w = (2 * (Real.pi : ℂ) * Complex.I) * piExp w :=
  (Work.Horn.piExp_hasDerivAt w).deriv

/-- **The lift/cylinder derivative identity** (NOTES_L62f (F5)).  If `π ∘ f = F ∘ π` and both
`f` (at `w`) and `F` (at `π w`) are complex differentiable, then
`deriv f w = deriv F (π w) * π w / π (f w)`. -/
theorem deriv_lift_eq {f F : ℂ → ℂ} {w : ℂ} (hf : DifferentiableAt ℂ f w)
    (hF : DifferentiableAt ℂ F (piExp w)) (h : ∀ u : ℂ, piExp (f u) = F (piExp u)) :
    deriv f w = deriv F (piExp w) * piExp w / piExp (f w) := by
  have hpi : HasDerivAt piExp ((2 * (Real.pi : ℂ) * Complex.I) * piExp w) w :=
    Work.Horn.piExp_hasDerivAt w
  have hpi' : HasDerivAt piExp ((2 * (Real.pi : ℂ) * Complex.I) * piExp (f w)) (f w) :=
    Work.Horn.piExp_hasDerivAt (f w)
  have h1 : HasDerivAt (fun u : ℂ => piExp (f u))
      (((2 * (Real.pi : ℂ) * Complex.I) * piExp (f w)) * deriv f w) w :=
    hpi'.comp w hf.hasDerivAt
  have h2 : HasDerivAt (fun u : ℂ => F (piExp u))
      (deriv F (piExp w) * ((2 * (Real.pi : ℂ) * Complex.I) * piExp w)) w :=
    hF.hasDerivAt.comp w hpi
  have hfun : (fun u : ℂ => piExp (f u)) = fun u : ℂ => F (piExp u) := funext h
  rw [hfun] at h1
  have heq : ((2 * (Real.pi : ℂ) * Complex.I) * piExp (f w)) * deriv f w
      = deriv F (piExp w) * ((2 * (Real.pi : ℂ) * Complex.I) * piExp w) :=
    h1.unique h2
  have hne : (2 * (Real.pi : ℂ) * Complex.I) * piExp (f w) ≠ 0 :=
    mul_ne_zero Complex.two_pi_I_ne_zero (Work.Horn.MandelDim.piExp_ne_zero (f w))
  have h3 : deriv f w
      = (deriv F (piExp w) * ((2 * (Real.pi : ℂ) * Complex.I) * piExp w))
        / ((2 * (Real.pi : ℂ) * Complex.I) * piExp (f w)) := by
    rw [eq_div_iff hne]
    rw [← heq]
    ring
  rw [h3]
  rw [show deriv F (piExp w) * ((2 * (Real.pi : ℂ) * Complex.I) * piExp w)
      = (2 * (Real.pi : ℂ) * Complex.I) * (deriv F (piExp w) * piExp w) by ring]
  rw [mul_div_mul_left _ _ Complex.two_pi_I_ne_zero]

/-- The norm form: `‖deriv f w‖` is the Koenigs ratio at `π w`. -/
theorem norm_deriv_lift_eq {f F : ℂ → ℂ} {w : ℂ} (hf : DifferentiableAt ℂ f w)
    (hF : DifferentiableAt ℂ F (piExp w)) (h : ∀ u : ℂ, piExp (f u) = F (piExp u)) :
    ‖deriv f w‖ = ‖deriv F (piExp w) * piExp w / F (piExp w)‖ := by
  rw [deriv_lift_eq hf hF h, h w]

end

end Work.L62
