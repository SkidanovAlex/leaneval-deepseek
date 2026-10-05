import Mathlib
import Submission.Work.RPB.Defs
import Submission.Work.RPB.B5.contDiff_signedArea
import Submission.Work.RPB.B5.contDiff_sliceDeriv_gen
import Submission.Work.RPB.B4.contDiff_parametric_integral

/-!
# B5: smoothness of the signed area in a general family parameter

`Work.RPB.B5.contDiff_signedArea` proves that for a two-parameter family of closed plane curves
`(σ, t) ↦ V σ t` with `V` jointly `C^{k+1}`, the signed area
`σ ↦ signedArea (V σ) = (1/2) ∫_0^{2π} ω_ℂ (V σ t, ∂_t V σ t) dt`
is `C^k` in `σ`.  That statement is restricted to the parameter space `X = ℝ`, because its proof
goes through `Work.RPA3.deriv_prodMk_right`, the identity
`deriv (fun s => f (a,s)) b = fderiv ℝ f (a,b) (0,1)`, which is stated for `f : ℝ × ℝ → E`.

This file removes that restriction: for an arbitrary real normed space `X` the same conclusion
holds,

`contDiff_signedArea_gen : ContDiff ℝ (k+1) (fun z : X × ℝ => V z.1 z.2) →
    ContDiff ℝ k (fun x : X => signedArea (fun t => V x t))`,

which is the statement needed when the family parameter `x` lives in a general normed space (e.g. a
space of curves).  The proof is the same three-step composition as in the `ℝ` case.

* The `t`-slice derivative `∂_t V x t` is the evaluation of the Fréchet derivative of the joint map
  `z ↦ V z.1 z.2` at `(0,1)`, hence `C^k` in `(x,t)`: this is
  `Work.RPB.B5.contDiff_sliceDeriv_gen`, the general-`X` form of
  `Work.RPB.B5.contDiff_sliceDeriv`.
* `ω_ℂ` is smooth on jointly `C^k` families (`Work.RPB.B5.contDiff_omegaC`).
* A parametric interval integral of a jointly `C^k` family is `C^k`
  (`Work.RPB.B4.contDiff_parametric_integral`, which bridges the universe gap between the
  parameter space and the codomain).

No periodicity hypothesis is needed: `deriv` is taken inside the integrand, so no boundary term
arises.
-/

open MeasureTheory intervalIntegral
open scoped Interval

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

/-- Smoothness of the signed area in the family parameter, for an arbitrary real normed space `X`
of parameters: if `(x, t) ↦ V x t` is jointly `C^{k+1}`, then `x ↦ signedArea (V x)` is `C^k`. -/
theorem contDiff_signedArea_gen {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (V : X → ℝ → ℂ) (k : ℕ)
    (hV : ContDiff ℝ (k + 1) (fun z : X × ℝ => V z.1 z.2)) :
    ContDiff ℝ k (fun x : X => Work.RPB.signedArea (fun t => V x t)) := by
  have hWk : ContDiff ℝ k (fun z : X × ℝ => V z.1 z.2) := hV.of_le (by norm_num)
  have hderivCont : ContDiff ℝ k (fun z : X × ℝ => deriv (fun s => V z.1 s) z.2) :=
    contDiff_sliceDeriv_gen V hV
  have hg : ContDiff ℝ k
      (fun z : X × ℝ => Work.RPV.ωC (V z.1 z.2) (deriv (fun s => V z.1 s) z.2)) :=
    contDiff_omegaC hWk hderivCont
  -- Swap the argument order so that the integration variable comes first.
  have hg' : ContDiff ℝ k
      (fun z : ℝ × X => Work.RPV.ωC (V z.2 z.1) (deriv (fun s => V z.2 s) z.1)) := by
    have hφ : ContDiff ℝ k (fun z : ℝ × X => (z.2, z.1)) := by fun_prop
    simpa [Function.comp_def] using hg.comp hφ
  have hint : ContDiff ℝ k
      (fun x : X => ∫ t in (0 : ℝ)..(2 * Real.pi),
        Work.RPV.ωC (V x t) (deriv (fun s => V x s) t)) :=
    Work.RPB.B4.contDiff_parametric_integral
      (fun t x => Work.RPV.ωC (V x t) (deriv (fun s => V x s) t)) 0 (2 * Real.pi) k hg'
  have h2 : ContDiff ℝ k
      (fun x : X => (1 / 2 : ℝ) * ∫ t in (0 : ℝ)..(2 * Real.pi),
        Work.RPV.ωC (V x t) (deriv (fun s => V x s) t)) :=
    ContDiff.const_smul (1 / 2 : ℝ) hint
  simpa only [Work.RPB.signedArea] using h2

end Work.RPB.B5
