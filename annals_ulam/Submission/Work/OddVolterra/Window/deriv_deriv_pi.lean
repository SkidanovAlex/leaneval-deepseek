import Mathlib

namespace Work.OddVolterra.Window

/-- (`Work.OddVolterra.Window`, module `Submission.Work.OddVolterra.Window.deriv_deriv_pi`.)
The second derivative of a `C²` curve `Φ : ℝ → (ι → ℝ)` into a finite product of `ℝ`s is the
product of the second derivatives of its components.  A short proof: `ContDiffAt ℝ 2 Φ a` gives
via `ContDiffAt.eventually` and `contDiffAt_pi` that each component is differentiable near `a`,
so `deriv Φ =ᶠ[𝓝 a] fun u => fun i => deriv (fun v => Φ v i) u` by `deriv_pi`; rewriting the outer
derivative with `Filter.EventuallyEq.deriv_eq` and applying `deriv_pi` once more (each
`u ↦ deriv (fun v => Φ v i) u` is differentiable at `a` by `ContDiffAt.derivWithin` and
`ContDiffAt.differentiableAt`) gives the claim. -/
theorem deriv_deriv_pi {ι : Type*} [Fintype ι] {Φ : ℝ → (ι → ℝ)} {a : ℝ}
    (h : ContDiffAt ℝ 2 Φ a) :
    deriv (deriv Φ) a = fun i => deriv (deriv (fun u : ℝ => Φ u i)) a := by
  have hcomp : ∀ i, ContDiffAt ℝ 2 (fun u : ℝ => Φ u i) a := fun i => (contDiffAt_pi.mp h) i
  have hev : deriv Φ =ᶠ[nhds a] fun u => fun i => deriv (fun v => Φ v i) u := by
    filter_upwards [h.eventually (by norm_num)] with u hu
    exact deriv_pi fun i => (contDiffAt_pi.mp hu i).differentiableAt (by norm_num)
  have h2 : deriv (fun u => fun i => deriv (fun v => Φ v i) u) a
      = fun i => deriv (deriv (fun u : ℝ => Φ u i)) a :=
    deriv_pi fun i => ((hcomp i).derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [hev.deriv_eq, h2]

end Work.OddVolterra.Window
