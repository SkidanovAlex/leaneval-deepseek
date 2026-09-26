/-
# Holomorphy of a contour integral over `(0,∞)` by dominated convergence

The CKMRV generating function is defined by an integral over the positive imaginary axis,

  `τ ↦ ∫_0^∞ K(τ, it) e^{-πr²t} dt`,

and the first analytic fact needed about it (`h1` of
`Work.Kernels.satisfiesThm31_of_analysis`) is that it is holomorphic in `τ`.  The tool is
differentiation under the integral sign (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`
from `Mathlib`), together with Cauchy's estimate
(`Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`) which upgrades a *value* bound on a ball
to a *derivative* bound on the concentric half-ball.

Everything in this file is independent of the CKMRV kernels: it is the general analytic engine,
stated for an arbitrary family `f : ℂ → ℝ → ℂ`, so that the concrete kernel estimates of
`Work.Asymptotics.Cleared` can be fed into it.

## Main results

* `Work.Asymptotics.integrableOn_of_bound` : an a.e. bound by an integrable function, together
  with a.e. strong measurability, gives integrability.
* `Work.Asymptotics.deriv_bound_of_bound` : Cauchy's estimate in the form used here: from
  `‖f z t‖ ≤ bound t` on `ball τ₀ R` for a.e. `t` one gets
  `‖deriv (f · t) z‖ ≤ (2/R) * bound t` on `ball τ₀ (R/2)`.
* `Work.Asymptotics.hasDerivAt_integral_Ioi` : the parametric differentiation formula.
* `Work.Asymptotics.differentiableOn_integral_Ioi` : holomorphy of the contour integral on an
  open set.
-/
import Mathlib
import Submission.Work.Asymptotics.Basic

noncomputable section

open MeasureTheory Filter Topology
open scoped Topology

namespace Work.Asymptotics

/-! ## Integrability from a bound -/

/-- An a.e. bound by an integrable function, together with a.e. strong measurability, makes the
function integrable. -/
lemma integrableOn_of_bound {f : ℝ → ℂ} {bound : ℝ → ℝ} {s : Set ℝ}
    (hmeas : AEStronglyMeasurable f (volume.restrict s))
    (hbint : IntegrableOn bound s) (hb : ∀ᵐ t ∂(volume.restrict s), ‖f t‖ ≤ bound t) :
    IntegrableOn f s := by
  rw [IntegrableOn] at hbint ⊢
  exact hbint.mono' hmeas hb

/-! ## Cauchy's estimate -/

/-- **Cauchy's estimate, in the form used for the contour integral.**  If for a.e. `t` the
function `z ↦ f z t` is holomorphic on `ball τ₀ R` and bounded there by `bound t`, then its
`z`-derivative is bounded by `(2/R) * bound t` on `ball τ₀ (R/2)`. -/
lemma deriv_bound_of_bound {f : ℂ → ℝ → ℂ} {τ₀ : ℂ} {R : ℝ} (hR : 0 < R) {bound : ℝ → ℝ}
    (hdiff : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ∀ z ∈ Metric.ball τ₀ R, DifferentiableAt ℂ (fun z' => f z' t) z)
    (hbb : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ∀ z ∈ Metric.ball τ₀ R, ‖f z t‖ ≤ bound t) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ∀ z ∈ Metric.ball τ₀ (R / 2), ‖deriv (fun z' => f z' t) z‖ ≤ (2 / R) * bound t := by
  filter_upwards [hdiff, hbb] with t ht hb
  intro z hz
  have hz' : dist z τ₀ < R / 2 := by simpa [Metric.mem_ball] using hz
  have hsub : Metric.closedBall z (R / 2) ⊆ Metric.ball τ₀ R := by
    intro w hw
    rw [Metric.mem_closedBall] at hw
    rw [Metric.mem_ball]
    calc dist w τ₀ ≤ dist w z + dist z τ₀ := dist_triangle _ _ _
      _ < R / 2 + R / 2 := by linarith
      _ = R := by ring
  have hdiffOn : DiffContOnCl ℂ (fun w => f w t) (Metric.ball z (R / 2)) := by
    refine DifferentiableOn.diffContOnCl fun w hw => ?_
    have hcl : closure (Metric.ball z (R / 2)) ⊆ Metric.closedBall z (R / 2) :=
      closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall
    have hw' : dist w z ≤ R / 2 := Metric.mem_closedBall.mp (hcl hw)
    have hmem : w ∈ Metric.ball τ₀ R := by
      rw [Metric.mem_ball]
      calc dist w τ₀ ≤ dist w z + dist z τ₀ := dist_triangle _ _ _
        _ < R / 2 + R / 2 := by linarith
        _ = R := by ring
    exact (ht w hmem).differentiableWithinAt
  have hsphere : ∀ w ∈ Metric.sphere z (R / 2), ‖f w t‖ ≤ bound t := by
    intro w hw
    exact hb w (hsub (Metric.mem_closedBall.mpr (le_of_eq (Metric.mem_sphere.mp hw))))
  have hkey := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (f := fun w => f w t)
    (c := z) (R := R / 2) (C := bound t) (by linarith) hdiffOn hsphere
  calc ‖deriv (fun z' => f z' t) z‖ ≤ bound t / (R / 2) := hkey
    _ = (2 / R) * bound t := by field_simp

/-! ## Differentiation under the integral sign -/

/-- **The parametric differentiation formula** for an integral over `(0,∞)`: if the family
`τ ↦ f τ t` is holomorphic on `ball τ₀ R` for a.e. `t`, with a dominator `bound` (integrable on
`(0,∞)`) and an a.e. integrable bound `gderiv` for its `τ`-derivative, then the integral is
differentiable at `τ₀` with derivative the integral of the derivatives. -/
theorem hasDerivAt_integral_Ioi {f : ℂ → ℝ → ℂ} {τ₀ : ℂ} {R : ℝ} (hR : 0 < R)
    (hmeas : ∀ᶠ z in 𝓝 τ₀, AEStronglyMeasurable (fun t => f z t)
      (volume.restrict (Set.Ioi (0 : ℝ))))
    (hgmeas : AEStronglyMeasurable (fun t => deriv (fun z => f z t) τ₀)
      (volume.restrict (Set.Ioi (0 : ℝ))))
    (gderiv : ℝ → ℝ) (hgint : IntegrableOn gderiv (Set.Ioi (0 : ℝ)))
    (hgb : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ∀ z ∈ Metric.ball τ₀ R, ‖deriv (fun z' => f z' t) z‖ ≤ gderiv t)
    (hdiff : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ∀ z ∈ Metric.ball τ₀ R, DifferentiableAt ℂ (fun z' => f z' t) z)
    (hint : IntegrableOn (fun t => f τ₀ t) (Set.Ioi (0 : ℝ))) :
    HasDerivAt (fun z => ∫ t in Set.Ioi (0 : ℝ), f z t)
      (∫ t in Set.Ioi (0 : ℝ), deriv (fun z => f z t) τ₀) τ₀ := by
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    (F := f) (F' := fun x (t : ℝ) => deriv (fun z => f z t) x)
    (bound := gderiv) (x₀ := τ₀) (s := Metric.ball τ₀ (R / 2))
    (Metric.ball_mem_nhds τ₀ (by linarith))
    hmeas
    (by rwa [IntegrableOn] at hint)
    hgmeas
    (by
      filter_upwards [hgb] with t ht z hz
      exact ht z (Metric.ball_subset_ball (by linarith) hz))
    (by rwa [IntegrableOn] at hgint)
    (by
      filter_upwards [hdiff] with t ht z hz
      exact (ht z (Metric.ball_subset_ball (by linarith) hz)).hasDerivAt)
  exact key.2

/-! ## Holomorphy on an open set -/

/-- **Holomorphy of the contour integral.**  Let `U ⊆ ℂ` be open, let `f : ℂ → ℝ → ℂ` be such
that for a.e. `t` the function `z ↦ f z t` is holomorphic on `U`, and suppose there is an
integrable dominator `bound` for `f` on `U`.  If moreover `f z` and its `z`-derivative are a.e.
strongly measurable for every `z ∈ U` — the unavoidable measurability inputs, which in the
concrete application come from the continuity of `τ ↦ K(τ,it)` on the contour — then
`z ↦ ∫_0^∞ f z t dt` is holomorphic on `U`. -/
theorem differentiableOn_integral_Ioi {f : ℂ → ℝ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (bound : ℝ → ℝ) (hbint : IntegrableOn bound (Set.Ioi (0 : ℝ)))
    (hbb : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))), ∀ z ∈ U, ‖f z t‖ ≤ bound t)
    (hdiff : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ∀ z ∈ U, DifferentiableAt ℂ (fun z' => f z' t) z)
    (hmeas : ∀ z ∈ U, AEStronglyMeasurable (fun t => f z t)
      (volume.restrict (Set.Ioi (0 : ℝ))))
    (hdmeas : ∀ z ∈ U, AEStronglyMeasurable (fun t => deriv (fun z' => f z' t) z)
      (volume.restrict (Set.Ioi (0 : ℝ)))) :
    DifferentiableOn ℂ (fun z => ∫ t in Set.Ioi (0 : ℝ), f z t) U := by
  intro τ₀ hτ₀
  obtain ⟨R, hR, hRU⟩ := Metric.mem_nhds_iff.1 (hU.mem_nhds hτ₀)
  have hRpos : 0 < R := hR
  have hR2 : 0 < R / 2 := by linarith
  have hball : Metric.ball τ₀ R ⊆ U := hRU
  have hball2 : Metric.ball τ₀ (R / 2) ⊆ U := fun z hz => hball (Metric.ball_subset_ball (by linarith) hz)
  have hbb' : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ∀ z ∈ Metric.ball τ₀ R, ‖f z t‖ ≤ bound t :=
    hbb.mono fun t ht z hz => ht z (hball hz)
  have hdiff' : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ∀ z ∈ Metric.ball τ₀ R, DifferentiableAt ℂ (fun z' => f z' t) z :=
    hdiff.mono fun t ht z hz => ht z (hball hz)
  have hgb := deriv_bound_of_bound (f := f) (τ₀ := τ₀) hRpos hdiff' hbb'
  have hint : IntegrableOn (fun t => f τ₀ t) (Set.Ioi (0 : ℝ)) :=
    integrableOn_of_bound (hmeas τ₀ hτ₀) hbint (hbb.mono fun t ht => ht τ₀ hτ₀)
  have hmeas' : ∀ᶠ z in 𝓝 τ₀, AEStronglyMeasurable (fun t => f z t)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (show ∀ᶠ z in 𝓝 τ₀, z ∈ U from hU.mem_nhds hτ₀).mono fun z hz => hmeas z hz
  have hbdiff : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ∀ z ∈ Metric.ball τ₀ (R / 2), DifferentiableAt ℂ (fun z' => f z' t) z :=
    hdiff.mono fun t ht z hz => ht z (hball2 hz)
  have := hasDerivAt_integral_Ioi (f := f) (τ₀ := τ₀) hR2 hmeas'
    (hdmeas τ₀ hτ₀) (fun t => (2 / R) * bound t)
    (hbint.const_mul (2 / R)) hgb hbdiff hint
  exact this.differentiableAt.differentiableWithinAt

end Work.Asymptotics
