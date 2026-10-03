import Mathlib
import Submission.Work.PlanarSC.Defs
import Submission.Work.PlanarSC.Tools

/-!
# A continuous square root of a null-winding simple closed curve

`Work.PlanarSC.exists_sqrtCurve`: if `γ : C(Circle, ℂ)` is injective, `z ∉ range γ`, and the
`1`-periodic parametrisation `t ↦ circleParam γ t - z = γ (exp (2 π i t)) - z` admits a continuous
`1`-periodic argument function (`Commons.Topology.Winding.HasArg`), then `γ - z` has a continuous
square root parametrised by the circle: a continuous injective `k : C(Circle, ℂ)` with
`(k u)^2 = γ u - z` for all `u`.

## The mathematics

Write `w t = circleParam γ t - z` and let `θ` be the `1`-periodic argument lift supplied by
`HasArg`, so `w t = ‖w t‖ * exp (θ t * I)`.  The periodic argument is exactly the statement that
`w` has *even* "degree", so the half argument `θ / 2` is again a well-defined function of
`t mod 1`; hence
`Φ t = sqrt (‖w t‖) * exp ((θ t / 2) * I)`
is a `1`-periodic continuous function with `(Φ t)^2 = w t`.  Since `Φ` is `1`-periodic and
continuous it descends to the additive circle `ℝ ⧸ ℤ` (the `AddCircle 1`-quotient of `ℝ`), and
`AddCircle.homeomorphCircle` identifies that quotient with `Circle`, giving the required
`k : C(Circle, ℂ)`.

Injectivity needs no argument hypothesis at all: `k u = k v` gives `(k u)^2 = (k v)^2`, that is
`γ u - z = γ v - z`, hence `γ u = γ v` and `u = v` by injectivity of `γ`.
-/

namespace Work.PlanarSC

open Set

/-- **A null-winding simple closed curve has a continuous square root parametrised by the
circle.**  If `γ : C(Circle, ℂ)` is injective, `z` is off `γ`, and the `1`-periodic curve
`t ↦ γ (exp (2 π i t)) - z` has a continuous `1`-periodic argument function, then there is an
injective `k : C(Circle, ℂ)` with `(k u)^2 = γ u - z` for every `u : Circle`. -/
theorem exists_sqrtCurve (γ : C(Circle, ℂ)) (hγ : Function.Injective γ) {z : ℂ} (hz : z ∉ Set.range γ)
    (hH : Commons.Topology.Winding.HasArg (Work.PlanarSC.circleParam γ) z) :
    ∃ k : C(Circle, ℂ), Function.Injective k ∧ ∀ u : Circle, (k u) ^ 2 = γ u - z := by
  obtain ⟨θ, _hθc, hθper, hθrep⟩ := hH
  -- The half-argument square root, as a `1`-periodic function of the parameter.
  let Φ : ℝ → ℂ := fun t =>
    ((Real.sqrt ‖circleParam γ t - z‖ : ℝ) : ℂ) * (Circle.exp (θ t / 2) : ℂ)
  have hΦper : Function.Periodic Φ 1 := by
    intro t
    show ((Real.sqrt ‖circleParam γ (t + 1) - z‖ : ℝ) : ℂ) * (Circle.exp (θ (t + 1) / 2) : ℂ)
        = ((Real.sqrt ‖circleParam γ t - z‖ : ℝ) : ℂ) * (Circle.exp (θ t / 2) : ℂ)
    rw [circleParam_periodic γ t, hθper t]
  have hΦcont : Continuous Φ := by
    show Continuous (fun t : ℝ =>
      ((Real.sqrt ‖circleParam γ t - z‖ : ℝ) : ℂ) * (Circle.exp (θ t / 2) : ℂ))
    simp only [circleParam_apply]
    fun_prop
  -- The defining property of the square root.
  have hΦsq : ∀ t : ℝ, (Φ t) ^ 2 = circleParam γ t - z := by
    intro t
    show ((((Real.sqrt ‖circleParam γ t - z‖ : ℝ) : ℂ) * (Circle.exp (θ t / 2) : ℂ)) ^ 2
      = circleParam γ t - z)
    rw [mul_pow, ← Complex.ofReal_pow, Real.sq_sqrt (norm_nonneg _), ← Circle.coe_pow]
    have h2 : (Circle.exp (θ t / 2)) ^ 2 = Circle.exp (θ t) := by
      rw [pow_two, ← Circle.exp_add]
      congr 1
      ring
    rw [h2, Circle.coe_exp]
    exact (hθrep t).symm
  -- Descent of a `1`-periodic continuous function to the additive circle `ℝ ⧸ ℤ`.
  have hΨcont : Continuous (hΦper.lift : AddCircle (1 : ℝ) → ℂ) := by
    refine continuous_coinduced_dom.mpr ?_
    show Continuous (fun t : ℝ => hΦper.lift (t : AddCircle (1 : ℝ)))
    simp only [Function.Periodic.lift_coe]
    exact hΦcont
  -- `ℝ ⧸ ℤ ≃ₜ Circle` (via `t ↦ exp (2 π i t)`).
  let h1 : AddCircle (1 : ℝ) ≃ₜ Circle := AddCircle.homeomorphCircle (by norm_num)
  let k : C(Circle, ℂ) := ⟨fun u => hΦper.lift (h1.symm u), hΨcont.comp h1.symm.continuous⟩
  have hh1_apply : ∀ t : ℝ, h1 (t : AddCircle (1 : ℝ)) = Circle.exp (2 * Real.pi * t) := by
    intro t
    show AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0) (t : AddCircle (1 : ℝ))
      = Circle.exp (2 * Real.pi * t)
    rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk]
    congr 1
    ring
  -- The value of `k` at the parametric point.
  have hk_exp : ∀ t : ℝ, k (Circle.exp (2 * Real.pi * t)) = Φ t := by
    intro t
    have h1t := hh1_apply t
    have hs : h1.symm (Circle.exp (2 * Real.pi * t)) = (t : AddCircle (1 : ℝ)) := by
      rw [← h1t, Homeomorph.symm_apply_apply]
    show hΦper.lift (h1.symm (Circle.exp (2 * Real.pi * t))) = Φ t
    rw [hs, Function.Periodic.lift_coe]
  have hkprop : ∀ u : Circle, (k u) ^ 2 = γ u - z := by
    intro u
    obtain ⟨s, hs⟩ := Circle.exp_surjective u
    let t : ℝ := s / (2 * Real.pi)
    have hexp : Circle.exp (2 * Real.pi * t) = u := by
      show Circle.exp (2 * Real.pi * (s / (2 * Real.pi))) = u
      rw [mul_div_cancel₀ _ (by positivity : (2 : ℝ) * Real.pi ≠ 0), hs]
    rw [← hexp, hk_exp t, hΦsq t]
    rfl
  refine ⟨k, ?_, hkprop⟩
  intro u v huv
  have h2 : γ u - z = γ v - z := by
    have h := congrArg (fun w : ℂ => w ^ 2) huv
    rwa [hkprop u, hkprop v] at h
  exact hγ (sub_left_inj.mp h2)

end Work.PlanarSC
