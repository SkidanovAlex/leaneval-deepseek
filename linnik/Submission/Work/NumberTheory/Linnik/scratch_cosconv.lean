import Mathlib

open Real MeasureTheory intervalIntegral

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Commons.NumberTheory.Linnik

/-- `t ↦ sin (a t + b)` has derivative `a cos (a t + b)`. -/
private lemma hasDerivAt_sin_affine (a b t : ℝ) :
    HasDerivAt (fun y : ℝ => Real.sin (a * y + b)) (a * Real.cos (a * t + b)) t := by
  have h1 : HasDerivAt (fun y : ℝ => a * y + b) a t := by
    have h := (hasDerivAt_id t).const_mul a
    have h2 := h.add_const b
    simpa [mul_one] using h2
  have h3 := (Real.hasDerivAt_sin (a * t + b)).comp t h1
  simpa [Function.comp_def, mul_comm] using h3

/-- `t ↦ sin (b - a t)` has derivative `-a cos (b - a t)`. -/
private lemma hasDerivAt_sin_reflect (a b t : ℝ) :
    HasDerivAt (fun y : ℝ => Real.sin (b - a * y)) (-(a * Real.cos (b - a * t))) t := by
  have h1 : HasDerivAt (fun y : ℝ => b - a * y) (-a) t := by
    have h := ((hasDerivAt_id t).const_mul a).const_sub b
    simpa using h
  have h3 := (Real.hasDerivAt_sin (b - a * t)).comp t h1
  have hval : Real.cos (b - a * t) * (-a) = -(a * Real.cos (b - a * t)) := by ring
  simpa [Function.comp_def, hval] using h3

/-- **The convolution-square identity for the extremal function of Heath-Brown Lemma 7.1.**

With `g(t) = λ(1+tan²θ)(cos(ζt) - cos θ)` on `[-γ,γ]` (`ζ = λ tan θ`, `γ = θ/ζ`, so that
`ζγ = θ`), the convolution `g * g` on `[0, 2γ]` is given by the bracket of Lemma 7.1:

`(g*g)(x) = A²[ (2γ-x)/2 · cos(ζx) + sin(2θ-ζx)/(2ζ) - 2cosθ(sinθ + sin(θ-ζx))/ζ + cos²θ(2γ-x) ]`

with `A = λ(1+tan²θ)`.  In particular `g*g` is the function `f` of Lemma 7.1, so `f = g*g`; this is
the structural fact behind both parts of Condition 2 for `f` (`f ≥ 0` on `[0,2γ]`, and
`ℜ F(it) ≥ 0` by the convolution theorem for the cosine transform). -/
theorem cosG_conv {θ lam : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam) :
    let ζ : ℝ := lam * Real.tan θ
    let γ : ℝ := θ / ζ
    ∀ x : ℝ,
      (∫ t in (x - γ)..γ,
          (lam * (1 + Real.tan θ ^ 2) * (Real.cos (ζ * t) - Real.cos θ))
            * (lam * (1 + Real.tan θ ^ 2) * (Real.cos (ζ * (x - t)) - Real.cos θ)))
        = (lam * (1 + Real.tan θ ^ 2)) ^ 2 *
          ((2 * γ - x) / 2 * Real.cos (ζ * x) + Real.sin (2 * θ - ζ * x) / (2 * ζ)
            - 2 * Real.cos θ * (Real.sin θ + Real.sin (θ - ζ * x)) / ζ
            + Real.cos θ ^ 2 * (2 * γ - x)) := by
  intro ζ γ x
  have hζdef : ζ = lam * Real.tan θ := rfl
  have hγdef : γ = θ / ζ := rfl
  have htanpos : 0 < Real.tan θ := Real.tan_pos_of_pos_of_lt_pi_div_two hθ0 hθ1
  have hζpos : 0 < ζ := by rw [hζdef]; positivity
  have hζne : ζ ≠ 0 := ne_of_gt hζpos
  have hζγ : ζ * γ = θ := by rw [hγdef]; field_simp
  set A : ℝ := lam * (1 + Real.tan θ ^ 2) with hAdef
  set c : ℝ := Real.cos θ with hcdef
  have hpt : ∀ t : ℝ,
      (A * (Real.cos (ζ * t) - c)) * (A * (Real.cos (ζ * (x - t)) - c))
        = A ^ 2 * (Real.cos (ζ * x) / 2 + Real.cos (2 * ζ * t - ζ * x) / 2
            - c * Real.cos (ζ * t) - c * Real.cos (ζ * x - ζ * t) + c ^ 2) := by
    intro t
    have harg : ζ * (x - t) = ζ * x - ζ * t := by ring
    rw [harg]
    have hcc : Real.cos (ζ * t) * Real.cos (ζ * x - ζ * t)
        = Real.cos (ζ * x) / 2 + Real.cos (2 * ζ * t - ζ * x) / 2 := by
      have h2 := Real.cos_add (ζ * t) (ζ * x - ζ * t)
      have h3 := Real.cos_sub (ζ * t) (ζ * x - ζ * t)
      have e1 : ζ * t + (ζ * x - ζ * t) = ζ * x := by ring
      have e2 : ζ * t - (ζ * x - ζ * t) = 2 * ζ * t - ζ * x := by ring
      rw [e1] at h2
      rw [e2] at h3
      linarith
    rw [show (A * (Real.cos (ζ * t) - c)) * (A * (Real.cos (ζ * x - ζ * t) - c))
        = A ^ 2 * (Real.cos (ζ * t) * Real.cos (ζ * x - ζ * t) - c * Real.cos (ζ * t)
            - c * Real.cos (ζ * x - ζ * t) + c ^ 2) from by ring, hcc]
  have hΦ : ∀ t : ℝ, HasDerivAt (fun y : ℝ => A ^ 2 *
        (Real.cos (ζ * x) / 2 * y + Real.sin (2 * ζ * y - ζ * x) / (4 * ζ)
          - c * Real.sin (ζ * y) / ζ + c * Real.sin (ζ * x - ζ * y) / ζ + c ^ 2 * y))
      (A ^ 2 * (Real.cos (ζ * x) / 2 + Real.cos (2 * ζ * t - ζ * x) / 2
        - c * Real.cos (ζ * t) - c * Real.cos (ζ * x - ζ * t) + c ^ 2)) t := by
    intro t
    have h1 : HasDerivAt (fun y : ℝ => Real.cos (ζ * x) / 2 * y) (Real.cos (ζ * x) / 2) t := by
      simpa using (hasDerivAt_id t).const_mul (Real.cos (ζ * x) / 2)
    have h2 : HasDerivAt (fun y : ℝ => Real.sin (2 * ζ * y - ζ * x) / (4 * ζ))
        (Real.cos (2 * ζ * t - ζ * x) / 2) t := by
      have h := (hasDerivAt_sin_affine (2 * ζ) (-(ζ * x)) t).div_const (4 * ζ)
      have harg : 2 * ζ * t + -(ζ * x) = 2 * ζ * t - ζ * x := by ring
      rw [harg] at h
      have hval : 2 * ζ * Real.cos (2 * ζ * t - ζ * x) / (4 * ζ)
          = Real.cos (2 * ζ * t - ζ * x) / 2 := by
        field_simp
        ring
      rw [hval] at h
      exact h
    have h3 : HasDerivAt (fun y : ℝ => c * Real.sin (ζ * y) / ζ) (c * Real.cos (ζ * t)) t := by
      have h := ((hasDerivAt_sin_affine ζ 0 t).const_mul c).div_const ζ
      have hval : c * (ζ * Real.cos (ζ * t + 0)) / ζ = c * Real.cos (ζ * t) := by
        rw [add_zero]
        field_simp
      rw [hval] at h
      simpa using h
    have h4 : HasDerivAt (fun y : ℝ => c * Real.sin (ζ * x - ζ * y) / ζ)
        (-(c * Real.cos (ζ * x - ζ * t))) t := by
      have h := ((hasDerivAt_sin_reflect ζ (ζ * x) t).const_mul c).div_const ζ
      have hval : c * (-(ζ * Real.cos (ζ * x - ζ * t))) / ζ
          = -(c * Real.cos (ζ * x - ζ * t)) := by
        field_simp
      rw [hval] at h
      exact h
    have h5 : HasDerivAt (fun y : ℝ => c ^ 2 * y) (c ^ 2) t := by
      simpa using (hasDerivAt_id t).const_mul (c ^ 2)
    have htot := (((h1.add h2).sub h3).add h4).add h5
    have hfun : (((((fun y : ℝ => (Real.cos (ζ * x) / 2 * y))
            + (fun y : ℝ => (Real.sin (2 * ζ * y - ζ * x) / (4 * ζ))))
          - (fun y : ℝ => (c * Real.sin (ζ * y) / ζ)))
          + (fun y : ℝ => (c * Real.sin (ζ * x - ζ * y) / ζ)))
          + (fun y : ℝ => (c ^ 2 * y)))
        = (fun y : ℝ => (Real.cos (ζ * x) / 2 * y + Real.sin (2 * ζ * y - ζ * x) / (4 * ζ)
            - c * Real.sin (ζ * y) / ζ + c * Real.sin (ζ * x - ζ * y) / ζ + c ^ 2 * y)) := by
      funext y
      simp only [Pi.add_apply, Pi.sub_apply]
    rw [hfun] at htot
    have hd : Real.cos (ζ * x) / 2 + Real.cos (2 * ζ * t - ζ * x) / 2 - c * Real.cos (ζ * t)
          + -(c * Real.cos (ζ * x - ζ * t)) + c ^ 2
        = Real.cos (ζ * x) / 2 + Real.cos (2 * ζ * t - ζ * x) / 2 - c * Real.cos (ζ * t)
          - c * Real.cos (ζ * x - ζ * t) + c ^ 2 := by ring
    rw [hd] at htot
    exact htot.const_mul (A ^ 2)
  have hint : IntervalIntegrable (fun t : ℝ => A ^ 2 * (Real.cos (ζ * x) / 2
      + Real.cos (2 * ζ * t - ζ * x) / 2 - c * Real.cos (ζ * t)
      - c * Real.cos (ζ * x - ζ * t) + c ^ 2)) volume (x - γ) γ := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_congr (g := fun t : ℝ => A ^ 2 * (Real.cos (ζ * x) / 2
      + Real.cos (2 * ζ * t - ζ * x) / 2 - c * Real.cos (ζ * t)
      - c * Real.cos (ζ * x - ζ * t) + c ^ 2)) (fun t _ => hpt t)]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun y : ℝ => A ^ 2 *
        (Real.cos (ζ * x) / 2 * y + Real.sin (2 * ζ * y - ζ * x) / (4 * ζ)
          - c * Real.sin (ζ * y) / ζ + c * Real.sin (ζ * x - ζ * y) / ζ + c ^ 2 * y))
      (f' := fun t : ℝ => A ^ 2 * (Real.cos (ζ * x) / 2 + Real.cos (2 * ζ * t - ζ * x) / 2
        - c * Real.cos (ζ * t) - c * Real.cos (ζ * x - ζ * t) + c ^ 2)) (fun t _ => hΦ t) hint]
  have hA1 : 2 * ζ * γ = 2 * θ := by rw [mul_assoc, hζγ]
  have hx1 : ζ * (x - γ) = ζ * x - θ := by rw [mul_sub, hζγ]
  have hval : A ^ 2 * (Real.cos (ζ * x) / 2 * γ + Real.sin (2 * ζ * γ - ζ * x) / (4 * ζ)
        - c * Real.sin (ζ * γ) / ζ + c * Real.sin (ζ * x - ζ * γ) / ζ + c ^ 2 * γ)
      - A ^ 2 * (Real.cos (ζ * x) / 2 * (x - γ) + Real.sin (2 * ζ * (x - γ) - ζ * x) / (4 * ζ)
        - c * Real.sin (ζ * (x - γ)) / ζ + c * Real.sin (ζ * x - ζ * (x - γ)) / ζ
        + c ^ 2 * (x - γ))
      = A ^ 2 * ((2 * γ - x) / 2 * Real.cos (ζ * x) + Real.sin (2 * θ - ζ * x) / (2 * ζ)
          - 2 * Real.cos θ * (Real.sin θ + Real.sin (θ - ζ * x)) / ζ
          + Real.cos θ ^ 2 * (2 * γ - x)) := by
    rw [hA1, hζγ, hx1]
    have e1 : 2 * ζ * (x - γ) - ζ * x = ζ * x - 2 * θ := by rw [mul_sub, hA1]; ring
    rw [e1]
    have e2 : ζ * x - (ζ * x - θ) = θ := by ring
    rw [e2]
    have e3 : Real.sin (ζ * x - 2 * θ) = -Real.sin (2 * θ - ζ * x) := by
      rw [← Real.sin_neg]; congr 1; ring
    have e4 : Real.sin (ζ * x - θ) = -Real.sin (θ - ζ * x) := by
      rw [← Real.sin_neg]; congr 1; ring
    rw [e3, e4, hcdef]
    field_simp
    ring
  rw [hval]

end Commons.NumberTheory.Linnik
