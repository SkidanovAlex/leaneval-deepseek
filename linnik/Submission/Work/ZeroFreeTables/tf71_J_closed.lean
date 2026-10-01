import Mathlib

namespace Work.ZeroFreeTables

/-- `1 - cos (2x) = 2 sin²x`. -/
lemma one_sub_cos_two_mul (x : ℝ) : 1 - Real.cos (2 * x) = 2 * Real.sin x ^ 2 := by
  rw [Real.cos_two_mul, Real.sin_sq]
  ring

/-- Sum of two sine waves. -/
lemma sin_half_sum (c x : ℝ) :
    Real.sin ((1 + c) * x) / 2 + Real.sin ((1 - c) * x) / 2 = Real.sin x * Real.cos (c * x) := by
  rw [show (1 + c) * x = x + c * x by ring, show (1 - c) * x = x - c * x by ring]
  rw [Real.sin_add, Real.sin_sub]
  ring

/-- Derivative of `u ↦ c * u`. -/
lemma hasDerivAt_mul_left (c x : ℝ) : HasDerivAt (fun u : ℝ => c * u) c x := by
  have h := (hasDerivAt_id x).const_mul c
  simp only [mul_one] at h
  exact h

/-- Derivative of `u ↦ sin (c * u) / c`. -/
lemma hasDeriv_sin_div (c x : ℝ) (hc : c ≠ 0) :
    HasDerivAt (fun u : ℝ => Real.sin (c * u) / c) (Real.cos (c * x)) x := by
  have h2 := (hasDerivAt_mul_left c x).sin.div_const c
  have he : (Real.cos (c * x) * c) / c = Real.cos (c * x) := by field_simp
  rw [he] at h2
  exact h2

/-- Derivative of `u ↦ cos (c * u) / c ^ 2`. -/
lemma hasDeriv_cos_div_c2 (c x : ℝ) (hc : c ≠ 0) :
    HasDerivAt (fun u : ℝ => Real.cos (c * u) / c ^ 2) (-(Real.sin (c * x) / c)) x := by
  have h2 := (hasDerivAt_mul_left c x).cos.div_const (c ^ 2)
  have he : (-Real.sin (c * x) * c) / c ^ 2 = -(Real.sin (c * x) / c) := by field_simp
  rw [he] at h2
  exact h2

/-- Derivative of `u ↦ cos (k * u) / (2k)`. -/
lemma hasDeriv_cos_div_2k (k x : ℝ) (hk : k ≠ 0) :
    HasDerivAt (fun u : ℝ => Real.cos (k * u) / (2 * k)) (-(Real.sin (k * x)) / 2) x := by
  have h2 := (hasDerivAt_mul_left k x).cos.div_const (2 * k)
  have he : (-Real.sin (k * x) * k) / (2 * k) = -(Real.sin (k * x)) / 2 := by field_simp
  rw [he] at h2
  exact h2

/-- Antiderivative of `(2θ - u) cos (c u)`. -/
lemma hasDeriv_lin (c θ x : ℝ) (hc : c ≠ 0) :
    HasDerivAt (fun u : ℝ => (2 * θ - u) * (Real.sin (c * u) / c) - Real.cos (c * u) / c ^ 2)
      ((2 * θ - x) * Real.cos (c * x)) x := by
  have h1 := hasDeriv_sin_div c x hc
  have h2 := hasDeriv_cos_div_c2 c x hc
  have hlin : HasDerivAt (fun u : ℝ => 2 * θ - u) (-1) x := by
    have h := (hasDerivAt_const x (2 * θ)).sub (hasDerivAt_id x)
    rw [show (0:ℝ) - 1 = -1 by ring] at h
    exact h
  have hres := (hlin.mul h1).sub h2
  have he : ((-1) * (Real.sin (c * x) / c) + (2 * θ - x) * Real.cos (c * x)) - (-(Real.sin (c * x) / c))
      = (2 * θ - x) * Real.cos (c * x) := by ring
  rw [he] at hres
  exact hres

/-- Final trig/algebra identity converting the antiderivative endpoint difference to the
claimed closed form. -/
lemma final_identity (θ c : ℝ) (hc0 : c ≠ 0) (hc1 : c ≠ 1) (hc2 : c ≠ -1) :
    Real.cos θ ^ 2 * (1 - Real.cos (c*(2*θ)))/c^2
      + (1 - Real.cos ((1+c)*(2*θ)))/(2*(1+c))
      + (1 - Real.cos ((1-c)*(2*θ)))/(2*(1-c))
      - (2*Real.sin θ*Real.cos θ)*Real.sin (c*(2*θ))/c
    = 2 * Real.cos θ ^ 2 * (Real.sin (c*θ))^2 / c^2
      - (Real.cos θ * Real.sin (c*θ) - Real.sin θ * Real.cos (c*θ))^2 / (c-1)
      + (Real.cos θ * Real.sin (c*θ) + Real.sin θ * Real.cos (c*θ))^2 / (c+1)
      - 4 * Real.sin θ * Real.cos θ * Real.sin (c*θ) * Real.cos (c*θ) / c := by
  have hcp1 : (1:ℝ) + c ≠ 0 := by intro h; exact hc2 (by linarith)
  have hcp1' : c + 1 ≠ 0 := by intro h; exact hc2 (by linarith)
  have hcm1 : (1:ℝ) - c ≠ 0 := by intro h; exact hc1 (by linarith)
  have hcm1' : c - 1 ≠ 0 := by intro h; exact hc1 (by linarith)
  rw [show c*(2*θ) = 2*(c*θ) by ring,
      show (1+c)*(2*θ) = 2*((c+1)*θ) by ring,
      show (1-c)*(2*θ) = 2*((1-c)*θ) by ring]
  rw [one_sub_cos_two_mul (c*θ), one_sub_cos_two_mul ((c+1)*θ), one_sub_cos_two_mul ((1-c)*θ)]
  rw [Real.sin_two_mul (c*θ)]
  have hP : Real.cos θ * Real.sin (c*θ) - Real.sin θ * Real.cos (c*θ) = Real.sin ((c-1)*θ) := by
    rw [show (c-1)*θ = c*θ - θ by ring, Real.sin_sub]; ring
  have hQ : Real.cos θ * Real.sin (c*θ) + Real.sin θ * Real.cos (c*θ) = Real.sin ((c+1)*θ) := by
    rw [show (c+1)*θ = c*θ + θ by ring, Real.sin_add]; ring
  have hc1sq : Real.sin ((1-c)*θ)^2 = Real.sin ((c-1)*θ)^2 := by
    rw [show (1-c)*θ = -((c-1)*θ) by ring, Real.sin_neg]; ring
  rw [hP, hQ, hc1sq]
  field_simp
  ring

theorem tf71_J_closed (θ c : ℝ) (hc0 : c ≠ 0) (hc1 : c ≠ 1) (hc2 : c ≠ -1) :
    (∫ u in (0:ℝ)..(2*θ), Real.cos (c*u) *
        (Real.cos θ ^ 2 * (2*θ - u) + Real.sin u - 2 * Real.sin θ * Real.cos θ))
      = 2 * Real.cos θ ^ 2 * (Real.sin (c*θ))^2 / c^2
        - (Real.cos θ * Real.sin (c*θ) - Real.sin θ * Real.cos (c*θ))^2 / (c-1)
        + (Real.cos θ * Real.sin (c*θ) + Real.sin θ * Real.cos (c*θ))^2 / (c+1)
        - 4 * Real.sin θ * Real.cos θ * Real.sin (c*θ) * Real.cos (c*θ) / c := by
  have hcp1 : (1:ℝ) + c ≠ 0 := by intro h; exact hc2 (by linarith)
  have hcm1 : (1:ℝ) - c ≠ 0 := by intro h; exact hc1 (by linarith)
  let F : ℝ → ℝ := fun u =>
      Real.cos θ ^ 2 * ((2*θ - u) * (Real.sin (c*u)/c) - Real.cos (c*u)/c^2)
      - (Real.cos ((1+c)*u)/(2*(1+c)) + Real.cos ((1-c)*u)/(2*(1-c)))
      - (2 * Real.sin θ * Real.cos θ) * (Real.sin (c*u)/c)
  have hderiv : ∀ x : ℝ,
      HasDerivAt F (Real.cos (c*x) * (Real.cos θ ^ 2 * (2*θ - x) + Real.sin x - 2 * Real.sin θ * Real.cos θ)) x := by
    intro x
    have hA : HasDerivAt (fun u : ℝ => Real.cos θ ^ 2 * ((2*θ - u) * (Real.sin (c*u)/c) - Real.cos (c*u)/c^2))
        (Real.cos θ ^ 2 * ((2*θ - x) * Real.cos (c*x))) x :=
      (hasDeriv_lin c θ x hc0).const_mul (Real.cos θ ^ 2)
    have h3 : HasDerivAt (fun u : ℝ => Real.cos ((1+c)*u)/(2*(1+c))) (-(Real.sin ((1+c)*x))/2) x :=
      hasDeriv_cos_div_2k (1+c) x hcp1
    have h4 : HasDerivAt (fun u : ℝ => Real.cos ((1-c)*u)/(2*(1-c))) (-(Real.sin ((1-c)*x))/2) x :=
      hasDeriv_cos_div_2k (1-c) x hcm1
    have hB : HasDerivAt (fun u : ℝ => Real.cos ((1+c)*u)/(2*(1+c)) + Real.cos ((1-c)*u)/(2*(1-c)))
        (-(Real.sin ((1+c)*x))/2 + -(Real.sin ((1-c)*x))/2) x := h3.add h4
    have hC : HasDerivAt (fun u : ℝ => (2 * Real.sin θ * Real.cos θ) * (Real.sin (c*u)/c))
        ((2 * Real.sin θ * Real.cos θ) * Real.cos (c*x)) x :=
      (hasDeriv_sin_div c x hc0).const_mul _
    have hABC := (hA.sub hB).sub hC
    have hgoal : (Real.cos θ ^ 2 * ((2*θ - x) * Real.cos (c*x))
          - (-(Real.sin ((1+c)*x))/2 + -(Real.sin ((1-c)*x))/2))
          - (2 * Real.sin θ * Real.cos θ) * Real.cos (c*x)
        = Real.cos (c*x) * (Real.cos θ ^ 2 * (2*θ - x) + Real.sin x - 2 * Real.sin θ * Real.cos θ) := by
      have hX : -(Real.sin ((1+c)*x))/2 + -(Real.sin ((1-c)*x))/2 = -(Real.sin x * Real.cos (c*x)) := by
        rw [← sin_half_sum c x]; ring
      rw [hX]; ring
    rw [hgoal] at hABC
    exact hABC
  have hint : IntervalIntegrable (fun u : ℝ => Real.cos (c*u) * (Real.cos θ ^ 2 * (2*θ - u) + Real.sin u - 2 * Real.sin θ * Real.cos θ)) MeasureTheory.volume (0:ℝ) (2*θ) :=
    (by fun_prop : Continuous fun u : ℝ => Real.cos (c*u) * (Real.cos θ ^ 2 * (2*θ - u) + Real.sin u - 2 * Real.sin θ * Real.cos θ)).intervalIntegrable 0 (2*θ)
  have hInt := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := F)
      (f' := fun u : ℝ => Real.cos (c*u) * (Real.cos θ ^ 2 * (2*θ - u) + Real.sin u - 2 * Real.sin θ * Real.cos θ))
      (fun x _ => hderiv x) hint
  rw [hInt]
  have hval : F (2*θ) - F 0 =
      Real.cos θ ^ 2 * (1 - Real.cos (c*(2*θ)))/c^2
      + (1 - Real.cos ((1+c)*(2*θ)))/(2*(1+c))
      + (1 - Real.cos ((1-c)*(2*θ)))/(2*(1-c))
      - (2*Real.sin θ*Real.cos θ)*Real.sin (c*(2*θ))/c := by
    simp only [F]
    simp only [Real.sin_zero, Real.cos_zero, mul_zero, sub_zero, zero_sub, zero_div]
    field_simp
    ring
  rw [hval]
  exact final_identity θ c hc0 hc1 hc2

end Work.ZeroFreeTables
