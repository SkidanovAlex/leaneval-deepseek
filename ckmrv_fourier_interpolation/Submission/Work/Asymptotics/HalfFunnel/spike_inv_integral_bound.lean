import Mathlib

namespace Work.Asymptotics.HalfFunnel

open MeasureTheory

/-! ## The base case `m = 0` of the spike model integral

We prove that the (signed) interval integral
`∫_{-ρ}^{ρ} e^{-a(y+u)} (u + iε)⁻¹ du`
is bounded uniformly in `a > 0` and `0 < |ε| ≤ 1/4`, for `0 < ρ < y`.

The integrand is split as `(u + iε)⁻¹ = (u - iε)/(u² + ε²)`, so that pointwise
`e^{-a(y+u)} (u + iε)⁻¹ = ↑(e^{-a y} u/(u²+ε²))
   + ↑((e^{-a(y+u)} - e^{-a y}) u/(u²+ε²))
   - ↑(e^{-a(y+u)} ε/(u²+ε²)) · I`.

The first summand has vanishing integral (the function `u ↦ u/(u²+ε²)` is odd), the second is
bounded by the mean value theorem (`|e^{-a(y+u)} - e^{-a y}| ≤ a e^{-a(y-ρ)}|u|`, and
`|u|²/(u²+ε²) ≤ 1`), and the third is an *absolute* integral, bounded by
`|ε| ∫_{-ρ}^{ρ} du/(u²+ε²) ≤ π`. -/

/-- Casting the real exponential: `exp (-(a:ℂ) * (y + u)) = ↑(exp (-(a*(y+u))))`. -/
lemma spike_exp_neg_mul_ofReal (a y u : ℝ) :
    Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) = ((Real.exp (-(a * (y + u))) : ℝ) : ℂ) := by
  rw [show -(a : ℂ) * ((y : ℂ) + (u : ℂ)) = ((-(a * (y + u)) : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_exp]

/-- The reciprocal of `u + iε` for real `u` and `ε ≠ 0`, in terms of the real denominator
`u² + ε²`. -/
lemma spike_inv_add_mul_I {u ε : ℝ} (hε : ε ≠ 0) :
    ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹
      = ((u : ℂ) - (ε : ℂ) * Complex.I) * (((u ^ 2 + ε ^ 2 : ℝ)) : ℂ)⁻¹ := by
  have hmul : ((u : ℂ) + (ε : ℂ) * Complex.I) * ((u : ℂ) - (ε : ℂ) * Complex.I)
      = ((u ^ 2 + ε ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring_nf
    simp
  have hne : (u : ℂ) + (ε : ℂ) * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact hε this
  have hne2 : (u : ℂ) - (ε : ℂ) * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact hε this
  have hD : ((u ^ 2 + ε ^ 2 : ℝ) : ℂ) ≠ 0 := by rw [← hmul]; exact mul_ne_zero hne hne2
  apply inv_eq_of_mul_eq_one_right
  rw [← mul_assoc, hmul, mul_inv_cancel₀ hD]

/-- The odd function `u ↦ u/(u²+ε²)` has vanishing integral over a symmetric interval. -/
lemma spike_odd_integral (ρ ε : ℝ) :
    (∫ u in (-ρ)..ρ, u / (u ^ 2 + ε ^ 2)) = 0 := by
  have hodd : ∀ x : ℝ, (-x) / ((-x) ^ 2 + ε ^ 2) = -(x / (x ^ 2 + ε ^ 2)) := by
    intro x; ring
  have h1 : (∫ x in (-ρ)..ρ, (-x) / ((-x) ^ 2 + ε ^ 2))
      = ∫ x in (-ρ)..ρ, x / (x ^ 2 + ε ^ 2) := by
    have := intervalIntegral.integral_comp_neg (a := -ρ) (b := ρ)
      (f := fun x : ℝ => x / (x ^ 2 + ε ^ 2))
    simpa using this
  have h2 : (∫ x in (-ρ)..ρ, (-x) / ((-x) ^ 2 + ε ^ 2))
      = ∫ x in (-ρ)..ρ, -(x / (x ^ 2 + ε ^ 2)) := by
    apply intervalIntegral.integral_congr
    intro x _
    exact hodd x
  rw [h2, intervalIntegral.integral_neg] at h1
  linarith

/-- `∫_{-ρ}^{ρ} du/(u²+ε²) ≤ π/|ε|` for `ε ≠ 0`: the antiderivative is
`u ↦ arctan(u/|ε|)/|ε|` and `|arctan| < π/2`. -/
lemma spike_inv_sq_integral_le {ρ ε : ℝ} (hε : ε ≠ 0) :
    (∫ u in (-ρ)..ρ, (u ^ 2 + ε ^ 2)⁻¹) ≤ Real.pi / |ε| := by
  have hεpos : 0 < |ε| := abs_pos.mpr hε
  have habs : |ε| ^ 2 = ε ^ 2 := sq_abs ε
  have hsq : 0 < ε ^ 2 := by simpa [sq] using mul_self_pos.mpr hε
  have hderiv : ∀ x ∈ Set.uIcc (-ρ) ρ,
      HasDerivAt (fun u : ℝ => Real.arctan (u / |ε|) / |ε|) ((x ^ 2 + ε ^ 2)⁻¹) x := by
    intro x _
    have h1 : HasDerivAt (fun u : ℝ => u / |ε|) (1 / |ε|) x := by
      simpa using (hasDerivAt_id x).div_const |ε|
    have h2 := ((Real.hasDerivAt_arctan (x / |ε|)).comp x h1).div_const |ε|
    refine h2.congr_deriv ?_
    have hx : x ^ 2 + ε ^ 2 ≠ 0 := by nlinarith [sq_nonneg x]
    field_simp
    rw [habs]
    ring
  have hint : IntervalIntegrable (fun x : ℝ => (x ^ 2 + ε ^ 2)⁻¹) volume (-ρ) ρ := by
    apply Continuous.intervalIntegrable
    apply Continuous.inv₀
    · fun_prop
    · intro x; nlinarith [sq_nonneg x]
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [h, ← sub_div]
  apply div_le_div_of_nonneg_right _ hεpos.le
  have ha := Real.arctan_lt_pi_div_two (ρ / |ε|)
  have hb := Real.neg_pi_div_two_lt_arctan ((-ρ) / |ε|)
  linarith

/-- Mean value bound for the exponential weight: for `u ∈ [-ρ,ρ]`,
`|e^{-a(y+u)} - e^{-ay}| ≤ a e^{-a(y-ρ)} |u|`. -/
lemma spike_exp_sub_le {a y ρ u : ℝ} (ha : 0 < a) (hρ : 0 < ρ) (hρy : ρ < y)
    (hu : u ∈ Set.Icc (-ρ) ρ) :
    |Real.exp (-(a * (y + u))) - Real.exp (-(a * y))|
      ≤ a * Real.exp (-(a * (y - ρ))) * |u| := by
  have hderiv : ∀ x ∈ Set.Icc (-ρ) ρ,
      deriv (fun t : ℝ => Real.exp (-(a * (y + t)))) x = Real.exp (-(a * (y + x))) * (-a) := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => a * (y + t)) a x := by
      have h := ((hasDerivAt_id x).const_mul a).const_add (a * y)
      simpa [mul_add, add_comm, add_left_comm, add_assoc] using h
    exact (h1.neg.exp).deriv
  have hbound : ∀ x ∈ Set.Icc (-ρ) ρ,
      ‖deriv (fun t : ℝ => Real.exp (-(a * (y + t)))) x‖ ≤ a * Real.exp (-(a * (y - ρ))) := by
    intro x hx
    rw [hderiv x hx, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos ha,
      abs_of_pos (Real.exp_pos _)]
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_left _ ha.le
    apply Real.exp_le_exp.mpr
    nlinarith [hx.1, ha]
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := fun t : ℝ => Real.exp (-(a * (y + t))))
      (s := Set.Icc (-ρ) ρ) (x := 0) (y := u) (C := a * Real.exp (-(a * (y - ρ))))
      (fun x _ => by fun_prop) hbound (convex_Icc _ _) (by constructor <;> linarith) hu
  simpa [Real.norm_eq_abs, sub_zero] using h

/-- `sup_{a>0} a e^{-a(y-ρ)} ≤ 1/(y-ρ)`. -/
lemma spike_mul_exp_le_inv {a y ρ : ℝ} (ha : 0 < a) (hρy : ρ < y) :
    a * Real.exp (-(a * (y - ρ))) ≤ 1 / (y - ρ) := by
  have hc : 0 < y - ρ := by linarith
  have h1 : a * (y - ρ) * Real.exp (-(a * (y - ρ))) ≤ 1 := by
    have hle : a * (y - ρ) ≤ Real.exp (a * (y - ρ)) := by
      have := Real.add_one_le_exp (a * (y - ρ)); linarith
    calc a * (y - ρ) * Real.exp (-(a * (y - ρ)))
        ≤ Real.exp (a * (y - ρ)) * Real.exp (-(a * (y - ρ))) :=
          mul_le_mul_of_nonneg_right hle (Real.exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add]; simp
  rw [le_div_iff₀ hc]
  calc a * Real.exp (-(a * (y - ρ))) * (y - ρ)
      = a * (y - ρ) * Real.exp (-(a * (y - ρ))) := by ring
    _ ≤ 1 := h1

/-- The base case `m = 0` of `spike_model_integral`: for `0 < ρ < y` the integral
`∫_{-ρ}^{ρ} e^{-a(y+u)}(u+iε)⁻¹ du` is bounded uniformly over `a > 0` and `0 < |ε| ≤ 1/4`.

Strategy: `(u+iε)⁻¹ = (u-iε)/(u²+ε²)`, so the integral is
`∫ g(u) u/(u²+ε²) du - iε ∫ g(u)/(u²+ε²) du` with `g u = e^{-a(y+u)}`.  The second piece is bounded
by `|ε| ∫_{-ρ}^ρ (u²+ε²)⁻¹ du ≤ π`.  For the first, write `g u = g 0 + (g u - g 0)`; the
constant part integrates to `0` because `u ↦ u/(u²+ε²)` is odd, and `|g u - g 0| ≤ a e^{-a(y-ρ)} |u|`
by the mean value theorem, so the first piece is bounded by `2ρ a e^{-a(y-ρ)} ≤ 2ρ/(e(y-ρ))`. -/
theorem spike_inv_integral_bound {y ρ : ℝ} (hy : 0 < y) (hρ : 0 < ρ) (hρy : ρ < y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a ε : ℝ), 0 < a → ε ≠ 0 → |ε| ≤ 1 / 4 →
      ‖∫ u in (-ρ)..ρ, Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) *
          ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹‖ ≤ C := by
  refine ⟨Real.pi + 2 * ρ / (y - ρ), ?_, ?_⟩
  · have hc : 0 < y - ρ := by linarith
    positivity
  · intro a ε ha hε hεle
    have hc : 0 < y - ρ := by linarith
    have hle : -ρ ≤ ρ := by linarith
    have hsq : 0 < ε ^ 2 := by simpa [sq] using mul_self_pos.mpr hε
    have hden : ∀ u : ℝ, u ^ 2 + ε ^ 2 ≠ 0 := by
      intro u; nlinarith [sq_nonneg u]
    -- ### pointwise decomposition of the integrand
    have hpt : ∀ u : ℝ,
        Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) * ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹
        = ((Real.exp (-(a * y)) * u / (u ^ 2 + ε ^ 2) : ℝ) : ℂ)
          + (((Real.exp (-(a * (y + u))) - Real.exp (-(a * y))) * u / (u ^ 2 + ε ^ 2) : ℝ) : ℂ)
          - (((Real.exp (-(a * (y + u))) / (u ^ 2 + ε ^ 2)) * ε : ℝ) : ℂ) * Complex.I := by
      intro u
      have hDc : ((u ^ 2 + ε ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hden u
      rw [spike_exp_neg_mul_ofReal, spike_inv_add_mul_I hε]
      push_cast
      field_simp
      ring
    -- ### the constant part integrates to zero
    have hInt0 : (∫ u in (-ρ)..ρ, ((Real.exp (-(a * y)) * u / (u ^ 2 + ε ^ 2) : ℝ) : ℂ)) = 0 := by
      have hcongr : (∫ u in (-ρ)..ρ, ((Real.exp (-(a * y)) * u / (u ^ 2 + ε ^ 2) : ℝ) : ℂ))
          = ∫ u in (-ρ)..ρ, ((Real.exp (-(a * y)) * (u / (u ^ 2 + ε ^ 2)) : ℝ) : ℂ) := by
        apply intervalIntegral.integral_congr
        intro u _
        rw [Complex.ofReal_inj]
        ring
      rw [hcongr, intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul,
        spike_odd_integral, mul_zero, Complex.ofReal_zero]
    -- ### integrability of the three summands
    have hi0 : IntervalIntegrable
        (fun u : ℝ => ((Real.exp (-(a * y)) * u / (u ^ 2 + ε ^ 2) : ℝ) : ℂ)) volume (-ρ) ρ := by
      have hr : Continuous (fun u : ℝ => Real.exp (-(a * y)) * u / (u ^ 2 + ε ^ 2)) := by
        apply Continuous.div
        · fun_prop
        · fun_prop
        · exact hden
      exact (Complex.continuous_ofReal.comp hr).intervalIntegrable (-ρ) ρ
    have hi1 : IntervalIntegrable
        (fun u : ℝ =>
          (((Real.exp (-(a * (y + u))) - Real.exp (-(a * y))) * u / (u ^ 2 + ε ^ 2) : ℝ) : ℂ))
        volume (-ρ) ρ := by
      have hr : Continuous
          (fun u : ℝ => (Real.exp (-(a * (y + u))) - Real.exp (-(a * y))) * u / (u ^ 2 + ε ^ 2)) := by
        apply Continuous.div
        · fun_prop
        · fun_prop
        · exact hden
      exact (Complex.continuous_ofReal.comp hr).intervalIntegrable (-ρ) ρ
    have hi2 : IntervalIntegrable
        (fun u : ℝ =>
          (((Real.exp (-(a * (y + u))) / (u ^ 2 + ε ^ 2)) * ε : ℝ) : ℂ) * Complex.I)
        volume (-ρ) ρ := by
      have hr : Continuous (fun u : ℝ => (Real.exp (-(a * (y + u))) / (u ^ 2 + ε ^ 2)) * ε) := by
        apply Continuous.mul
        · apply Continuous.div
          · fun_prop
          · fun_prop
          · exact hden
        · fun_prop
      have hc2 : Continuous
          (fun u : ℝ => (((Real.exp (-(a * (y + u))) / (u ^ 2 + ε ^ 2)) * ε : ℝ) : ℂ)
            * Complex.I) :=
        (Complex.continuous_ofReal.comp hr).mul continuous_const
      exact hc2.intervalIntegrable (-ρ) ρ
    -- ### bound on the mean value part
    have hInt1 : ‖∫ u in (-ρ)..ρ,
        (((Real.exp (-(a * (y + u))) - Real.exp (-(a * y))) * u / (u ^ 2 + ε ^ 2) : ℝ) : ℂ)‖
        ≤ a * Real.exp (-(a * (y - ρ))) * (2 * ρ) := by
      have hpt_bound : ∀ u ∈ Set.uIoc (-ρ) ρ,
          ‖(((Real.exp (-(a * (y + u))) - Real.exp (-(a * y))) * u / (u ^ 2 + ε ^ 2) : ℝ) : ℂ)‖
            ≤ a * Real.exp (-(a * (y - ρ))) := by
        intro u hu
        have hu' : u ∈ Set.Icc (-ρ) ρ := by
          rw [Set.uIoc_of_le hle] at hu
          exact ⟨le_of_lt hu.1, hu.2⟩
        have hDpos : 0 < u ^ 2 + ε ^ 2 := by nlinarith [sq_nonneg u]
        have hgu := spike_exp_sub_le ha hρ hρy hu'
        have hkey : ‖(((Real.exp (-(a * (y + u))) - Real.exp (-(a * y))) * u
            / (u ^ 2 + ε ^ 2) : ℝ) : ℂ)‖
            = |Real.exp (-(a * (y + u))) - Real.exp (-(a * y))| * |u| / (u ^ 2 + ε ^ 2) := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hDpos]
        rw [hkey]
        calc |Real.exp (-(a * (y + u))) - Real.exp (-(a * y))| * |u| / (u ^ 2 + ε ^ 2)
            ≤ (a * Real.exp (-(a * (y - ρ))) * |u|) * |u| / (u ^ 2 + ε ^ 2) := by
              exact div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_right hgu (abs_nonneg u)) hDpos.le
          _ = a * Real.exp (-(a * (y - ρ))) * (|u| ^ 2 / (u ^ 2 + ε ^ 2)) := by ring
          _ ≤ a * Real.exp (-(a * (y - ρ))) * 1 := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              rw [div_le_one hDpos]
              nlinarith [sq_nonneg ε, sq_abs u]
          _ = a * Real.exp (-(a * (y - ρ))) := by ring
      have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -ρ) (b := ρ)
        (f := fun u : ℝ =>
          (((Real.exp (-(a * (y + u))) - Real.exp (-(a * y))) * u / (u ^ 2 + ε ^ 2) : ℝ) : ℂ))
        (C := a * Real.exp (-(a * (y - ρ)))) hpt_bound
      rw [show ρ - (-ρ) = 2 * ρ by ring, abs_of_pos (by linarith : (0:ℝ) < 2 * ρ)] at h
      exact h
    -- ### bound on the polar part
    have hInt2 : ‖∫ u in (-ρ)..ρ,
        (((Real.exp (-(a * (y + u))) / (u ^ 2 + ε ^ 2)) * ε : ℝ) : ℂ) * Complex.I‖
        ≤ Real.pi := by
      have hcont1 : Continuous (fun u : ℝ => Real.exp (-(a * (y + u))) / (u ^ 2 + ε ^ 2)) := by
        apply Continuous.div
        · fun_prop
        · fun_prop
        · exact hden
      have hcont2 : Continuous (fun u : ℝ => (u ^ 2 + ε ^ 2)⁻¹) := by
        apply Continuous.inv₀
        · fun_prop
        · exact hden
      have h1 := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (a := -ρ) (b := ρ)
        (f := fun u : ℝ => (((Real.exp (-(a * (y + u))) / (u ^ 2 + ε ^ 2)) * ε : ℝ) : ℂ)
          * Complex.I) hle
      have h2 : (∫ u in (-ρ)..ρ,
            ‖(((Real.exp (-(a * (y + u))) / (u ^ 2 + ε ^ 2)) * ε : ℝ) : ℂ) * Complex.I‖)
          = |ε| * ∫ u in (-ρ)..ρ, (Real.exp (-(a * (y + u))) / (u ^ 2 + ε ^ 2)) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro u _
        dsimp only
        have hDpos : 0 < u ^ 2 + ε ^ 2 := by nlinarith [sq_nonneg u]
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
          abs_div, abs_of_pos (Real.exp_pos _), abs_of_pos hDpos]
        ring
      have h3 : (∫ u in (-ρ)..ρ, (Real.exp (-(a * (y + u))) / (u ^ 2 + ε ^ 2)))
          ≤ ∫ u in (-ρ)..ρ, (u ^ 2 + ε ^ 2)⁻¹ := by
        apply intervalIntegral.integral_mono_on hle
          (hcont1.intervalIntegrable _ _) (hcont2.intervalIntegrable _ _)
        intro u hu
        have hgu : Real.exp (-(a * (y + u))) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          nlinarith [hu.1, ha]
        rw [div_eq_mul_inv]
        simpa using mul_le_mul_of_nonneg_right hgu (by positivity)
      calc ‖∫ u in (-ρ)..ρ,
              (((Real.exp (-(a * (y + u))) / (u ^ 2 + ε ^ 2)) * ε : ℝ) : ℂ) * Complex.I‖
          ≤ ∫ u in (-ρ)..ρ,
              ‖(((Real.exp (-(a * (y + u))) / (u ^ 2 + ε ^ 2)) * ε : ℝ) : ℂ) * Complex.I‖ := h1
        _ = |ε| * ∫ u in (-ρ)..ρ, (Real.exp (-(a * (y + u))) / (u ^ 2 + ε ^ 2)) := h2
        _ ≤ |ε| * ∫ u in (-ρ)..ρ, (u ^ 2 + ε ^ 2)⁻¹ :=
              mul_le_mul_of_nonneg_left h3 (abs_nonneg ε)
        _ ≤ |ε| * (Real.pi / |ε|) :=
              mul_le_mul_of_nonneg_left (spike_inv_sq_integral_le hε) (abs_nonneg ε)
        _ = Real.pi := by rw [mul_div_cancel₀ _ (abs_ne_zero.mpr hε)]
    -- ### assembly
    have e1 : (∫ u in (-ρ)..ρ, Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ)))
          * ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹)
        = ∫ u in (-ρ)..ρ, (((Real.exp (-(a * y)) * u / (u ^ 2 + ε ^ 2) : ℝ) : ℂ)
            + (((Real.exp (-(a * (y + u))) - Real.exp (-(a * y))) * u / (u ^ 2 + ε ^ 2) : ℝ) : ℂ)
            - (((Real.exp (-(a * (y + u))) / (u ^ 2 + ε ^ 2)) * ε : ℝ) : ℂ) * Complex.I) := by
      apply intervalIntegral.integral_congr
      intro u _
      exact hpt u
    have e2 : (∫ u in (-ρ)..ρ, (((Real.exp (-(a * y)) * u / (u ^ 2 + ε ^ 2) : ℝ) : ℂ)
            + (((Real.exp (-(a * (y + u))) - Real.exp (-(a * y))) * u / (u ^ 2 + ε ^ 2) : ℝ) : ℂ)
            - ((((Real.exp (-(a * (y + u))) / (u ^ 2 + ε ^ 2)) * ε : ℝ) : ℂ) * Complex.I)))
        = (∫ u in (-ρ)..ρ, ((Real.exp (-(a * y)) * u / (u ^ 2 + ε ^ 2) : ℝ) : ℂ))
          + (∫ u in (-ρ)..ρ,
              (((Real.exp (-(a * (y + u))) - Real.exp (-(a * y))) * u / (u ^ 2 + ε ^ 2) : ℝ) : ℂ))
          - (∫ u in (-ρ)..ρ,
              (((Real.exp (-(a * (y + u))) / (u ^ 2 + ε ^ 2)) * ε : ℝ) : ℂ) * Complex.I) := by
      rw [intervalIntegral.integral_sub (hi0.add hi1) hi2, intervalIntegral.integral_add hi0 hi1]
    have hfinal : ‖(∫ u in (-ρ)..ρ,
              (((Real.exp (-(a * (y + u))) - Real.exp (-(a * y))) * u / (u ^ 2 + ε ^ 2) : ℝ) : ℂ))
            - (∫ u in (-ρ)..ρ,
              (((Real.exp (-(a * (y + u))) / (u ^ 2 + ε ^ 2)) * ε : ℝ) : ℂ) * Complex.I)‖
        ≤ Real.pi + 2 * ρ / (y - ρ) := by
      calc ‖(∫ u in (-ρ)..ρ,
                (((Real.exp (-(a * (y + u))) - Real.exp (-(a * y))) * u / (u ^ 2 + ε ^ 2) : ℝ) : ℂ))
              - (∫ u in (-ρ)..ρ,
                (((Real.exp (-(a * (y + u))) / (u ^ 2 + ε ^ 2)) * ε : ℝ) : ℂ) * Complex.I)‖
          ≤ ‖∫ u in (-ρ)..ρ,
                (((Real.exp (-(a * (y + u))) - Real.exp (-(a * y))) * u / (u ^ 2 + ε ^ 2) : ℝ) : ℂ)‖
            + ‖∫ u in (-ρ)..ρ,
                (((Real.exp (-(a * (y + u))) / (u ^ 2 + ε ^ 2)) * ε : ℝ) : ℂ) * Complex.I‖ :=
            norm_sub_le _ _
        _ ≤ a * Real.exp (-(a * (y - ρ))) * (2 * ρ) + Real.pi := add_le_add hInt1 hInt2
        _ ≤ 2 * ρ / (y - ρ) + Real.pi := by
            have h4 := spike_mul_exp_le_inv ha hρy
            have h5 : a * Real.exp (-(a * (y - ρ))) * (2 * ρ) ≤ (1 / (y - ρ)) * (2 * ρ) :=
              mul_le_mul_of_nonneg_right h4 (by linarith)
            have h6 : (1 / (y - ρ)) * (2 * ρ) = 2 * ρ / (y - ρ) := by ring
            linarith
        _ = Real.pi + 2 * ρ / (y - ρ) := by ring
    rw [e1, e2, hInt0, zero_add]
    exact hfinal

end Work.Asymptotics.HalfFunnel
