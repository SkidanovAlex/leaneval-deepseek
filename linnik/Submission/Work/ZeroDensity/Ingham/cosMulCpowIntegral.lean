import Mathlib

namespace Work.ZeroDensity.Ingham

open MeasureTheory

/-- Integration by parts for `v ↦ v^c` against `cos`:

`c ∫₀ᴬ cos v · v^{c-1} dv = cos A · A^c + ∫₀ᴬ sin v · v^c dv`  (for `Re c > 0`).

This is the antiderivative identity `d/dv (cos v · v^c) = -sin v · v^c + c · cos v · v^{c-1}`
integrated over `(0, A]`; the boundary term at `0` vanishes because `Re c > 0`. -/
theorem cosMulCpowIntegral {c : ℂ} (hc : 0 < c.re) {A : ℝ} (hA : 0 < A) :
    c * (∫ v in Set.Ioc 0 A, ((Real.cos v : ℝ) : ℂ) * (v : ℂ) ^ (c - 1)) =
      ((Real.cos A : ℝ) : ℂ) * (A : ℂ) ^ c +
        ∫ v in Set.Ioc 0 A, ((Real.sin v : ℝ) : ℂ) * (v : ℂ) ^ c := by
  have hAle : (0 : ℝ) ≤ A := hA.le
  have hcne : c ≠ 0 := by
    intro h; rw [h] at hc; exact lt_irrefl _ hc
  have hcre : -1 < (c - 1).re := by
    have : (c - 1).re = c.re - 1 := by simp
    linarith
  -- Rewrite the two `Ioc` integrals as interval integrals.
  rw [← intervalIntegral.integral_of_le hAle, ← intervalIntegral.integral_of_le hAle]
  -- Integration by parts for `u = cos`, `v = (·)^c`.
  have hcont_u : ContinuousOn (fun v : ℝ => ((Real.cos v : ℝ) : ℂ)) (Set.uIcc (0 : ℝ) A) := by
    rw [Set.uIcc_of_le hAle]
    exact (Complex.continuous_ofReal.comp Real.continuous_cos).continuousOn
  have hcont_v : ContinuousOn (fun v : ℝ => (v : ℂ) ^ c) (Set.uIcc (0 : ℝ) A) := by
    rw [Set.uIcc_of_le hAle]
    exact (Complex.continuous_ofReal_cpow_const hc).continuousOn
  have hder_u : ∀ x ∈ Set.Ioo (min (0 : ℝ) A) (max (0 : ℝ) A),
      HasDerivAt (fun v : ℝ => ((Real.cos v : ℝ) : ℂ)) (-(((Real.sin x : ℝ)) : ℂ)) x := by
    intro x hx
    rw [min_eq_left hAle, max_eq_right hAle] at hx
    simpa using (Real.hasDerivAt_cos x).ofReal_comp
  have hder_v : ∀ x ∈ Set.Ioo (min (0 : ℝ) A) (max (0 : ℝ) A),
      HasDerivAt (fun v : ℝ => (v : ℂ) ^ c) (c * (x : ℂ) ^ (c - 1)) x := by
    intro x hx
    rw [min_eq_left hAle, max_eq_right hAle] at hx
    exact hasDerivAt_ofReal_cpow_const hx.1.ne' hcne
  have hint_u : IntervalIntegrable (fun v : ℝ => -(((Real.sin v : ℝ)) : ℂ)) volume (0 : ℝ) A :=
    (((Complex.continuous_ofReal.comp Real.continuous_sin).neg).intervalIntegrable 0 A)
  have hint_v : IntervalIntegrable (fun v : ℝ => c * (v : ℂ) ^ (c - 1)) volume (0 : ℝ) A :=
    (intervalIntegral.intervalIntegrable_cpow' (a := (0 : ℝ)) (b := A) hcre).const_mul c
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := (0 : ℝ)) (b := A)
    (u := fun v : ℝ => ((Real.cos v : ℝ) : ℂ))
    (u' := fun v : ℝ => -(((Real.sin v : ℝ)) : ℂ))
    (v := fun v : ℝ => (v : ℂ) ^ c)
    (v' := fun v : ℝ => c * (v : ℂ) ^ (c - 1))
    hcont_u hcont_v hder_u hder_v hint_u hint_v
  -- Rewrite the two integrals appearing in the identity.
  have hL : (∫ x in (0 : ℝ)..A, ((Real.cos x : ℝ) : ℂ) * (c * (x : ℂ) ^ (c - 1)))
      = c * ∫ x in (0 : ℝ)..A, ((Real.cos x : ℝ) : ℂ) * (x : ℂ) ^ (c - 1) := by
    rw [← intervalIntegral.integral_const_mul c
      (fun x : ℝ => ((Real.cos x : ℝ) : ℂ) * (x : ℂ) ^ (c - 1))]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  have hR : (∫ x in (0 : ℝ)..A, (-(((Real.sin x : ℝ)) : ℂ)) * (x : ℂ) ^ c)
      = -∫ x in (0 : ℝ)..A, ((Real.sin x : ℝ) : ℂ) * (x : ℂ) ^ c := by
    rw [← intervalIntegral.integral_neg
      (f := fun x : ℝ => ((Real.sin x : ℝ) : ℂ) * (x : ℂ) ^ c)]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  rw [hL, hR] at hIBP
  have h0 : ((0 : ℝ) : ℂ) ^ c = 0 := by rw [Complex.ofReal_zero, Complex.zero_cpow hcne]
  rw [h0, mul_zero, sub_zero, sub_neg_eq_add] at hIBP
  exact hIBP

end Work.ZeroDensity.Ingham
