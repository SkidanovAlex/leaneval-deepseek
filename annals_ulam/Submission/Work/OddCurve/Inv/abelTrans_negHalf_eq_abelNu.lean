import Mathlib
import Submission.Work.OddCurve.Inv.Defs
import Submission.Work.OddRadon.Abel

/-!
# `abelTrans (-1/2)` is `abelNu` in the `ν = c²` variable

The classical Abel transform at exponent `α = -1/2` is

  `abelTrans (-1/2) γ c = ∫_0^c γ s (c² - s²)^{-1/2} ds`,

and the substitution `τ = s²` converts it into the unnormalized fractional integral
`abelNu` of the reduced profile `σ ↦ γ(√σ)/√σ` at `ν = c²`:

  `abelTrans (-1/2) γ c = (1/2) · ∫_0^{c²} (√(c²-τ))⁻¹ γ(√τ)/√τ dτ`
                        `= (1/2) · abelNu (σ ↦ γ(√σ)/√σ) (c^2)`.

The change of variables is the interval-integral substitution `τ = x²` on `[0, c]`
(`intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg`, valid since `x ↦ 2x ≥ 0` there);
the point `x = 0` is invisible to the (left-open) interval integral, and for `x > 0` we have
`√(x²) = x`.
-/

namespace Work.OddCurve.Inv

open MeasureTheory Set Filter
open scoped Topology Interval

noncomputable section

theorem abelTrans_negHalf_eq_abelNu (γ : ℝ → ℝ) :
    ∀ c : ℝ, 0 < c →
      Work.OddRadon.abelTrans (-(1/2)) γ c =
        (1/2) * Work.OddCurve.Inv.abelNu (fun σ : ℝ => γ (Real.sqrt σ) / Real.sqrt σ) (c^2) := by
  intro c hc
  -- the reduced profile, i.e. the integrand of `abelNu`
  set G : ℝ → ℝ := fun u => (Real.sqrt (c^2 - u))⁻¹ * (γ (Real.sqrt u) / Real.sqrt u) with hGdef
  -- change of variables `τ = x²` on `[0, c]`
  have hsub : (∫ x in (0:ℝ)..c, G (x^2) * (2*x)) = ∫ u in (0:ℝ)..c^2, G u := by
    have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg (a := (0:ℝ)) (b := c)
      (f := fun x : ℝ => x^2) (f' := fun x : ℝ => 2*x) (g := G)
      (by fun_prop)
      (by intro x _; simpa using (hasDerivAt_pow 2 x))
      (by
        intro x hx
        have hx0 : 0 < x := by
          have hmem : x ∈ Ioo (min (0:ℝ) c) (max (0:ℝ) c) := hx
          simp only [min_eq_left hc.le, max_eq_right hc.le, mem_Ioo] at hmem
          exact hmem.1
        linarith)
    simpa using h
  calc Work.OddRadon.abelTrans (-(1/2)) γ c
      = ∫ s in (0:ℝ)..c, γ s * (c^2 - s^2) ^ (-(1/2:ℝ)) := rfl
    _ = (1/2) * ∫ u in (0:ℝ)..c^2, G u := by
        rw [← hsub, ← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr_ae
        filter_upwards with x hx
        have hx0 : 0 < x := by
          rw [Set.uIoc_of_le hc.le, Set.mem_Ioc] at hx
          exact hx.1
        have hxc : x ≤ c := by
          rw [Set.uIoc_of_le hc.le, Set.mem_Ioc] at hx
          exact hx.2
        have hsq : Real.sqrt (x^2) = x := by rw [Real.sqrt_sq_eq_abs, abs_of_pos hx0]
        have hc2 : 0 ≤ c^2 - x^2 := by nlinarith
        have hsl : (c^2 - x^2) ^ (-(1/2:ℝ)) = (Real.sqrt (c^2 - x^2))⁻¹ := by
          rw [Real.rpow_neg hc2 (1/2), ← Real.sqrt_eq_rpow]
        simp only [hGdef]
        rw [hsq, hsl]
        field_simp
    _ = (1/2) * Work.OddCurve.Inv.abelNu (fun σ : ℝ => γ (Real.sqrt σ) / Real.sqrt σ) (c^2) := by
        simp only [Work.OddCurve.Inv.abelNu, hGdef]

end

end Work.OddCurve.Inv
