import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.Integral

/-- The Euler-type real integral `∫₀^∞ e^{−c·r}·r^{σ−1} dr` converges for
`c > 0`, `σ > 0`. -/
theorem exp_neg_mul_rpow_integrableOn_Ioi {c σ : ℝ} (hc : 0 < c) (hσ : 0 < σ) :
    MeasureTheory.IntegrableOn (fun r : ℝ => Real.exp (-(c * r)) * r ^ (σ - 1))
      (Set.Ioi 0) := by
  -- The integrand of Euler's Γ-integral (with coefficient of decay 1) is integrable on `(0, ∞)`
  -- for `0 < σ`; this is the case `c = 1` of the desired statement.
  have hG : MeasureTheory.IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ (σ - 1))
      (Set.Ioi 0) :=
    Real.GammaIntegral_convergent hσ
  -- Reduce the general decay rate `c > 0` to `c = 1` by the substitution `x ↦ c⁻¹ * x`
  -- (a bijective linear change of variables on the half-line `(0, ∞)`).
  have hcpos : 0 < c⁻¹ := inv_pos.mpr hc
  have hiff :=
    (MeasureTheory.integrableOn_Ioi_comp_mul_left_iff (f := fun r : ℝ => Real.exp (-(c * r)) * r ^ (σ - 1))
      (c := (0 : ℝ)) (a := c⁻¹) hcpos)
  -- The integrand after substitution is a scalar multiple of the `c = 1` integrand:
  -- `exp (-(c · (c⁻¹ · x))) · (c⁻¹ · x) ^ (σ - 1) = (c⁻¹) ^ (σ - 1) · exp (-x) · x ^ (σ - 1)`
  -- for every `x > 0`.
  have hleft : MeasureTheory.IntegrableOn
      (fun x : ℝ => Real.exp (-(c * (c⁻¹ * x))) * (c⁻¹ * x) ^ (σ - 1)) (Set.Ioi 0) := by
    have hk : MeasureTheory.IntegrableOn
        (fun x : ℝ => (c⁻¹) ^ (σ - 1) * (Real.exp (-x) * x ^ (σ - 1))) (Set.Ioi 0) :=
      hG.const_mul ((c⁻¹) ^ (σ - 1))
    refine hk.congr_fun ?_ measurableSet_Ioi
    intro x hx
    have hcx : c * (c⁻¹ * x) = x := by
      field_simp [hc.ne']
    have hx0 : 0 ≤ x := le_of_lt hx
    have hc0 : 0 ≤ c⁻¹ := le_of_lt hcpos
    calc
      (c⁻¹) ^ (σ - 1) * (Real.exp (-x) * x ^ (σ - 1))
          = (c⁻¹ * x) ^ (σ - 1) * Real.exp (-x) := by
            rw [Real.mul_rpow hc0 hx0]
            ring
      _ = (c⁻¹ * x) ^ (σ - 1) * Real.exp (-(c * (c⁻¹ * x))) := by
            rw [hcx]
      _ = Real.exp (-(c * (c⁻¹ * x))) * (c⁻¹ * x) ^ (σ - 1) := by
            ring
  simpa using hiff.1 hleft

end Commons.Analysis.Integral