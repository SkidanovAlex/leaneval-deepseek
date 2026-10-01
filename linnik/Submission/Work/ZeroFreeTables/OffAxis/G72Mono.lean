import Mathlib

namespace Work.ZeroFreeTables.OffAxis

/-- Derivative of the function `x ↦ 4 * exp(2x) * σ² / (x² + σ²)³`. -/
lemma deriv_G72 (x σ : ℝ) (hσ : 0 < σ) :
    deriv (fun y : ℝ => 4 * Real.exp (2*y) * σ^2 / (y^2 + σ^2)^3) x
      = 8*σ^2*Real.exp (2*x)*(x^2-3*x+σ^2)/(x^2+σ^2)^4 := by
  have hc : DifferentiableAt ℝ (fun y : ℝ => 4 * Real.exp (2*y) * σ^2) x := by fun_prop
  have hd : DifferentiableAt ℝ (fun y : ℝ => (y^2 + σ^2)^3) x := by fun_prop
  have hpos : (0:ℝ) < x^2 + σ^2 := by
    have h2 : (0:ℝ) < σ^2 := pow_pos hσ 2
    nlinarith [sq_nonneg x]
  have hx : (x^2 + σ^2)^3 ≠ 0 := ne_of_gt (pow_pos hpos 3)
  have hx4 : (x^2 + σ^2)^4 ≠ 0 := ne_of_gt (pow_pos hpos 4)
  have hx6 : ((x^2 + σ^2)^3)^2 ≠ 0 := pow_ne_zero 2 hx
  have hde : deriv (fun y : ℝ => Real.exp (2*y)) x = 2 * Real.exp (2*x) := by
    rw [deriv_exp (show DifferentiableAt ℝ (fun y:ℝ => 2*y) x by fun_prop)]
    rw [deriv_const_mul_id]
    ring
  have hN : deriv (fun y : ℝ => 4 * Real.exp (2*y) * σ^2) x = 8*Real.exp (2*x)*σ^2 := by
    rw [deriv_mul_const (show DifferentiableAt ℝ (fun y : ℝ => 4 * Real.exp (2*y)) x by fun_prop) (σ^2)]
    rw [deriv_const_mul (4:ℝ) (show DifferentiableAt ℝ (fun y : ℝ => Real.exp (2*y)) x by fun_prop)]
    rw [hde]; ring
  have hD : deriv (fun y : ℝ => (y^2 + σ^2)^3) x = 6*x*(x^2+σ^2)^2 := by
    simp; ring
  rw [deriv_fun_div hc hd hx, hN, hD]
  rw [div_eq_div_iff hx6 hx4]
  ring

theorem G72Mono (s σ : ℝ) (hs : (3:ℝ)/4 ≤ s) (hs1 : s ≤ 1) (hσ : (36:ℝ)/10 ≤ σ) :
    4 * Real.exp (2*s) * σ^2 / (s^2 + σ^2)^3
      ≤ 4 * Real.exp (2:ℝ) * σ^2 / (1 + σ^2)^3 := by
  have hσpos : (0:ℝ) < σ := by linarith
  have hmono : MonotoneOn (fun x : ℝ => 4 * Real.exp (2*x) * σ^2 / (x^2 + σ^2)^3)
      (Set.Icc ((3:ℝ)/4) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · apply Continuous.continuousOn
      apply Continuous.div
      · fun_prop
      · fun_prop
      · intro x
        have h2 : (0:ℝ) < σ^2 := pow_pos hσpos 2
        have h3 : (0:ℝ) < x^2 + σ^2 := by nlinarith [sq_nonneg x]
        exact ne_of_gt (pow_pos h3 3)
    · apply Differentiable.differentiableOn
      apply Differentiable.div
      · fun_prop
      · fun_prop
      · intro x
        have h2 : (0:ℝ) < σ^2 := pow_pos hσpos 2
        have h3 : (0:ℝ) < x^2 + σ^2 := by nlinarith [sq_nonneg x]
        exact ne_of_gt (pow_pos h3 3)
    · intro x hx
      rw [interior_Icc] at hx
      have hx1 : x ≤ 1 := le_of_lt hx.2
      rw [deriv_G72 x σ hσpos]
      have hsig2 : (2:ℝ) ≤ σ^2 := by nlinarith [hσ]
      have hx12 : 0 ≤ (x-1)*(x-2) := mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
      have hfac : 0 ≤ x^2 - 3*x + σ^2 := by nlinarith [hx12, hsig2]
      have hnum1 : 0 ≤ 8 * σ^2 * Real.exp (2*x) := by positivity
      have hden : (0:ℝ) ≤ (x^2 + σ^2)^4 := by positivity
      exact div_nonneg (mul_nonneg hnum1 hfac) hden
  have h1 : (1:ℝ) ∈ Set.Icc ((3:ℝ)/4) 1 := by norm_num
  have hs' : s ∈ Set.Icc ((3:ℝ)/4) 1 := ⟨hs, hs1⟩
  have hres := hmono hs' h1 hs1
  simpa using hres

end Work.ZeroFreeTables.OffAxis
