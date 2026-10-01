import Mathlib

namespace Work.LinnikAreas.Density4

/-- Lower bound `Γ(σ) ≥ 1/(3σ)` for `0 < σ ≤ 1`, obtained from the recurrence
`Γ(s+1) = s Γ(s)` together with the monotonicity of `Γ` on `[2,∞)` (`Γ(σ+1) ≥ 1/3`). -/
lemma Gamma_ge_inv_three_mul (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    (1:ℝ)/3 ≤ σ * Real.Gamma σ := by
  have hσ1pos : (0:ℝ) < σ + 1 := by linarith
  have hσ2pos : (0:ℝ) < σ + 2 := by linarith
  have hG1pos : 0 < Real.Gamma (σ+1) := Real.Gamma_pos_of_pos hσ1pos
  -- `Γ(σ+3) = (σ+1)(σ+2) Γ(σ+1)`
  have hG3 : Real.Gamma (σ+3) = (σ+1)*(σ+2)*Real.Gamma (σ+1) := by
    have e1 : Real.Gamma (σ+2) = (σ+1)*Real.Gamma (σ+1) := by
      have h := Real.Gamma_add_one (s := σ+1) (by linarith)
      rwa [show σ+1+1 = σ+2 by ring] at h
    have e2 : Real.Gamma (σ+3) = (σ+2)*Real.Gamma (σ+2) := by
      have h := Real.Gamma_add_one (s := σ+2) (by linarith)
      rwa [show σ+2+1 = σ+3 by ring] at h
    rw [e2, e1]; ring
  -- `Γ(σ+3) ≥ Γ 3 = 2` by monotonicity on `[2,∞)`
  have hG3eq : Real.Gamma 3 = 2 := by
    norm_num [Real.Gamma_nat_eq_factorial]
  have hGge : Real.Gamma 3 ≤ Real.Gamma (σ+3) :=
    Real.Gamma_strictMonoOn_Ici.monotoneOn
      (by norm_num [Set.mem_Ici] : (3:ℝ) ∈ Set.Ici (2:ℝ))
      (by simp only [Set.mem_Ici]; linarith : (σ+3) ∈ Set.Ici (2:ℝ)) (by linarith)
  have hprod_ge : (2:ℝ) ≤ (σ+1)*(σ+2)*Real.Gamma (σ+1) := by
    rw [← hG3]; linarith
  have hfactor_le : (σ+1)*(σ+2) ≤ 6 := by nlinarith [hσ, hσ1]
  have h6 : (2:ℝ) ≤ 6 * Real.Gamma (σ+1) := by
    have h := mul_le_mul_of_nonneg_right hfactor_le hG1pos.le
    linarith
  have hG1ge : (1:ℝ)/3 ≤ Real.Gamma (σ+1) := by linarith
  have h := Real.Gamma_add_one (s := σ) (ne_of_gt hσ)
  linarith [hG1ge, h]

theorem thetaDiag_kappa_lower (σ A M : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hA : 1 ≤ A)
    (hM : 0 < M) (hAM : Real.exp M ≤ A) :
    0.184 * Real.exp (σ*M)/(σ*M*M) ≤ Real.Gamma σ * A^σ / M^2 := by
  have _hApos : (0:ℝ) < A := lt_of_lt_of_le zero_lt_one hA
  -- `exp (σ M) ≤ A^σ`
  have hexp_le : Real.exp (σ*M) ≤ A^σ := by
    have h1 : (Real.exp M)^σ ≤ A^σ := Real.rpow_le_rpow (Real.exp_pos M).le hAM hσ.le
    have h2 : (Real.exp M)^σ = Real.exp (M*σ) := by rw [← Real.exp_mul]
    rw [h2, mul_comm M σ] at h1
    exact h1
  have hGamma_lb : (1:ℝ)/3 ≤ σ * Real.Gamma σ := Gamma_ge_inv_three_mul σ hσ hσ1
  have hden : σ*M*M = σ*M^2 := by ring
  rw [hden]
  have hepos : 0 ≤ Real.exp (σ*M) := (Real.exp_pos _).le
  have hstep1 : 0.184 * Real.exp (σ*M)/(σ*M^2) ≤ (1/3) * Real.exp (σ*M)/(σ*M^2) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [hepos]
  have hstep2 : (1/3) * Real.exp (σ*M)/(σ*M^2) ≤ Real.Gamma σ * Real.exp (σ*M)/M^2 := by
    have hnum : (1/3)*Real.exp (σ*M) ≤ (σ*Real.Gamma σ)*Real.exp (σ*M) :=
      mul_le_mul_of_nonneg_right hGamma_lb hepos
    have h := div_le_div_of_nonneg_right hnum (by positivity : (0:ℝ) ≤ σ*M^2)
    have heq : (σ*Real.Gamma σ)*Real.exp (σ*M)/(σ*M^2) = Real.Gamma σ * Real.exp (σ*M)/M^2 := by
      field_simp
    rwa [heq] at h
  have hstep3 : Real.Gamma σ * Real.exp (σ*M)/M^2 ≤ Real.Gamma σ * A^σ/M^2 := by
    apply div_le_div_of_nonneg_right _ (by positivity : (0:ℝ) ≤ M^2)
    exact mul_le_mul_of_nonneg_left hexp_le (Real.Gamma_pos_of_pos hσ).le
  linarith [hstep1, hstep2, hstep3]

end Work.LinnikAreas.Density4
