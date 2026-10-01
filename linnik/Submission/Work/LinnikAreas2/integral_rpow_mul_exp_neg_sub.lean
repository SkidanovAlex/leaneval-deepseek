import Mathlib

namespace Work.LinnikAreas2

open MeasureTheory

/-- The integral of `t ^ (σ - 1) * exp (-(t / A))` over `(0, ∞)` equals `Γ σ * A ^ σ`:
the substitution `u = t / A` of the Gamma integral. -/
private lemma integral_rpow_mul_exp_neg_div (σ A : ℝ) (hσ : 0 < σ) (hA : 0 < A) :
    (∫ t in Set.Ioi (0 : ℝ), t ^ (σ - 1) * Real.exp (-(t / A)))
      = Real.Gamma σ * A ^ σ := by
  have hcongr : (∫ t in Set.Ioi (0 : ℝ), t ^ (σ - 1) * Real.exp (-(t / A)))
      = ∫ t in Set.Ioi (0 : ℝ), t ^ (σ - 1) * Real.exp (-((1 / A) * t)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    congr 2
    ring
  rw [hcongr, Real.integral_rpow_mul_exp_neg_mul_Ioi hσ (by positivity)]
  rw [one_div_one_div]
  ring

theorem integral_rpow_mul_exp_neg_sub (σ A B : ℝ) (hσ : 0 < σ) (hA : 0 < A) (hB : 0 < B) :
    (∫ t in Set.Ioi (0 : ℝ), t ^ (σ - 1) * (Real.exp (-(t / A)) - Real.exp (-(t / B))))
      = Real.Gamma σ * (A ^ σ - B ^ σ) := by
  have hfi : IntegrableOn (fun t : ℝ => t ^ (σ - 1) * Real.exp (-(t / A))) (Set.Ioi 0) volume := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := σ - 1) (b := 1 / A)
      (by linarith) one_pos (by positivity)
    simpa [Real.rpow_one, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, neg_mul] using h
  have hgi : IntegrableOn (fun t : ℝ => t ^ (σ - 1) * Real.exp (-(t / B))) (Set.Ioi 0) volume := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := σ - 1) (b := 1 / B)
      (by linarith) one_pos (by positivity)
    simpa [Real.rpow_one, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, neg_mul] using h
  have hsplit : (∫ t in Set.Ioi (0 : ℝ), t ^ (σ - 1) * (Real.exp (-(t / A)) - Real.exp (-(t / B))))
      = (∫ t in Set.Ioi (0 : ℝ), t ^ (σ - 1) * Real.exp (-(t / A)))
        - (∫ t in Set.Ioi (0 : ℝ), t ^ (σ - 1) * Real.exp (-(t / B))) := by
    rw [← integral_sub hfi hgi]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    ring
  rw [hsplit, integral_rpow_mul_exp_neg_div σ A hσ hA, integral_rpow_mul_exp_neg_div σ B hσ hB]
  ring

end Work.LinnikAreas2
