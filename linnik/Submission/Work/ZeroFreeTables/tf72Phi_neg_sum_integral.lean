import Mathlib
import Submission.Work.ZeroFreeTables.tf72Phi_defs

namespace Work.ZeroFreeTables

theorem tf72Phi_neg_sum_integral (x : ℝ) :
    (∫ s in (0:ℝ)..2, (∑ m ∈ Finset.range 9, (x * s) ^ m / (m.factorial : ℝ)) * tf72Body s)
      = ∑ m ∈ Finset.range 9, x ^ m * tf72M m / (m.factorial : ℝ) := by
  rw [show (∫ s in (0:ℝ)..2, (∑ m ∈ Finset.range 9, (x * s) ^ m / (m.factorial : ℝ)) * tf72Body s)
      = ∫ s in (0:ℝ)..2, ∑ m ∈ Finset.range 9, (x * s) ^ m / (m.factorial : ℝ) * tf72Body s by
    apply intervalIntegral.integral_congr; intro s _
    simp only [Finset.sum_mul]]
  rw [intervalIntegral.integral_finsetSum (f := fun m s => (x * s) ^ m / (m.factorial : ℝ) * tf72Body s)
      (fun m hm => ((by unfold tf72Body; fun_prop : Continuous (fun s : ℝ => (x * s) ^ m / (m.factorial : ℝ) * tf72Body s))).intervalIntegrable 0 2)]
  apply Finset.sum_congr rfl
  intro m hm
  rw [show (∫ s in (0:ℝ)..2, (x * s) ^ m / (m.factorial : ℝ) * tf72Body s)
      = ∫ s in (0:ℝ)..2, (x^m / (m.factorial:ℝ)) * (s^m * tf72Body s) by
    apply intervalIntegral.integral_congr; intro s _
    simp only [mul_pow]; ring]
  rw [intervalIntegral.integral_const_mul, tf72M_eq_integral]
  ring

end Work.ZeroFreeTables
