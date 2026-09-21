import Mathlib
import Submission.Work.OddVolterra.Defs

namespace Work.OddVolterra.Existence

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

/-- Pull a constant out of the `τ`-integral `∫_0^1 c / √(τ(1-τ)) dτ`. -/
lemma integral_inv_sqrt_diag (c : ℝ) :
    (∫ τ in (0 : ℝ)..1, c / Real.sqrt (τ * (1 - τ))) =
      c * ∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ := by
  have h : (fun τ : ℝ => c / Real.sqrt (τ * (1 - τ)))
      = fun τ : ℝ => c * (Real.sqrt (τ * (1 - τ)))⁻¹ := by
    funext τ
    rw [div_eq_mul_inv]
  rw [h, intervalIntegral.integral_const_mul]

/-- At `σ = s` the Abel-averaged kernel `G₂` loses its `τ`-dependence inside
`Kvec`, so the `τ`-integral collapses to the constant
`∫_0^1 (√(τ(1-τ)))⁻¹ dτ` times the kernel value. -/
lemma G2_self (n : ℕ) (h : ℝ → ℝ) (s : ℝ) (x y x' y' : ℝ) :
    Work.OddVolterra.G2 n h s s x y x' y' =
      fun i : Fin 2 =>
        (Work.OddVolterra.Kvec n h s s x y x' y') i *
          ∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ := by
  funext i
  simp only [Work.OddVolterra.G2]
  simp only [show ∀ τ : ℝ, s + τ * (s - s) = s from fun τ => by ring]
  exact integral_inv_sqrt_diag _

lemma Godd_zero_diag (n : ℕ) (s : ℝ) (z : Work.OddVolterra.St) :
    Work.OddVolterra.Godd n 0 s z =
      ![z 0, z 1,
        (∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹)
          * (Work.OddVolterra.K1 n (fun _ : ℝ => 0) s s (-(z 0)) * z 2
            + Work.OddVolterra.K1 n (fun _ : ℝ => 0) s s (z 1) * z 3),
        (∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹)
          * (Work.OddVolterra.K2 n (fun _ : ℝ => 0) s s (-(z 0)) * z 2
            + Work.OddVolterra.K2 n (fun _ : ℝ => 0) s s (z 1) * z 3)] := by
  rw [show (0 : ℝ → ℝ) = fun _ : ℝ => 0 from rfl]
  funext i
  fin_cases i <;>
    simp [Work.OddVolterra.Godd, Work.OddVolterra.G2, Work.OddVolterra.Kvec,
      integral_inv_sqrt_diag]
  all_goals ring

end Work.OddVolterra.Existence
