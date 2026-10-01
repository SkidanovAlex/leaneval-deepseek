import Mathlib
import Submission.Work.LinnikAreas.Density4.SqfreeCoprimeDefs

namespace Work.LinnikAreas.Density4

open Finset

/-- The Möbius function is bounded by `1` in absolute value, as a real number. -/
lemma abs_moebius_cast_le_one (m : ℕ) :
    |(ArithmeticFunction.moebius m : ℝ)| ≤ 1 := by
  have h := ArithmeticFunction.abs_moebius_le_one (n := m)
  have h' : ((|ArithmeticFunction.moebius m| : ℤ) : ℝ) ≤ ((1 : ℤ) : ℝ) := by
    exact_mod_cast h
  rwa [Int.cast_abs, Int.cast_one] at h'

/-- The coprimality restricted Möbius reciprocal sum `moebU r = Σ'_{(m,r)=1} μ(m)/m²` is
bounded in absolute value by `2`: each summand is dominated by `1/m²`, whose full series is
`ζ(2) = π²/6 < 2`. -/
theorem moebU_abs_le (r : ℕ) : |moebU r| ≤ 2 := by
  have hterm : ∀ m : ℕ,
      |(if Nat.Coprime m r then (ArithmeticFunction.moebius m : ℝ) / (m : ℝ) ^ 2 else 0)|
        ≤ (1 : ℝ) / (m : ℝ) ^ 2 := by
    intro m
    by_cases hc : Nat.Coprime m r
    · rw [if_pos hc, abs_div]
      have hb : |(m : ℝ) ^ 2| = (m : ℝ) ^ 2 := by rw [abs_of_nonneg (by positivity)]
      rw [hb]
      refine div_le_div_of_nonneg_right (abs_moebius_cast_le_one m) (by positivity)
    · rw [if_neg hc, abs_zero]
      exact div_nonneg zero_le_one (by positivity)
  -- The series `Σ 1/m² = ζ(2)` is summable.
  have hg : Summable (fun m : ℕ => (1 : ℝ) / (m : ℝ) ^ 2) := hasSum_zeta_two.summable
  -- hence so is the series of absolute values of our summands
  have habs : Summable (fun m : ℕ =>
      |(if Nat.Coprime m r then (ArithmeticFunction.moebius m : ℝ) / (m : ℝ) ^ 2 else 0)|) :=
    Summable.of_nonneg_of_le (fun m => abs_nonneg _) hterm hg
  have hnorm : Summable (fun m : ℕ =>
      ‖(if Nat.Coprime m r then (ArithmeticFunction.moebius m : ℝ) / (m : ℝ) ^ 2 else 0)‖) := by
    simpa only [Real.norm_eq_abs] using habs
  calc |moebU r|
      = |∑' m : ℕ,
          (if Nat.Coprime m r then (ArithmeticFunction.moebius m : ℝ) / (m : ℝ) ^ 2 else 0)| := by
        rw [moebU]
    _ ≤ ∑' m : ℕ,
          ‖(if Nat.Coprime m r then (ArithmeticFunction.moebius m : ℝ) / (m : ℝ) ^ 2 else 0)‖ :=
        norm_tsum_le_tsum_norm hnorm
    _ = ∑' m : ℕ,
          |(if Nat.Coprime m r then (ArithmeticFunction.moebius m : ℝ) / (m : ℝ) ^ 2 else 0)| := by
        simp only [Real.norm_eq_abs]
    _ ≤ ∑' m : ℕ, (1 : ℝ) / (m : ℝ) ^ 2 :=
        Summable.tsum_le_tsum hterm habs hg
    _ = Real.pi ^ 2 / 6 := hasSum_zeta_two.tsum_eq
    _ ≤ 2 := by nlinarith [Real.pi_pos, Real.pi_lt_d2]

end Work.LinnikAreas.Density4
