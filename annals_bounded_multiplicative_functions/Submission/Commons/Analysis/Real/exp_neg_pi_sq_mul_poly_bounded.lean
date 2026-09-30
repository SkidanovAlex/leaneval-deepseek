import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.Real

theorem exp_neg_pi_sq_mul_poly_bounded (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      Real.exp (-Real.pi * t ^ 2) * (1 + t) ^ (100 * m) ≤ C := by
  let N : ℕ := 100 * m
  let n : ℝ := N
  let T : ℝ := max 1 (n / Real.pi)
  let K : ℝ := (1 + T) ^ N
  refine ⟨max K 1, ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_right K 1)
  · intro t ht
    change Real.exp (-Real.pi * t ^ 2) * (1 + t) ^ N ≤ max K 1
    have ht0 : 0 ≤ 1 + t := by nlinarith
    have hx_pos : 0 < 1 + t := by nlinarith
    by_cases hle : t ≤ T
    · -- regime t ≤ T
      have hexp_le : Real.exp (-Real.pi * t ^ 2) ≤ 1 := by
        have hneg : -Real.pi * t ^ 2 ≤ 0 := by nlinarith [Real.pi_pos.le, sq_nonneg t]
        simpa using Real.exp_le_exp.mpr hneg
      have h1le : 1 + t ≤ 1 + T := by nlinarith
      have hpowK : (1 + t) ^ N ≤ K := by
        dsimp [K]
        exact pow_le_pow_left₀ ht0 h1le N
      have hmain : Real.exp (-Real.pi * t ^ 2) * (1 + t) ^ N ≤ K := by
        simpa using (mul_le_mul hexp_le hpowK (pow_nonneg ht0 N) (by norm_num : (0 : ℝ) ≤ 1))
      exact le_trans hmain (le_max_left K 1)
    · -- regime t ≥ T
      have hTlt : T < t := lt_of_not_ge hle
      have hTle : T ≤ t := le_of_lt hTlt
      have hdiv : n / Real.pi ≤ T := le_max_right 1 (n / Real.pi)
      have hdiv' : n / Real.pi ≤ t := le_trans hdiv hTle
      have h_n : n ≤ Real.pi * t := by
        have h1 : n ≤ t * Real.pi := (div_le_iff₀ Real.pi_pos).mp hdiv'
        simpa [mul_comm] using h1
      have hlog_le : Real.log (1 + t) ≤ t := by
        have h := Real.log_le_sub_one_of_pos hx_pos
        nlinarith
      have hN0 : 0 ≤ n := by dsimp [n, N]; exact_mod_cast Nat.zero_le (100 * m)
      have h1 : n * Real.log (1 + t) ≤ n * t :=
        mul_le_mul_of_nonneg_left hlog_le hN0
      have h2 : n * t ≤ Real.pi * t ^ 2 := by
        calc
          n * t ≤ (Real.pi * t) * t := mul_le_mul_of_nonneg_right h_n ht
          _ = Real.pi * t ^ 2 := by ring
      have hbound : n * Real.log (1 + t) ≤ Real.pi * t ^ 2 := le_trans h1 h2
      have hpow_le : (1 + t) ^ N ≤ Real.exp (Real.pi * t ^ 2) := by
        have h_eq : (1 + t) ^ N = Real.exp (n * Real.log (1 + t)) := by
          calc
            (1 + t) ^ N = Real.exp (Real.log ((1 + t) ^ N)) :=
              (Real.exp_log (pow_pos hx_pos N)).symm
            _ = Real.exp (n * Real.log (1 + t)) := by
              dsimp [n]
              rw [Real.log_pow]
        rw [h_eq]
        exact Real.exp_le_exp.mpr hbound
      have hprod : Real.exp (-Real.pi * t ^ 2) * (1 + t) ^ N ≤ 1 := by
        calc
          Real.exp (-Real.pi * t ^ 2) * (1 + t) ^ N
              ≤ Real.exp (-Real.pi * t ^ 2) * Real.exp (Real.pi * t ^ 2) := by
                exact mul_le_mul_of_nonneg_left hpow_le (Real.exp_nonneg (-Real.pi * t ^ 2))
          _ = 1 := by
            rw [← Real.exp_add]
            have hsum : -Real.pi * t ^ 2 + Real.pi * t ^ 2 = 0 := by ring
            rw [hsum, Real.exp_zero]
      exact le_trans hprod (le_max_right K 1)

end Commons.Analysis.Real