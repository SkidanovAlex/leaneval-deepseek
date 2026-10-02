import Mathlib
import Submission.Work.LinnikAreas.Density4.vonMangoldt_sq_sum_bound
import Submission.Commons.NumberTheory.Chebyshev.theta_abs_sub_id_le

namespace Work.LinnikAreas.Density4

open Filter

/-- Chebyshev's `θ` is `N − O(N/log N)` from below, uniformly in `N ≥ 2`. -/
theorem theta_lower_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, 2 ≤ N →
      (N : ℝ) - K * (N : ℝ) / Real.log (N : ℝ) ≤ Chebyshev.theta (N : ℝ) := by
  obtain ⟨x₀, _hx₀1, hθ⟩ := Commons.NumberTheory.Chebyshev.theta_abs_sub_id_le 2 (by norm_num)
  set M : ℕ := max 2 ⌈x₀⌉₊ with hMdef
  have hM2 : 2 ≤ M := le_max_left _ _
  have hx₀M : x₀ ≤ (M : ℝ) := by
    have h1 : x₀ ≤ (⌈x₀⌉₊ : ℝ) := Nat.le_ceil x₀
    have h2 : ((⌈x₀⌉₊ : ℕ) : ℝ) ≤ (M : ℝ) := by
      rw [hMdef]; exact_mod_cast le_max_right 2 ⌈x₀⌉₊
    linarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  refine ⟨max (1 / Real.log 2) (Real.log (M : ℝ)), ?_, ?_⟩
  · have hpos : 0 < 1 / Real.log 2 := by positivity
    exact lt_of_lt_of_le hpos (le_max_left _ _)
  · intro N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
    have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hlogn : 0 < Real.log (N : ℝ) := Real.log_pos hN1
    have hlognnn : 0 ≤ Real.log (N : ℝ) := le_of_lt hlogn
    have hlogn2 : Real.log 2 ≤ Real.log (N : ℝ) := Real.log_le_log (by norm_num) hN2
    have hKey : ((N : ℝ) - Chebyshev.theta (N : ℝ)) * Real.log (N : ℝ)
        ≤ max (1 / Real.log 2) (Real.log (M : ℝ)) * (N : ℝ) := by
      by_cases hcase : M ≤ N
      · -- large `N`: use the PNT error term
        have hxn : x₀ ≤ (N : ℝ) := le_trans hx₀M (by exact_mod_cast hcase)
        have hbd := hθ (N : ℝ) hxn
        have hle : (N : ℝ) - Chebyshev.theta (N : ℝ)
            ≤ (N : ℝ) / (Real.log (N : ℝ)) ^ (2 : ℝ) := by
          have h := (abs_le.mp hbd).1
          linarith
        have hmul := mul_le_mul_of_nonneg_right hle hlognnn
        have hsimp : (N : ℝ) / (Real.log (N : ℝ)) ^ (2 : ℝ) * Real.log (N : ℝ)
            = (N : ℝ) / Real.log (N : ℝ) := by
          rw [Real.rpow_two]
          field_simp
        have hinv : 1 / Real.log (N : ℝ) ≤ 1 / Real.log 2 :=
          one_div_le_one_div_of_le hlog2pos hlogn2
        have hKge : 1 / Real.log 2 ≤ max (1 / Real.log 2) (Real.log (M : ℝ)) :=
          le_max_left _ _
        have hfinal : (N : ℝ) / Real.log (N : ℝ)
            ≤ max (1 / Real.log 2) (Real.log (M : ℝ)) * (N : ℝ) := by
          rw [div_eq_mul_one_div]
          calc (N : ℝ) * (1 / Real.log (N : ℝ))
              ≤ (N : ℝ) * (1 / Real.log 2) :=
                mul_le_mul_of_nonneg_left hinv (le_of_lt hNpos)
            _ ≤ (N : ℝ) * max (1 / Real.log 2) (Real.log (M : ℝ)) :=
                mul_le_mul_of_nonneg_left hKge (le_of_lt hNpos)
            _ = max (1 / Real.log 2) (Real.log (M : ℝ)) * (N : ℝ) := by ring
        calc ((N : ℝ) - Chebyshev.theta (N : ℝ)) * Real.log (N : ℝ)
            ≤ (N : ℝ) / (Real.log (N : ℝ)) ^ (2 : ℝ) * Real.log (N : ℝ) := hmul
          _ = (N : ℝ) / Real.log (N : ℝ) := hsimp
          _ ≤ max (1 / Real.log 2) (Real.log (M : ℝ)) * (N : ℝ) := hfinal
      · -- small `N`: crudely `N − θ N ≤ N`
        have hNM : N < M := not_le.mp hcase
        have hle : (N : ℝ) - Chebyshev.theta (N : ℝ) ≤ (N : ℝ) := by
          have := Chebyshev.theta_nonneg (N : ℝ); linarith
        have hmul := mul_le_mul_of_nonneg_right hle hlognnn
        have hlogNM : Real.log (N : ℝ) ≤ Real.log (M : ℝ) :=
          Real.log_le_log hNpos (by exact_mod_cast le_of_lt hNM)
        have hKgeM : Real.log (M : ℝ) ≤ max (1 / Real.log 2) (Real.log (M : ℝ)) :=
          le_max_right _ _
        calc ((N : ℝ) - Chebyshev.theta (N : ℝ)) * Real.log (N : ℝ)
            ≤ (N : ℝ) * Real.log (N : ℝ) := hmul
          _ ≤ (N : ℝ) * max (1 / Real.log 2) (Real.log (M : ℝ)) :=
              mul_le_mul_of_nonneg_left (le_trans hlogNM hKgeM) (le_of_lt hNpos)
          _ = max (1 / Real.log 2) (Real.log (M : ℝ)) * (N : ℝ) := by ring
    have hmain : (N : ℝ) - Chebyshev.theta (N : ℝ)
        ≤ max (1 / Real.log 2) (Real.log (M : ℝ)) * (N : ℝ) / Real.log (N : ℝ) := by
      rw [le_div_iff₀ hlogn]
      exact hKey
    linarith

end Work.LinnikAreas.Density4
