import Mathlib
import Submission.Work.BMF.liouville.vk_large_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.liouville

noncomputable section

/-- Properties of `M = ⌈N^{2/5}⌉` and `μ = log M / log N` for `log N ≥ 10`. -/
theorem vk_large_M_bounds (N : ℝ) (hN : 2 ≤ N) (hlogN : 10 ≤ Real.log N) :
    1 ≤ dM N ∧ ((dM N : ℝ)) ^ 2 ≤ N ∧ 2/5 ≤ dMu N ∧ 2 * dMu N ≤ 17/20 := by
  have hNpos : 0 < N := by linarith
  have hlogNpos : 0 < Real.log N := by linarith
  -- `N ≥ exp 10`, hence `N^(2/5) ≥ exp 4 ≥ 16` and `N^(1/5) ≥ exp 2 ≥ 4`.
  have hNexp : Real.exp 10 ≤ N := by
    rw [← Real.exp_log hNpos]
    exact Real.exp_le_exp.mpr hlogN
  have hXge16 : (16:ℝ) ≤ N ^ ((2:ℝ)/5) := by
    have h1 : Real.exp 10 ^ ((2:ℝ)/5) ≤ N ^ ((2:ℝ)/5) :=
      Real.rpow_le_rpow (Real.exp_pos 10).le hNexp (by norm_num)
    have h2 : Real.exp 10 ^ ((2:ℝ)/5) = Real.exp 4 := by
      rw [Real.rpow_def_of_pos (Real.exp_pos 10), Real.log_exp]
      norm_num
    have h3 : (16:ℝ) ≤ Real.exp 4 := by
      have h1e : (2:ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp 1; linarith
      have h4 : Real.exp 4 = (Real.exp 1)^4 := by
        rw [← Real.exp_nat_mul 1 4]; norm_num
      rw [h4]
      calc (16:ℝ) = (2:ℝ)^4 := by norm_num
        _ ≤ (Real.exp 1)^4 := pow_le_pow_left₀ (by norm_num) h1e 4
    linarith
  have hXpos : 0 < N ^ ((2:ℝ)/5) := Real.rpow_pos_of_pos hNpos _
  -- `⌈x⌉₊ < x + 1` and `x ≤ ⌈x⌉₊`
  have hceil_lt : (dM N : ℝ) < N^((2:ℝ)/5) + 1 :=
    Nat.ceil_lt_add_one (le_of_lt hXpos)
  have hdMpos : (0:ℝ) < (dM N : ℝ) := lt_of_lt_of_le hXpos (Nat.le_ceil _)
  have hX1 : (1:ℝ) ≤ N ^ ((2:ℝ)/5) := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `1 ≤ M`
    have h1 : (1:ℝ) ≤ (dM N : ℝ) := le_trans hX1 (Nat.le_ceil _)
    exact_mod_cast h1
  · -- `M^2 ≤ N`
    have hdMle : (dM N : ℝ) ≤ 2 * N^((2:ℝ)/5) := by linarith
    have hX2 : (N ^ ((2:ℝ)/5))^2 = N ^ ((4:ℝ)/5) := by
      rw [← Real.rpow_natCast (N ^ ((2:ℝ)/5)) 2]
      rw [← Real.rpow_mul hNpos.le]
      norm_num
    have hfour : (4:ℝ) ≤ N^((1:ℝ)/5) := by
      have h := Real.rpow_le_rpow (Real.exp_pos 10).le hNexp
        (show (0:ℝ) ≤ (1:ℝ)/5 by norm_num)
      have h2 : Real.exp 10 ^ ((1:ℝ)/5) = Real.exp 2 := by
        rw [Real.rpow_def_of_pos (Real.exp_pos 10), Real.log_exp]; norm_num
      rw [h2] at h
      have he2 : (4:ℝ) ≤ Real.exp 2 := by
        have h1e : (2:ℝ) ≤ Real.exp 1 := by
          have := Real.add_one_le_exp 1; linarith
        have h4 : Real.exp 2 = (Real.exp 1)^2 := by
          rw [← Real.exp_nat_mul 1 2]; norm_num
        rw [h4]
        calc (4:ℝ) = (2:ℝ)^2 := by norm_num
          _ ≤ (Real.exp 1)^2 := pow_le_pow_left₀ (by norm_num) h1e 2
      linarith
    have hNp : N ^ ((4:ℝ)/5) * N ^ ((1:ℝ)/5) = N := by
      rw [← Real.rpow_add hNpos]; norm_num
    have hnn : (0:ℝ) ≤ N^((4:ℝ)/5) := Real.rpow_nonneg hNpos.le _
    have step : (4:ℝ) * N^((4:ℝ)/5) ≤ N^((1:ℝ)/5) * N^((4:ℝ)/5) :=
      mul_le_mul_of_nonneg_right hfour hnn
    have h2eq : (2 * N^((2:ℝ)/5))^2 = 4 * N^((4:ℝ)/5) := by
      rw [mul_pow, hX2]; norm_num
    have hB : (2 * N^((2:ℝ)/5))^2 ≤ N := by
      rw [h2eq]
      calc (4:ℝ) * N^((4:ℝ)/5) ≤ N^((1:ℝ)/5) * N^((4:ℝ)/5) := step
        _ = N^((4:ℝ)/5) * N^((1:ℝ)/5) := by ring
        _ = N := hNp
    have hnnM : (0:ℝ) ≤ (dM N : ℝ) := le_of_lt hdMpos
    calc (dM N : ℝ)^2 ≤ (2 * N^((2:ℝ)/5))^2 := pow_le_pow_left₀ hnnM hdMle 2
      _ ≤ N := hB
  · -- `2/5 ≤ log M / log N`
    rw [dMu, le_div_iff₀ hlogNpos]
    have hle : N^((2:ℝ)/5) ≤ (dM N : ℝ) := Nat.le_ceil _
    have hlog : Real.log (N^((2:ℝ)/5)) ≤ Real.log (dM N) :=
      Real.log_le_log hXpos hle
    rw [Real.log_rpow hNpos] at hlog
    linarith
  · -- `2 (log M / log N) ≤ 17/20`, via `log M ≤ (2/5) log N + 1/N^(2/5)`
    have hmu : dMu N ≤ 17/40 := by
      rw [dMu, div_le_iff₀ hlogNpos]
      have hle : (dM N : ℝ) ≤ N^((2:ℝ)/5) + 1 := le_of_lt hceil_lt
      have hlog := Real.log_le_log hdMpos hle
      have hsplit : Real.log (N^((2:ℝ)/5) + 1)
          = (2:ℝ)/5 * Real.log N + Real.log (1 + 1/N^((2:ℝ)/5)) := by
        have hXne : N^((2:ℝ)/5) ≠ 0 := ne_of_gt hXpos
        have hfac : N^((2:ℝ)/5) + 1 = N^((2:ℝ)/5) * (1 + 1/N^((2:ℝ)/5)) := by
          field_simp
        rw [hfac, Real.log_mul hXne (by positivity), Real.log_rpow hNpos]
      have hlog1 : Real.log (1 + 1/N^((2:ℝ)/5)) ≤ 1/N^((2:ℝ)/5) := by
        have := Real.log_le_sub_one_of_pos
          (show (0:ℝ) < 1 + 1/N^((2:ℝ)/5) by positivity)
        linarith
      have hXinv : 1/N^((2:ℝ)/5) ≤ (1:ℝ)/4 :=
        one_div_le_one_div_of_le (by norm_num)
          (le_trans (by norm_num : (4:ℝ) ≤ 16) hXge16)
      have hlog40 : (1:ℝ)/4 ≤ (1:ℝ)/40 * Real.log N := by linarith
      linarith
    linarith

end

end Work.BMF.liouville
