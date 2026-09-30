import Mathlib
import Submission.Work.BMF.VKExpSum.ford51_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.VKExpSum

noncomputable section

/-- **Facts about `M = ⌈N^{2/5}⌉` and `μ = log M / log N`.** For `N ≥ 2` with `log N ≥ 70`
(module `Submission.Work.BMF.VKExpSum.ford51_defs`: `dM N = ⌈N^{2/5}⌉`, `dMu N = log (dM N)/log N`).

Route: `Nat.le_ceil`/`Nat.ceil_lt_add_one` for `M`; `Real.rpow_def_of_pos` + `Real.exp_log` for
`(dM N : ℝ) = N ^ dMu N`; `log N ≥ 70` gives `N ≥ 1024`, hence `2 ≤ N^{1/5}` (so `M² ≤ N`) and
`log 2 ≤ (1/100)·log N` (so `μ ≤ 41/100`; `2/5 ≤ μ` is immediate from `M ≥ N^{2/5}`). -/
theorem ford51_Mfacts (N : ℝ) (hN : 2 ≤ N) (hlog : 70 ≤ Real.log N) :
    (1 ≤ dM N) ∧ ((dM N : ℝ) = N ^ (dMu N))
      ∧ ((2 : ℝ) / 5 ≤ dMu N) ∧ (dMu N ≤ 41 / 100)
      ∧ ((dM N : ℝ) ^ 2 ≤ N)
      ∧ ((dM N : ℝ) ≤ 2 * N ^ ((2 : ℝ) / 5)) := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hlogpos : (0 : ℝ) < Real.log N := by linarith
  have h1N : (1 : ℝ) ≤ N := by linarith
  have hx1 : (1 : ℝ) ≤ N ^ ((2 : ℝ) / 5) := by
    simpa using (Real.rpow_le_rpow_of_exponent_le h1N (by norm_num : (0 : ℝ) ≤ (2 : ℝ) / 5))
  have hMge : N ^ ((2 : ℝ) / 5) ≤ (dM N : ℝ) := Nat.le_ceil _
  have hMlt : (dM N : ℝ) < N ^ ((2 : ℝ) / 5) + 1 :=
    Nat.ceil_lt_add_one (le_trans zero_le_one hx1)
  have hMpos : (0 : ℝ) < (dM N : ℝ) := by linarith
  have hMle : (dM N : ℝ) ≤ 2 * N ^ ((2 : ℝ) / 5) := by linarith
  -- `N ≥ 1024`
  have hN1024 : (1024 : ℝ) ≤ N := by
    have h2 : Real.exp 70 ≤ N := (Real.le_log_iff_exp_le hN0).mp hlog
    have h3 : (1024 : ℝ) ≤ Real.exp 70 := by
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 1024), Real.exp_le_exp]
      rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow]
      have h4 : Real.log 2 ≤ (1 : ℝ) := by
        have h5 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
        linarith
      push_cast
      linarith
    linarith
  have h4 : (4 : ℝ) ≤ N ^ ((1 : ℝ) / 5) := by
    have h5 : ((4 : ℝ) ^ 5) ≤ N := by norm_num at hN1024 ⊢; linarith
    have h6 := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ ((4 : ℝ) ^ 5)) h5
      (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 5)
    rwa [show ((4 : ℝ) ^ 5) ^ ((1 : ℝ) / 5) = 4 by
      rw [← Real.rpow_natCast (4 : ℝ) 5, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num] at h6
  have hsplit : N ^ ((1 : ℝ) / 5) * N ^ ((4 : ℝ) / 5) = N := by
    rw [← Real.rpow_add hN0]
    norm_num
  have hM2 : (dM N : ℝ) ^ 2 ≤ N := by
    have h1 : (dM N : ℝ) ^ 2 ≤ (2 * N ^ ((2 : ℝ) / 5)) ^ 2 :=
      pow_le_pow_left₀ hMpos.le hMle 2
    have h2 : (2 * N ^ ((2 : ℝ) / 5)) ^ 2 = 4 * N ^ ((4 : ℝ) / 5) := by
      rw [mul_pow, ← Real.rpow_natCast (N ^ ((2 : ℝ) / 5)) 2, ← Real.rpow_mul hN0.le]
      norm_num
    have h3 : 4 * N ^ ((4 : ℝ) / 5) ≤ N := by
      have h4' : 4 * N ^ ((4 : ℝ) / 5) ≤ N ^ ((1 : ℝ) / 5) * N ^ ((4 : ℝ) / 5) :=
        mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg hN0.le _)
      rwa [hsplit] at h4'
    calc (dM N : ℝ) ^ 2 ≤ (2 * N ^ ((2 : ℝ) / 5)) ^ 2 := h1
      _ = 4 * N ^ ((4 : ℝ) / 5) := h2
      _ ≤ N := h3
  have hMpow : (dM N : ℝ) = N ^ (dMu N) := by
    rw [dMu, Real.rpow_def_of_pos hN0]
    rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hlogpos), Real.exp_log hMpos]
  have hmu_ge : (2 : ℝ) / 5 ≤ dMu N := by
    rw [dMu, le_div_iff₀ hlogpos]
    calc (2 : ℝ) / 5 * Real.log N = Real.log (N ^ ((2 : ℝ) / 5)) :=
          (Real.log_rpow hN0 ((2 : ℝ) / 5)).symm
      _ ≤ Real.log (dM N) := Real.log_le_log (Real.rpow_pos_of_pos hN0 _) hMge
  have hmu_le : dMu N ≤ 41 / 100 := by
    have h2 : Real.log (dM N) ≤ Real.log 2 + (2 : ℝ) / 5 * Real.log N := by
      calc Real.log (dM N) ≤ Real.log (2 * N ^ ((2 : ℝ) / 5)) := Real.log_le_log hMpos hMle
        _ = Real.log 2 + (2 : ℝ) / 5 * Real.log N := by
            rw [Real.log_mul (by norm_num) (ne_of_gt (Real.rpow_pos_of_pos hN0 _)),
              Real.log_rpow hN0]
    rw [dMu, div_le_iff₀ hlogpos]
    have hlt : Real.log 2 ≤ (1 : ℝ) / 100 * Real.log N := by
      have := Real.log_two_lt_d9
      nlinarith [hlog]
    linarith
  exact ⟨by exact_mod_cast (le_trans hx1 hMge), hMpow, hmu_ge, hmu_le, hM2, hMle⟩

end

end Work.BMF.VKExpSum
