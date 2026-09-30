import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.VKChain

/-- Auxiliary arithmetic: the Vinogradov–Korobov threshold `(L/cvk)^(6/7)` is at most `L/2`
as soon as `L ≥ 1000/cvk^6` (no upper bound on `cvk` is needed: `κ ≤ L/2` is equivalent to
`L·cvk^6 ≥ 2^7 = 128`, and `1000 ≥ 128`). -/
private theorem kappa_le_half_aux {cvk L : ℝ} (hcvk0 : 0 < cvk) (hL : 1000 / cvk ^ 6 ≤ L) :
    (L / cvk) ^ (6 / 7 : ℝ) ≤ L / 2 := by
  have hc6pos : (0 : ℝ) < cvk ^ 6 := by positivity
  have hcvk6ne : cvk ^ 6 ≠ 0 := ne_of_gt hc6pos
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity : (0 : ℝ) < 1000 / cvk ^ 6) hL
  have hbase : 0 < L / cvk := by positivity
  have hLc : (1000 : ℝ) ≤ L * cvk ^ 6 := (div_le_iff₀ hc6pos).mp hL
  have hLg : (128 : ℝ) / cvk ^ 6 ≤ L := by
    rw [div_le_iff₀ hc6pos]
    nlinarith [hLc]
  have hlogL : Real.log ((128 : ℝ) / cvk ^ 6) ≤ Real.log L :=
    Real.log_le_log (by positivity) hLg
  have h128 : Real.log (128 : ℝ) = 7 * Real.log 2 := by
    rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]
    norm_num
  have hexpand : Real.log ((128 : ℝ) / cvk ^ 6) = 7 * Real.log 2 - 6 * Real.log cvk := by
    rw [Real.log_div (by norm_num : (128 : ℝ) ≠ 0) hcvk6ne, Real.log_pow, h128]
    norm_num
  refine (Real.log_le_log_iff (Real.rpow_pos_of_pos hbase _)
    (by positivity : (0 : ℝ) < L / 2)).mp ?_
  rw [Real.log_rpow hbase, Real.log_div hL0.ne' hcvk0.ne',
    Real.log_div hL0.ne' (by norm_num : (2 : ℝ) ≠ 0)]
  linarith [hlogL, hexpand]

/-- Auxiliary: the gate hypothesis `1000/cvk^6 ≤ log(x+3)` forces
`exp((log(x+3)/cvk)^(6/7)) + 2 ≤ x` for all `x ≥ 6`. -/
private theorem exp_kappa_gate_aux {cvk x : ℝ} (hcvk0 : 0 < cvk) (hx : 6 ≤ x)
    (hlog : 1000 / cvk ^ 6 ≤ Real.log (x + 3)) :
    Real.exp ((Real.log (x + 3) / cvk) ^ (6 / 7 : ℝ)) + 2 ≤ x := by
  have hx3pos : 0 < x + 3 := by linarith
  have hκ : (Real.log (x + 3) / cvk) ^ (6 / 7 : ℝ) ≤ Real.log (x + 3) / 2 :=
    kappa_le_half_aux hcvk0 hlog
  have hexp : Real.exp ((Real.log (x + 3) / cvk) ^ (6 / 7 : ℝ)) ≤ Real.sqrt (x + 3) := by
    calc Real.exp ((Real.log (x + 3) / cvk) ^ (6 / 7 : ℝ))
        ≤ Real.exp (Real.log (x + 3) / 2) := Real.exp_le_exp.mpr hκ
      _ = Real.sqrt (Real.exp (Real.log (x + 3))) := Real.exp_half _
      _ = Real.sqrt (x + 3) := by rw [Real.exp_log hx3pos]
  have hsqrt : Real.sqrt (x + 3) ≤ x - 2 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by linarith, by nlinarith [hx, sq_nonneg (x - 6)]⟩
  linarith

/-- Consequence of the size gate `exp(1000/cvk^6) ≤ |t|` for the Vinogradov–Korobov threshold
`κ = (log(|t|+3)/cvk)^{6/7}`: `κ ≤ log(|t|+3)/2` and `exp κ + 2 ≤ |t|`. -/
theorem gate_kappa_le {cvk t : ℝ} (hcvk0 : 0 < cvk) (hcvk1 : cvk ≤ 1) (ht : 3 ≤ |t|)
    (hgate : Real.exp (1000 / cvk ^ 6) ≤ |t|) :
    (Real.log (|t| + 3) / cvk) ^ (6 / 7 : ℝ) ≤ Real.log (|t| + 3) / 2 ∧
      Real.exp ((Real.log (|t| + 3) / cvk) ^ (6 / 7 : ℝ)) + 2 ≤ |t| ∧
      1 ≤ Real.log (|t| + 3) := by
  have hc6le : cvk ^ 6 ≤ 1 := by
    have h : cvk ^ 6 ≤ (1 : ℝ) ^ 6 := pow_le_pow_left₀ hcvk0.le hcvk1 6
    simpa using h
  have hx6 : (6 : ℝ) ≤ |t| := by
    have h1001 : (1001 : ℝ) ≤ Real.exp 1000 := by
      have := Real.add_one_le_exp 1000; linarith
    have hge : (1000 : ℝ) ≤ 1000 / cvk ^ 6 := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < cvk ^ 6)]
      nlinarith [hc6le]
    have hexpmono : Real.exp 1000 ≤ Real.exp (1000 / cvk ^ 6) := Real.exp_le_exp.mpr hge
    linarith [h1001, hexpmono, hgate]
  have hL1 : 1 ≤ Real.log (|t| + 3) := by
    rw [Real.le_log_iff_exp_le (by linarith [abs_nonneg t])]
    linarith [Real.exp_one_lt_three, ht]
  have hLgate : 1000 / cvk ^ 6 ≤ Real.log (|t| + 3) := by
    have h : Real.log (Real.exp (1000 / cvk ^ 6)) ≤ Real.log (|t| + 3) :=
      Real.log_le_log (Real.exp_pos _) (by linarith [hgate])
    rwa [Real.log_exp] at h
  exact ⟨kappa_le_half_aux hcvk0 hLgate, exp_kappa_gate_aux hcvk0 hx6 hLgate, hL1⟩

end Work.BMF.VKChain
