import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.threshold_tools

namespace Work.Deep.Nibble

/-- **Auxiliary threshold form of the squared-log bound.**
For `a > 0` and `x ≥ 1` lying above the threshold `(32 / a ^ 2) ^ (2 / a)` one has
`2 (log x) ^ 2 ≤ x ^ a`.

This is `two_log_sq_le` combined with the monotonicity of `x ↦ x ^ (a / 2)`: from
`x ≥ (32 / a ^ 2) ^ (2 / a)` we get `x ^ (a / 2) ≥ 32 / a ^ 2`, whence
`(32 / a ^ 2) * x ^ (a / 2) ≤ x ^ (a / 2) * x ^ (a / 2) = x ^ a`. -/
theorem two_log_sq_le_pow {a x : ℝ} (ha : 0 < a) (hx1 : 1 ≤ x)
    (hxN : (32 / a ^ 2) ^ (2 / a) ≤ x) : 2 * (Real.log x) ^ 2 ≤ x ^ a := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hcp : 0 < 32 / a ^ 2 := div_pos (by norm_num) (pow_pos ha 2)
  have hNp : 0 < (32 / a ^ 2) ^ (2 / a) := Real.rpow_pos_of_pos hcp _
  have hmono : ((32 / a ^ 2) ^ (2 / a)) ^ (a / 2) ≤ x ^ (a / 2) :=
    Real.rpow_le_rpow hNp.le hxN (div_nonneg ha.le (by norm_num))
  have hval : ((32 / a ^ 2) ^ (2 / a)) ^ (a / 2) = 32 / a ^ 2 := by
    rw [← Real.rpow_mul hcp.le, show (2 / a) * (a / 2) = 1 from by field_simp,
      Real.rpow_one]
  have hB : 32 / a ^ 2 ≤ x ^ (a / 2) := by
    calc 32 / a ^ 2 = ((32 / a ^ 2) ^ (2 / a)) ^ (a / 2) := hval.symm
      _ ≤ x ^ (a / 2) := hmono
  have hxp : 0 < x ^ (a / 2) := Real.rpow_pos_of_pos hx0 _
  have hstep : (32 / a ^ 2) * x ^ (a / 2) ≤ x ^ (a / 2) * x ^ (a / 2) :=
    mul_le_mul_of_nonneg_right hB hxp.le
  have hjoin : x ^ (a / 2) * x ^ (a / 2) = x ^ a := by
    rw [← Real.rpow_add hx0, show a / 2 + a / 2 = a from by ring]
  calc 2 * (Real.log x) ^ 2 ≤ (32 / a ^ 2) * x ^ (a / 2) := two_log_sq_le ha hx1
    _ ≤ x ^ (a / 2) * x ^ (a / 2) := hstep
    _ = x ^ a := hjoin

/-- **Clause 5 of the asymptotic side conditions of `cor:sparse_egj`** (threshold form).
For every `E > 0` and `κ > 0` there is `N > 0` such that for all `n ≥ N` and all
`D ≥ n^{1/100}` one has `n^(2 log n) ≤ exp(((1+κ)D)^E)`.

Route: since `n : ℕ` and `N > 0`, `n ≥ 1`, so `D ≥ n^{1/100} ≥ 1 > 0`.  Writing
`a := E / 100`, the auxiliary `two_log_sq_le_pow` with `x := n` and
`N := (32/a^2)^(2/a)` gives `2 (log n)^2 ≤ n^a`, and
`n^a = (n^{1/100})^E ≤ ((1+κ)D)^E` by monotonicity of the power, using
`n^{1/100} ≤ D ≤ (1+κ)D`.  Finally `n^(2 log n) = exp (log n * (2 log n)) ≤
exp (((1+κ)D)^E)` by `Real.rpow_def_of_pos` and monotonicity of `exp`. -/
theorem threshold_cond5 {E κ : ℝ} (hE : 0 < E) (hκ : 0 < κ) :
    ∃ N : ℝ, 0 < N ∧ ∀ n : ℕ, N ≤ (n : ℝ) → ∀ D : ℝ, (n : ℝ) ^ ((1 : ℝ) / 100) ≤ D →
      (n : ℝ) ^ (2 * Real.log n) ≤ Real.exp (((1 + κ) * D) ^ E) := by
  have ha : 0 < E / 100 := div_pos hE (by norm_num)
  have hcp : 0 < 32 / (E / 100) ^ 2 := div_pos (by norm_num) (pow_pos ha 2)
  have hNp : 0 < (32 / (E / 100) ^ 2) ^ (2 / (E / 100)) := Real.rpow_pos_of_pos hcp _
  refine ⟨(32 / (E / 100) ^ 2) ^ (2 / (E / 100)), hNp, ?_⟩
  intro n hn D hD
  have hn0 : 0 < (n : ℝ) := lt_of_lt_of_le hNp hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    have hpn : 0 < n := Nat.cast_pos.mp hn0
    have : 1 ≤ n := by omega
    exact_mod_cast this
  have hkey : 2 * (Real.log (n : ℝ)) ^ 2 ≤ (n : ℝ) ^ (E / 100) := two_log_sq_le_pow ha hn1 hn
  have hDbase : (1 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 100) := by
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hn1 (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 100)
    rwa [Real.one_rpow] at h
  have hA0 : (0 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 100) := le_trans zero_le_one hDbase
  have hD0 : (0 : ℝ) ≤ D := hA0.trans hD
  have hbase_le : (n : ℝ) ^ ((1 : ℝ) / 100) ≤ (1 + κ) * D :=
    hD.trans (le_mul_of_one_le_left hD0 (by linarith))
  have hnpow : (n : ℝ) ^ (E / 100) = ((n : ℝ) ^ ((1 : ℝ) / 100)) ^ E := by
    rw [← Real.rpow_mul hn0.le, show (1 : ℝ) / 100 * E = E / 100 from by ring]
  have hle : ((n : ℝ) ^ ((1 : ℝ) / 100)) ^ E ≤ ((1 + κ) * D) ^ E :=
    Real.rpow_le_rpow hA0 hbase_le hE.le
  have hfinal : 2 * Real.log (n : ℝ) * Real.log (n : ℝ) ≤ ((1 + κ) * D) ^ E := by
    calc 2 * Real.log (n : ℝ) * Real.log (n : ℝ) = 2 * (Real.log (n : ℝ)) ^ 2 := by ring
      _ ≤ (n : ℝ) ^ (E / 100) := hkey
      _ = ((n : ℝ) ^ ((1 : ℝ) / 100)) ^ E := hnpow
      _ ≤ ((1 + κ) * D) ^ E := hle
  calc (n : ℝ) ^ (2 * Real.log (n : ℝ))
      = Real.exp (Real.log (n : ℝ) * (2 * Real.log (n : ℝ))) := Real.rpow_def_of_pos hn0 _
    _ = Real.exp (2 * Real.log (n : ℝ) * Real.log (n : ℝ)) := by
        rw [show Real.log (n : ℝ) * (2 * Real.log (n : ℝ))
              = 2 * Real.log (n : ℝ) * Real.log (n : ℝ) from by ring]
    _ ≤ Real.exp (((1 + κ) * D) ^ E) := Real.exp_le_exp.mpr hfinal

end Work.Deep.Nibble
