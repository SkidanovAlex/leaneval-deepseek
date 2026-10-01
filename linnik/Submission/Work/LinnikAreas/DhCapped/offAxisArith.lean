import Mathlib

namespace Work.LinnikAreas.DhCapped

/-- **Arithmetic for the off-axis zero-free region at imaginary part `O(log q)`.**

Let `q ≥ 3` be a modulus, `d ≤ q` a conductor (`1 ≤ d`), and `ρ = x + i t` a point satisfying the
off-axis zero-free region bound `1 - x > c₁ / log (d (|t| + 2))` for a constant `c₁ > 0`.  If the
imaginary part obeys `|t| ≤ 10 log q`, then `λ = (1 - x) log q ≥ c₁ / 14`.

Elementary: `d (|t| + 2) ≤ q (10 log q + 2) ≤ 12 q log q` because `log q ≥ log 3 > 1`, so
`log (d (|t|+2)) ≤ log q + log (12 log q) ≤ log q + (12 log q - 1) ≤ 13 log q` by
`Real.log_le_sub_one_of_pos`; hence `1 - x > c₁ / (13 log q)`, and multiplying by `log q > 0`
gives `λ > c₁/13 ≥ c₁/14`. -/
theorem offAxisArith {c₁ x t : ℝ} {d q : ℕ} (hc₁ : 0 < c₁) (hd : 1 ≤ d) (hdq : d ≤ q)
    (hq : 3 ≤ q) (ht : |t| ≤ 10 * Real.log (q : ℝ))
    (hx : c₁ / Real.log ((d : ℝ) * (|t| + 2)) < 1 - x) :
    c₁ / 14 ≤ (1 - x) * Real.log (q : ℝ) := by
  have hq3 : (3:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have hq1 : (1:ℝ) < (q:ℝ) := by linarith
  have hqpos : (0:ℝ) < (q:ℝ) := by linarith
  have hlogq_pos : 0 < Real.log (q:ℝ) := Real.log_pos hq1
  have hlogq_ge_one : 1 ≤ Real.log (q:ℝ) := by
    rw [Real.le_log_iff_exp_le hqpos]
    linarith [Real.exp_one_lt_three, hq3]
  have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hdq' : (d:ℝ) ≤ (q:ℝ) := by exact_mod_cast hdq
  have habs : |t| + 2 ≤ 10 * Real.log (q:ℝ) + 2 := by linarith
  have habsnn : (0:ℝ) ≤ |t| + 2 := by positivity
  have hstep1 : (d:ℝ) * (|t| + 2) ≤ (q:ℝ) * (10 * Real.log (q:ℝ) + 2) :=
    mul_le_mul hdq' habs habsnn (by linarith)
  have hstep2 : (10 * Real.log (q:ℝ) + 2) ≤ 12 * Real.log (q:ℝ) := by linarith
  have h12logq_pos : 0 < 12 * Real.log (q:ℝ) := by linarith
  have hstep3 : (q:ℝ) * (10 * Real.log (q:ℝ) + 2) ≤ (q:ℝ) * (12 * Real.log (q:ℝ)) :=
    mul_le_mul_of_nonneg_left hstep2 (le_of_lt hqpos)
  have hbound : (d:ℝ) * (|t| + 2) ≤ (q:ℝ) * (12 * Real.log (q:ℝ)) := le_trans hstep1 hstep3
  have hdpos : 0 < (d:ℝ) * (|t| + 2) := by
    have := abs_nonneg t
    nlinarith [hd1, habsnn]
  have hqne : (q:ℝ) ≠ 0 := ne_of_gt hqpos
  have h12ne : (12 * Real.log (q:ℝ)) ≠ 0 := ne_of_gt h12logq_pos
  have hexpand : Real.log ((q:ℝ) * (12 * Real.log (q:ℝ)))
      = Real.log (q:ℝ) + Real.log (12 * Real.log (q:ℝ)) := Real.log_mul hqne h12ne
  have hlog_le2 : Real.log (12 * Real.log (q:ℝ)) ≤ 12 * Real.log (q:ℝ) - 1 :=
    Real.log_le_sub_one_of_pos h12logq_pos
  have hlogd_le : Real.log ((d:ℝ) * (|t| + 2)) ≤ 13 * Real.log (q:ℝ) := by
    calc Real.log ((d:ℝ) * (|t| + 2))
        ≤ Real.log ((q:ℝ) * (12 * Real.log (q:ℝ))) := Real.log_le_log hdpos hbound
      _ = Real.log (q:ℝ) + Real.log (12 * Real.log (q:ℝ)) := hexpand
      _ ≤ Real.log (q:ℝ) + (12 * Real.log (q:ℝ) - 1) := by linarith [hlog_le2]
      _ ≤ 13 * Real.log (q:ℝ) := by linarith
  have hlogd_pos : 0 < Real.log ((d:ℝ) * (|t| + 2)) := by
    apply Real.log_pos
    have := abs_nonneg t
    nlinarith [hd1, habsnn]
  have hc_div : c₁ / (13 * Real.log (q:ℝ)) ≤ c₁ / Real.log ((d:ℝ) * (|t| + 2)) :=
    div_le_div_of_nonneg_left (le_of_lt hc₁) hlogd_pos hlogd_le
  have hlt : c₁ / (13 * Real.log (q:ℝ)) < 1 - x := lt_of_le_of_lt hc_div hx
  have hmul : c₁ / (13 * Real.log (q:ℝ)) * Real.log (q:ℝ) < (1 - x) * Real.log (q:ℝ) :=
    mul_lt_mul_of_pos_right hlt hlogq_pos
  have hsimp : c₁ / (13 * Real.log (q:ℝ)) * Real.log (q:ℝ) = c₁ / 13 := by
    field_simp
  have hfinal : c₁ / 13 ≤ (1 - x) * Real.log (q:ℝ) := by
    rw [← hsimp]; exact le_of_lt hmul
  have hle : c₁ / 14 ≤ c₁ / 13 := div_le_div_of_nonneg_left (le_of_lt hc₁) (by norm_num) (by norm_num)
  linarith

end Work.LinnikAreas.DhCapped
