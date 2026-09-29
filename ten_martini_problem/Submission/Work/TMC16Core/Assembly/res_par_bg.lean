import Mathlib
import Submission.Work.TMC16Core.Assembly.RegWin

namespace Work.TMC16Core.Assembly

/-- For `0 < k`, `m/k - 1 < ⌊m/k⌋` over `ℝ` (`m/k - 1 < ⌊m/k⌋`), i.e. the natural division
`m / k` is at most `1` below the real quotient `m / k`. -/
lemma res_natCast_div_gt_one (m k : ℕ) (hk : 0 < k) :
    (m : ℝ) / (k : ℝ) - 1 < ((m / k : ℕ) : ℝ) := by
  have h1 : m < (m / k + 1) * k := (Nat.div_lt_iff_lt_mul hk).mp (Nat.lt_succ_self _)
  have h2 : (m : ℝ) < ((m / k + 1 : ℕ) : ℝ) * (k : ℝ) := by exact_mod_cast h1
  have h3 : (m : ℝ) / (k : ℝ) < ((m / k : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ (by exact_mod_cast hk)]
    have hc : (((m / k + 1 : ℕ)) : ℝ) = ((m / k : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [hc] at h2
    exact h2
  linarith

theorem res_par_bg {q : ℕ → ℕ} {n : ℕ} (hmono : StrictMono q) (h : 20 ^ 9 ≤ q n) :
    0 ≤ Work.TMC16Core.Assembly.bG q n ∧ Work.TMC16Core.Assembly.bG q n ≤ (q n : ℝ) / 20 + 3 ∧
    Work.TMC16Core.Assembly.bG q n ≤ (((5 * q n / 8 : ℕ) : ℝ)) - 1 ∧
    (((2 * q n - 1 : ℕ) : ℝ)) ≤ 40 * ((((5 * q n / 8 : ℕ) : ℝ)) - 1 - Work.TMC16Core.Assembly.bG q n) := by
  -- `20 ≤ q n`, hence `q n > 0`.
  have hQ20 : (20 : ℝ) ≤ (q n : ℝ) := by
    have h1 : ((20 : ℕ) ^ 9 : ℝ) ≤ (q n : ℝ) := by exact_mod_cast h
    calc (20 : ℝ) ≤ ((20 : ℕ) ^ 9 : ℝ) := by norm_num
      _ ≤ (q n : ℝ) := h1
  have hQpos : (0 : ℝ) < (q n : ℝ) := lt_of_lt_of_le (by norm_num) hQ20
  -- `(q n)^{1/9} ≥ 20`, so `(q n)^{8/9} ≤ q n / 20`.
  have hroot : (20 : ℝ) ≤ (q n : ℝ) ^ ((1 : ℝ) / 9) := by
    have h1 : (((20 : ℝ)) ^ (9 : ℕ)) ^ ((1 : ℝ) / 9) ≤ (q n : ℝ) ^ ((1 : ℝ) / 9) := by
      apply Real.rpow_le_rpow (by positivity)
      · exact_mod_cast h
      · norm_num
    have h2 : (((20 : ℝ)) ^ (9 : ℕ)) ^ ((1 : ℝ) / 9) = 20 := by
      rw [show (((20 : ℝ)) ^ (9 : ℕ)) = ((20 : ℝ)) ^ (((9 : ℕ) : ℝ)) from
        (Real.rpow_natCast 20 9).symm]
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 20)]
      norm_num
    rw [h2] at h1; exact h1
  have hpow : (q n : ℝ) ^ ((8 : ℝ) / 9) ≤ (q n : ℝ) / 20 := by
    have h8 : (q n : ℝ) ^ ((8 : ℝ) / 9) * (q n : ℝ) ^ ((1 : ℝ) / 9) =
        (q n : ℝ) ^ (1 : ℝ) := by
      rw [← Real.rpow_add hQpos]; norm_num
    rw [Real.rpow_one] at h8
    have h20 := mul_le_mul_of_nonneg_left hroot (Real.rpow_nonneg hQpos.le ((8 : ℝ) / 9))
    rw [h8] at h20
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 20)]
    linarith
  -- `q (n-1) ≤ q n` by monotonicity.
  have hqle : (q (n - 1) : ℝ) ≤ (q n : ℝ) := by
    have h1 : q (n - 1) ≤ q n := hmono.monotone (Nat.sub_le n 1)
    exact_mod_cast h1
  -- The main level bound.
  have hBG : bG q n ≤ (q n : ℝ) / 20 + 3 := by
    rw [bG]
    exact max_le (le_trans hpow (by linarith)) (by linarith)
  -- The floor bound for `5 q n / 8`.
  have hF : (5 * (q n : ℝ)) / 8 - 1 < (((5 * q n / 8 : ℕ) : ℝ)) := by
    have hh := res_natCast_div_gt_one (5 * q n) 8 (by norm_num)
    have hc : ((5 * q n : ℕ) : ℝ) = 5 * (q n : ℝ) := by push_cast; ring
    rw [hc] at hh; exact hh
  refine ⟨?_, hBG, ?_, ?_⟩
  · rw [bG]
    exact le_trans (Real.rpow_nonneg (by positivity) _) (le_max_left _ _)
  · have hkey : (q n : ℝ) / 20 + 3 ≤ (5 * (q n : ℝ)) / 8 - 2 := by
      nlinarith [hQ20]
    linarith [hBG, hkey, hF]
  · have hcast : ((2 * q n - 1 : ℕ) : ℝ) = 2 * (q n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * q n)]; push_cast; ring
    rw [hcast]
    have hlb : (5 * (q n : ℝ)) / 8 - 2 - ((q n : ℝ) / 20 + 3)
        ≤ (((5 * q n / 8 : ℕ) : ℝ)) - 1 - bG q n := by
      linarith [hBG, hF]
    have h40 : 2 * (q n : ℝ) - 1
        ≤ 40 * ((5 * (q n : ℝ)) / 8 - 2 - ((q n : ℝ) / 20 + 3)) := by
      nlinarith [hQ20]
    have := mul_le_mul_of_nonneg_left hlb (by norm_num : (0 : ℝ) ≤ 40)
    linarith

end Work.TMC16Core.Assembly
