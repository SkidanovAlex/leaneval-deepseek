import Mathlib

namespace Work.FIArea6Hecke.R

/-- Elementary bound: for `0 < ε` and `d ≥ 1`, `log (4d+1) ≤ (5^ε/ε)·d^ε`.
Indeed `log x ≤ x^ε/ε` and `4d+1 ≤ 5d`. -/
lemma log_four_mul_add_one_le (ε : ℝ) (hε : 0 < ε) (d : ℕ) (hd : 1 ≤ d) :
    Real.log (4 * (d : ℝ) + 1) ≤ (5 ^ ε / ε) * (d : ℝ) ^ ε := by
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < (d : ℝ) := lt_of_lt_of_le one_pos hdR
  have hA2 : 0 < 4 * (d : ℝ) + 1 := by linarith
  have hle5 : 4 * (d : ℝ) + 1 ≤ 5 * (d : ℝ) := by linarith
  have hrpow : (4 * (d : ℝ) + 1) ^ ε ≤ 5 ^ ε * (d : ℝ) ^ ε := by
    have h1 := Real.rpow_le_rpow (le_of_lt hA2) hle5 (le_of_lt hε)
    rwa [Real.mul_rpow (by norm_num) (le_of_lt hdpos)] at h1
  have h0 := Real.log_le_rpow_div (le_of_lt hA2) hε
  have h1 : (4 * (d : ℝ) + 1) ^ ε / ε ≤ (5 ^ ε * (d : ℝ) ^ ε) / ε :=
    div_le_div_of_nonneg_right hrpow (le_of_lt hε)
  have h2 : (5 ^ ε * (d : ℝ) ^ ε) / ε = (5 ^ ε / ε) * (d : ℝ) ^ ε := by ring
  linarith

/-- The main elementary estimate, for an abstract `δ` satisfying the two numeric conditions
`δ ≤ 1/2` and `δ·(5^ε/ε) ≤ log 3 / 2`. -/
lemma heckeStripArithConst_aux (ε : ℝ) (hε : 0 < ε) (δ : ℝ) (hδpos : 0 < δ)
    (hhalf : δ ≤ 1 / 2) (hδC : δ * (5 ^ ε / ε) ≤ Real.log 3 / 2) :
    ∀ (d : ℕ) (P : ℝ), 1 ≤ d → 0 ≤ P →
      δ * Real.log (4 * (d : ℝ) + P + 1) ≤ (d : ℝ) ^ ε * Real.log (P + 3) := by
  intro d P hd hP
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdtε_ge1 : 1 ≤ (d : ℝ) ^ ε := Real.one_le_rpow hdR (le_of_lt hε)
  have hdtε_pos : 0 < (d : ℝ) ^ ε := lt_of_lt_of_le one_pos hdtε_ge1
  have hA2 : 0 < 4 * (d : ℝ) + 1 := by linarith
  have hB3 : 0 < P + 3 := by linarith
  have hlog3pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog3B : Real.log 3 ≤ Real.log (P + 3) := Real.log_le_log (by norm_num) (by linarith)
  have hle : 4 * (d : ℝ) + P + 1 ≤ (4 * (d : ℝ) + 1) * (P + 3) := by nlinarith
  have hlog1 : Real.log (4 * (d : ℝ) + P + 1) ≤
      Real.log (4 * (d : ℝ) + 1) + Real.log (P + 3) := by
    have h := Real.log_le_log (by linarith : (0 : ℝ) < 4 * (d : ℝ) + P + 1) hle
    rwa [Real.log_mul (ne_of_gt hA2) (ne_of_gt hB3)] at h
  have hlog2 := log_four_mul_add_one_le ε hε d hd
  have hstep : δ * Real.log (4 * (d : ℝ) + 1) ≤ (Real.log 3 / 2) * (d : ℝ) ^ ε := by
    have h1 : δ * Real.log (4 * (d : ℝ) + 1) ≤ δ * ((5 ^ ε / ε) * (d : ℝ) ^ ε) :=
      mul_le_mul_of_nonneg_left hlog2 (le_of_lt hδpos)
    have h2 : δ * ((5 ^ ε / ε) * (d : ℝ) ^ ε) = (δ * (5 ^ ε / ε)) * (d : ℝ) ^ ε := by ring
    have h3 : (δ * (5 ^ ε / ε)) * (d : ℝ) ^ ε ≤ (Real.log 3 / 2) * (d : ℝ) ^ ε :=
      mul_le_mul_of_nonneg_right hδC (le_of_lt hdtε_pos)
    linarith
  have hstep2 : (Real.log 3 / 2) * (d : ℝ) ^ ε ≤
      (d : ℝ) ^ ε * Real.log (P + 3) - δ * Real.log (P + 3) := by
    have h1 : (d : ℝ) ^ ε / 2 ≤ (d : ℝ) ^ ε - δ := by linarith
    have h2 : 0 ≤ (d : ℝ) ^ ε / 2 := by linarith
    have h3 : ((d : ℝ) ^ ε / 2) * Real.log 3 ≤ ((d : ℝ) ^ ε - δ) * Real.log (P + 3) :=
      mul_le_mul h1 hlog3B (le_of_lt hlog3pos) (by linarith)
    have h4 : ((d : ℝ) ^ ε / 2) * Real.log 3 = (Real.log 3 / 2) * (d : ℝ) ^ ε := by ring
    nlinarith [h3, h4]
  have hkey : δ * Real.log (4 * (d : ℝ) + 1) + δ * Real.log (P + 3) ≤
      (d : ℝ) ^ ε * Real.log (P + 3) := by linarith
  calc δ * Real.log (4 * (d : ℝ) + P + 1)
      ≤ δ * (Real.log (4 * (d : ℝ) + 1) + Real.log (P + 3)) :=
        mul_le_mul_of_nonneg_left hlog1 (le_of_lt hδpos)
    _ = δ * Real.log (4 * (d : ℝ) + 1) + δ * Real.log (P + 3) := by ring
    _ ≤ (d : ℝ) ^ ε * Real.log (P + 3) := hkey

/-- **The uniform arithmetic comparison between the two logarithmic scales.**  For `0 < ε ≤ 1/4`
there is `δ > 0` with `δ·log(4d + P + 1) ≤ d^ε·log(P + 3)` for all `d ≥ 1`, `P ≥ 0`.  This is the
elementary fact that makes the product scale `4d(|m|+|t|+3)` dominate the sum scale
`4d + |m| + |t| + 1` uniformly, once the power `d^ε` is available: `log(4d) ≤ 2d^ε/ε`
(`Real.log_le_rpow_div`), while `log(P+2) ≤ d^ε log(P+3)` for `d ≥ 1`. -/
theorem heckeStripArithConst (ε : ℝ) (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ (d : ℕ) (P : ℝ), 1 ≤ d → 0 ≤ P →
        δ * Real.log (4 * (d : ℝ) + P + 1) ≤ (d : ℝ) ^ ε * Real.log (P + 3) := by
  have h5ε : (0 : ℝ) < 5 ^ ε := Real.rpow_pos_of_pos (by norm_num) ε
  have hCpos : 0 < 5 ^ ε / ε := div_pos h5ε hε
  have hlog3pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  refine ⟨min (1 / 2) (Real.log 3 / (2 * (5 ^ ε / ε))), ?_, ?_,
    heckeStripArithConst_aux ε hε _ ?_ ?_ ?_⟩
  · exact lt_min (by norm_num) (div_pos hlog3pos (by linarith))
  · have h := min_le_left (1 / 2) (Real.log 3 / (2 * (5 ^ ε / ε)))
    linarith
  · exact lt_min (by norm_num) (div_pos hlog3pos (by linarith))
  · exact min_le_left (1 / 2) (Real.log 3 / (2 * (5 ^ ε / ε)))
  · have h1 := mul_le_mul_of_nonneg_right
      (min_le_right (1 / 2) (Real.log 3 / (2 * (5 ^ ε / ε)))) (le_of_lt hCpos)
    have h2 : (Real.log 3 / (2 * (5 ^ ε / ε))) * (5 ^ ε / ε) = Real.log 3 / 2 := by
      field_simp
    linarith

end Work.FIArea6Hecke.R
