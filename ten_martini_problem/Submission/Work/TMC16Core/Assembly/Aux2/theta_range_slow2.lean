import Mathlib
import Submission.Work.TMC16Core.Defs

namespace Work.TMC16Core.Assembly.Aux2

/-- **`theta_range_slow2`.**  Slow-scale version of the index-range reduction, with the wider
index range `|j| ≤ 8 (q (n+1))^{8/9} + 8 q n + 4`.  The two `fracDist` lower bounds — `csm`
below the cut-off `|k| < K₀` and `1/k²` above it — are turned into a single constant `c` valid
on the whole range: with `B` the range endpoint one takes `c = min csm B⁻²`, and the growth
condition `q (n+1) ≤ (8 q n)^9` bounds `B ≤ 10^9 (q n)^8 ≤ e^{30} ((q n) + 2)^{10}`, whence
the logarithmic cost `log (1/c) ≤ log (1/csm) + 60 + 20 log ((q n) + 2)`. -/
theorem theta_range_slow2 {α θ : ℝ} {K₀ : ℤ} {csm : ℝ} {q : ℕ → ℕ} {n : ℕ}
    (hK₀1 : 1 ≤ K₀) (hcsm : 0 < csm) (hcsm1 : csm ≤ 1)
    (h1 : ∀ k : ℤ, |k| < K₀ → csm ≤ Work.TMC16Core.fracDist (2 * θ + (k : ℝ) * α))
    (h2 : ∀ k : ℤ, K₀ ≤ |k| → (((k.natAbs : ℕ) : ℝ))⁻¹ ^ 2 ≤ Work.TMC16Core.fracDist (2 * θ + (k : ℝ) * α))
    (hqpos : ∀ i, 0 < q i)
    (hslow : q (n + 1) ≤ (8 * q n) ^ 9) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧
      (∀ j : ℤ, |(j : ℝ)| ≤ 8 * Real.rpow (q (n + 1) : ℝ) (8 / 9) + 8 * (q n : ℝ) + 4 →
        c ≤ Work.TMC16Core.fracDist (2 * θ + (j : ℝ) * α)) ∧
      Real.log (1 / c) ≤ Real.log (1 / csm) + 60 + 20 * Real.log ((q n : ℝ) + 2) := by
  set B : ℝ := 8 * Real.rpow (q (n + 1) : ℝ) (8 / 9) + 8 * (q n : ℝ) + 4 with hB
  have hQ1 : (1 : ℝ) ≤ (q n : ℝ) := by exact_mod_cast hqpos n
  have hQpos : (0 : ℝ) < (q n : ℝ) := by linarith
  -- (1) the power bound coming from `hslow`
  have hrpow : Real.rpow (q (n + 1) : ℝ) (8 / 9) ≤ (8 * (q n : ℝ)) ^ 8 := by
    have hsl : (q (n + 1) : ℝ) ≤ (8 * (q n : ℝ)) ^ 9 := by
      have h := hslow; exact_mod_cast h
    have hstep := Real.rpow_le_rpow (by positivity) hsl (by norm_num : (0 : ℝ) ≤ 8 / 9)
    refine le_trans hstep (le_of_eq ?_)
    rw [← Real.rpow_natCast (8 * (q n : ℝ)) 9]
    rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 8 * (q n : ℝ)) ((9 : ℕ) : ℝ) (8 / 9 : ℝ)]
    norm_num
  -- (2) `B ≤ 2^28 * (q n)^8`
  have hBle : B ≤ 2 ^ 28 * (q n : ℝ) ^ 8 := by
    rw [hB]
    have hQ8 : (8 * (q n : ℝ)) ^ 8 = 16777216 * (q n : ℝ) ^ 8 := by rw [mul_pow]; norm_num
    rw [hQ8] at hrpow
    have hQ8ge1 : (1 : ℝ) ≤ (q n : ℝ) ^ 8 := one_le_pow₀ hQ1
    have hQ8geQ : (q n : ℝ) ≤ (q n : ℝ) ^ 8 := by
      calc (q n : ℝ) = (q n : ℝ) * 1 := by ring
        _ ≤ (q n : ℝ) * (q n : ℝ) ^ 7 := by
            apply mul_le_mul_of_nonneg_left _ (by linarith)
            calc (1 : ℝ) = (q n : ℝ) ^ 0 := by ring
              _ ≤ (q n : ℝ) ^ 7 := pow_le_pow_right₀ hQ1 (by norm_num)
        _ = (q n : ℝ) ^ 8 := by ring
    calc 8 * Real.rpow (q (n + 1) : ℝ) (8 / 9) + 8 * (q n : ℝ) + 4
        ≤ 8 * (16777216 * (q n : ℝ) ^ 8) + 8 * (q n : ℝ) + 4 := by linarith [hrpow]
      _ = 134217728 * (q n : ℝ) ^ 8 + 8 * (q n : ℝ) + 4 := by ring
      _ ≤ 134217728 * (q n : ℝ) ^ 8 + 8 * (q n : ℝ) ^ 8 + 4 * (q n : ℝ) ^ 8 := by
            linarith [hQ8geQ, hQ8ge1]
      _ = 134217740 * (q n : ℝ) ^ 8 := by ring
      _ ≤ 2 ^ 28 * (q n : ℝ) ^ 8 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          norm_num
  have hBpos : 0 < B := by
    rw [hB]
    have hr : (0 : ℝ) ≤ Real.rpow (q (n + 1) : ℝ) (8 / 9) := Real.rpow_nonneg (by positivity) _
    linarith [hQ1, hr]
  -- (3) the logarithmic bound on `B`
  have hlogB : 2 * Real.log B ≤ 60 + 20 * Real.log ((q n : ℝ) + 2) := by
    have hlog : Real.log B ≤ 28 * Real.log 2 + 8 * Real.log (q n : ℝ) := by
      have h2 : Real.log B ≤ Real.log (2 ^ 28 * (q n : ℝ) ^ 8) := Real.log_le_log hBpos hBle
      have h3 : Real.log (2 ^ 28 * (q n : ℝ) ^ 8) = 28 * Real.log 2 + 8 * Real.log (q n : ℝ) := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
        norm_num
      linarith [h2, h3.le]
    have hA : Real.log (q n : ℝ) ≤ Real.log ((q n : ℝ) + 2) := Real.log_le_log hQpos (by linarith)
    have hB0 : 0 ≤ Real.log ((q n : ℝ) + 2) := Real.log_nonneg (by linarith)
    have hlog2 : Real.log 2 < 0.7 := lt_trans Real.log_two_lt_d9 (by norm_num)
    nlinarith [hlog, hA, hB0, hlog2]
  refine ⟨min csm (1 / B ^ 2), ?_, ?_, ?_, ?_⟩
  · exact lt_min hcsm (one_div_pos.mpr (pow_pos hBpos 2))
  · refine le_trans (min_le_right _ _) ?_
    have hB12 : (12 : ℝ) ≤ B := by
      rw [hB]
      have hr : (0 : ℝ) ≤ Real.rpow (q (n + 1) : ℝ) (8 / 9) := Real.rpow_nonneg (by positivity) _
      linarith [hQ1, hr]
    have h2 : (2 : ℝ) ≤ B ^ 2 := by nlinarith [hB12]
    exact one_div_le_one_div_of_le (by norm_num) h2
  · intro j hj
    by_cases hK : K₀ ≤ |j|
    · have h2j := h2 j hK
      have hrec : (1 : ℝ) / B ^ 2 ≤ (((j.natAbs : ℕ) : ℝ))⁻¹ ^ 2 := by
        rw [Nat.cast_natAbs, Int.cast_abs]
        have h : (1 : ℤ) ≤ |j| := le_trans hK₀1 hK
        have hx1 : (1 : ℝ) ≤ |(j : ℝ)| := by
          have hR : (1 : ℝ) ≤ ((|j| : ℤ) : ℝ) := by exact_mod_cast h
          rwa [Int.cast_abs] at hR
        have hxpos : (0 : ℝ) < |(j : ℝ)| := by linarith
        have hx2 : |(j : ℝ)| ^ 2 ≤ B ^ 2 := by nlinarith [hj, hxpos, hBpos]
        have h1' : 1 / B ^ 2 ≤ 1 / |(j : ℝ)| ^ 2 := one_div_le_one_div_of_le (by positivity) hx2
        have h2' : (|(j : ℝ)|)⁻¹ ^ 2 = 1 / |(j : ℝ)| ^ 2 := by rw [inv_pow]; ring
        linarith [h1', h2'.symm.le]
      exact le_trans (min_le_right _ _) (le_trans hrec h2j)
    · exact le_trans (min_le_left _ _) (h1 j (not_le.mp hK))
  · rcases le_total csm (1 / B ^ 2) with hcase | hcase
    · rw [min_eq_left hcase]
      have h1' : 0 ≤ Real.log (1 / csm) :=
        Real.log_nonneg (by rw [le_div_iff₀ hcsm]; simpa using hcsm1)
      have h2' : 0 ≤ 60 + 20 * Real.log ((q n : ℝ) + 2) := by
        have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ (q n : ℝ) + 2)
        linarith
      linarith
    · rw [min_eq_right hcase]
      have hc_eq : 1 / (1 / B ^ 2) = B ^ 2 := by rw [one_div, one_div, inv_inv]
      rw [hc_eq, Real.log_pow]
      have h1' : 0 ≤ Real.log (1 / csm) :=
        Real.log_nonneg (by rw [le_div_iff₀ hcsm]; simpa using hcsm1)
      linarith [hlogB, h1']

end Work.TMC16Core.Assembly.Aux2
