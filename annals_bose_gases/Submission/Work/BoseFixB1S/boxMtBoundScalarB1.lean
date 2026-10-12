import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

/-- **The sharper `√`-shift weight**: `s(√(s+1) − √c)² ≤ (s − c − 1)² + s` for `s ≥ 0`, `c ≥ 1`. -/
theorem mul_sqrt_sub_sq_leB1 {s c : ℝ} (hs : 0 ≤ s) (hc : 1 ≤ c) :
    s * (Real.sqrt (s + 1) - Real.sqrt c) ^ 2 ≤ (s - c - 1) ^ 2 + s := by
  have hc0 : 0 ≤ c := le_trans zero_le_one hc
  have hs1 : 0 ≤ s + 1 := by linarith
  set A := Real.sqrt (s + 1) with hAdef
  set B := Real.sqrt c with hBdef
  have hA0 : 0 ≤ A := by rw [hAdef]; exact Real.sqrt_nonneg _
  have hB0 : 0 ≤ B := by rw [hBdef]; exact Real.sqrt_nonneg _
  have hA2 : A ^ 2 = s + 1 := by rw [hAdef]; exact Real.sq_sqrt hs1
  have hB2 : B ^ 2 = c := by rw [hBdef]; exact Real.sq_sqrt hc0
  have hB1 : 1 ≤ B := by
    rw [hBdef]
    calc (1 : ℝ) = Real.sqrt 1 := by simp
      _ ≤ Real.sqrt c := Real.sqrt_le_sqrt hc
  -- the exact identity for `s·h(s)`
  have hpsi : s * (A - B) ^ 2
      = 4 * (s - c) - (A - B) ^ 2 * (1 + c + 2 * (B * A)) + (s - c - 1) ^ 2 := by
    nlinarith [hA2, hB2]
  -- the reduced claim
  have hmain : 3 * s - 4 * c ≤ (A - B) ^ 2 * (1 + c + 2 * (B * A)) := by
    by_cases h3 : 3 * s ≤ 4 * c
    · have hnn : 0 ≤ (A - B) ^ 2 * (1 + c + 2 * (B * A)) := by
        have h1 : 0 ≤ 1 + c + 2 * (B * A) := by positivity
        positivity
      linarith
    · push_neg at h3
      have hA_B : B ≤ A := by
        apply Real.sqrt_le_sqrt
        nlinarith [h3, hs]
      set p := A - B with hpdef
      have hp0 : 0 ≤ p := by rw [hpdef]; linarith
      have hBpos : 0 < B := lt_of_lt_of_le one_pos hB1
      -- `2Bp³ − 2p² + B² ≥ 0`
      have hcube : 0 ≤ 2 * (B * p) ^ 3 - 2 * (B * p) ^ 2 + 8 / 27 := by
        rw [show 2 * (B * p) ^ 3 - 2 * (B * p) ^ 2 + 8 / 27
            = 2 * (B * p - 2 / 3) ^ 2 * (B * p + 1 / 3) from by ring]
        positivity
      have hB4 : 1 ≤ B ^ 4 := by nlinarith [hB1, sq_nonneg (B ^ 2)]
      have hkey : 0 ≤ 2 * B * p ^ 3 - 2 * p ^ 2 + B ^ 2 := by
        rw [show 2 * B * p ^ 3 - 2 * p ^ 2 + B ^ 2
            = (2 * (B * p) ^ 3 - 2 * (B * p) ^ 2 + B ^ 4) / B ^ 2 from by
          rw [eq_div_iff (by positivity : B ^ 2 ≠ 0)]
          ring]
        apply div_nonneg _ (by positivity)
        linarith
      have hE : 0 ≤ 2 * B * p ^ 3 + (3 * B ^ 2 - 2) * p ^ 2 - 6 * B * p + B ^ 2 + 3 := by
        have hsplit : 2 * B * p ^ 3 + (3 * B ^ 2 - 2) * p ^ 2 - 6 * B * p + B ^ 2 + 3
            = 3 * (B * p - 1) ^ 2 + (2 * B * p ^ 3 - 2 * p ^ 2 + B ^ 2) := by ring
        rw [hsplit]
        nlinarith [hkey, sq_nonneg (B * p - 1)]
      -- identify the two sides
      have hAid : 3 * s - 4 * c = -B ^ 2 + 6 * B * p + 3 * p ^ 2 - 3 := by
        rw [hpdef]
        nlinarith [hA2, hB2]
      have hRid : (A - B) ^ 2 * (1 + c + 2 * (B * A))
          = (3 * s - 4 * c)
            + (2 * B * p ^ 3 + (3 * B ^ 2 - 2) * p ^ 2 - 6 * B * p + B ^ 2 + 3) := by
        rw [hpdef]
        nlinarith [hA2, hB2]
      linarith [hE, hAid, hRid]
  rw [hpsi]
  linarith [hmain]

end Work.BoseFixB1S
