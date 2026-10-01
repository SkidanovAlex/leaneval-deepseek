import Mathlib
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.XY.P3ReDecay2

set_option linter.unusedVariables false

namespace Work.ZeroFreeTables.XY

/-- **Small-`Z₂` bound.**  Under the paper's hypotheses `0 < a ≤ α ≤ 3918/1000`,
`δ, L > 0`, `δL ≥ 10000` and `|γ| ≥ δ/3` — so that `|2γL| ≥ 20000/3` is huge
compared with `α` — the quantity `14900 · Re P₃(α/(a + 2γL i))` is extremely
small.  We obtain it from the signed decay estimate `P3ReDecay2`,
`|Re P₃(α/(a+iu))| ≤ 5α²/u²`, together with the crude bound
`α/|2γL| ≤ 3918·3/(1000·20000) < 1/1000`. -/
theorem Z2Small {a α δ L γ : ℝ} (ha : 0 < a) (haα : a ≤ α) (hαle : α ≤ 3918/1000)
    (hδ : 0 < δ) (hL : 0 < L) (hδL : 10000 ≤ δ * L) (hγ : δ / 3 ≤ |γ|) :
    14900 * (Work.ZeroFreeTables.P3 ((α:ℂ) / ((a:ℂ) + (((2*γ*L:ℝ)):ℂ) * Complex.I))).re ≤ 1 := by
  have hαpos : 0 < α := lt_of_lt_of_le ha haα
  -- `|2γL| ≥ 20000/3`
  have habs : |2 * γ * L| = 2 * L * |γ| := by
    rw [abs_mul, abs_mul, abs_of_pos hL, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    ring
  have hge : (2:ℝ) * (δ/3) * L ≤ 2 * L * |γ| := by
    have h2 : (0:ℝ) ≤ 2 * L := by positivity
    have := mul_le_mul_of_nonneg_right (by linarith [hγ, hδ] : δ/3 ≤ |γ|) h2
    linarith
  have hdL : (2:ℝ)/3 * 10000 ≤ (2:ℝ)/3 * (δ*L) := by
    have := mul_le_mul_of_nonneg_left hδL (by norm_num : (0:ℝ) ≤ (2:ℝ)/3)
    linarith
  have he : (2:ℝ) * (δ/3) * L = (2:ℝ)/3 * (δ*L) := by ring
  have hu_ge : (20000:ℝ)/3 ≤ |2 * γ * L| := by linarith [habs, hge, hdL, he]
  have huα : α ≤ |2 * γ * L| := by
    have h39 : (3918:ℝ)/1000 ≤ 20000/3 := by norm_num
    linarith [hαle, hu_ge]
  have hu_pos : (0:ℝ) < |2 * γ * L| := by linarith [hu_ge]
  -- the signed decay estimate
  have hdec := Work.ZeroFreeTables.XY.P3ReDecay2 (a := a) (α := α) (u := 2*γ*L) ha haα huα
  -- numeric bound
  have hu2pos : (0:ℝ) < (2*γ*L)^2 := by
    rw [← sq_abs (2 * γ * L)]
    exact pow_pos hu_pos 2
  have hαsq : α^2 ≤ ((3918:ℝ)/1000)^2 := pow_le_pow_left₀ (le_of_lt hαpos) hαle 2
  have htsq : ((20000:ℝ)/3)^2 ≤ (2*γ*L)^2 := by
    rw [← sq_abs (2 * γ * L)]
    exact pow_le_pow_left₀ (by norm_num) hu_ge 2
  have hfin : 14900 * (5 * α^2/(2*γ*L)^2) ≤ 1 := by
    rw [show 14900 * (5 * α^2/(2*γ*L)^2) = (14900*5*α^2)/(2*γ*L)^2 by ring]
    rw [div_le_iff₀ hu2pos]
    have hc : 14900 * 5 * ((3918:ℝ)/1000)^2 ≤ ((20000:ℝ)/3)^2 := by norm_num
    nlinarith [hαsq, htsq, hc]
  calc 14900 * (Work.ZeroFreeTables.P3 ((α:ℂ) / ((a:ℂ) + (((2*γ*L:ℝ)):ℂ) * Complex.I))).re
      ≤ 14900 * |(Work.ZeroFreeTables.P3 ((α:ℂ) / ((a:ℂ) + (((2*γ*L:ℝ)):ℂ) * Complex.I))).re| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num)
    _ ≤ 14900 * (5 * α^2/(2*γ*L)^2) := mul_le_mul_of_nonneg_left hdec (by norm_num)
    _ ≤ 1 := hfin

end Work.ZeroFreeTables.XY
