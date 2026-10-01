/-
# ZeroFreeTables/XY/Z4Small

The `4`-frequency (i.e. `t = 4γL`) instance of the elementary decay estimate for
`Re P₃` needed by the XY-engine of the order-2 `λ₁`-estimate.

With `P₃(X) = X + X² + (2/3)X³` and the hypotheses
`0 < a ≤ α ≤ 3918/1000`, `0 < δ`, `0 < L`, `10000 ≤ δL`, `δ/5 ≤ |γ|` the claim is

  `1250 · Re P₃(α/(a + 4γL·i)) ≤ 1`.

The argument is a single application of `XY.P3ReDecay2`,
`|Re P₃(α/(a+iu))| ≤ 5α²/u²` for `0 < a ≤ α ≤ |u|`, at `u = 4γL`.  The hypotheses
give `|γ| L ≥ δL/5 ≥ 2000`, hence `|4γL| = 4|γ|L ≥ 8000 ≥ 3918/1000 ≥ α`, so the
decay estimate applies; it remains to see that
`1250 · 5α²/(4γL)² = 6250 α²/(16 γ²L²) ≤ 1`, i.e. `6250 α² ≤ (4γL)²`, which follows
from `α ≤ 4` and `|4γL| ≥ 8000` (`6250 · 16 = 10⁵ < 6.4 · 10⁷ = 8000²`).
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.XY.P3ReDecay2

namespace Work.ZeroFreeTables.XY

/-- **The `t = 4γL` decay instance.**  For `0 < a ≤ α ≤ 3918/1000`, `0 < δ`, `0 < L`,
`10000 ≤ δL` and `δ/5 ≤ |γ|` one has `1250 · Re P₃(α/(a + 4γL·i)) ≤ 1`. -/
theorem Z4Small {a α δ L γ : ℝ} (ha : 0 < a) (haα : a ≤ α) (hαle : α ≤ 3918/1000)
    (hδ : 0 < δ) (hL : 0 < L) (hδL : 10000 ≤ δ * L) (hγ : δ / 5 ≤ |γ|) :
    1250 * (Work.ZeroFreeTables.P3 ((α:ℂ) / ((a:ℂ) + (((4*γ*L:ℝ)):ℂ) * Complex.I))).re ≤ 1 := by
  have hα0 : 0 ≤ α := le_of_lt (lt_of_lt_of_le ha haα)
  -- `|γ| L ≥ δ L / 5 ≥ 2000`
  have hδ5 : 0 < δ / 5 := by linarith
  have hγL : 2000 ≤ |γ| * L := by
    have h1 : δ / 5 * L ≤ |γ| * L := mul_le_mul_of_nonneg_right hγ (le_of_lt hL)
    have h2 : δ / 5 * L = δ * L / 5 := by ring
    linarith
  have habs : |4 * γ * L| = 4 * |γ| * L := by
    rw [abs_mul, abs_mul, abs_of_pos hL, abs_of_pos (show (0:ℝ) < 4 by norm_num)]
  have h8000 : 8000 ≤ |4 * γ * L| := by rw [habs]; linarith
  -- the decay estimate applies since `α ≤ 3918/1000 ≤ 4 ≤ |4γL|`
  have hαΔ : α ≤ |4 * γ * L| := by
    have hα4 : α ≤ 4 := by linarith
    linarith
  have hdec := P3ReDecay2 ha haα hαΔ
  have hle : (Work.ZeroFreeTables.P3 ((α:ℂ) / ((a:ℂ) + (((4*γ*L:ℝ)):ℂ) * Complex.I))).re
      ≤ 5 * α^2 / (4*γ*L)^2 := le_trans (le_abs_self _) hdec
  have hne : (4*γ*L) ≠ 0 := by
    intro h
    rw [h] at h8000
    norm_num at h8000
  have hu2 : 0 < (4 * γ * L)^2 := sq_pos_of_ne_zero hne
  -- `6250 α² ≤ (4γL)²`, the whole numerical content
  have hkey : 6250 * α^2 ≤ (4*γ*L)^2 := by
    rw [← sq_abs (4*γ*L)]
    have hα4 : α ≤ 4 := by linarith
    nlinarith [h8000, hα0, hα4]
  have hfin : 1250 * (5 * α^2 / (4*γ*L)^2) ≤ 1 := by
    have h : 6250 * α^2 / (4*γ*L)^2 ≤ 1 := by
      rw [div_le_one hu2]
      exact hkey
    calc 1250 * (5 * α^2 / (4*γ*L)^2) = 6250 * α^2 / (4*γ*L)^2 := by ring
      _ ≤ 1 := h
  calc 1250 * (Work.ZeroFreeTables.P3 ((α:ℂ) / ((a:ℂ) + (((4*γ*L:ℝ)):ℂ) * Complex.I))).re
      ≤ 1250 * (5 * α^2 / (4*γ*L)^2) := mul_le_mul_of_nonneg_left hle (by norm_num)
    _ ≤ 1 := hfin

end Work.ZeroFreeTables.XY
