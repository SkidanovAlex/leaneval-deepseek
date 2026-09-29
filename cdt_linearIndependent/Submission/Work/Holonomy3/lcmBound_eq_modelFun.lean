import Mathlib
import Submission.Work.Holonomy3.model_deps
import Submission.Work.Holonomy3.modelFun_eq_H

namespace Work.Holonomy3

/-- Floor computation underlying Lemma `lcm-2` (2) at `k = D`, `l`:
`⌊(n/D - 1)/max 1 (l/D)⌋ = (n - D)/max D l` for `D ≤ n`, `0 < D`.

Indeed `n/D - 1 = (n-D)/D`, and the denominator is `1` when `l ≤ D`, `l/D` when `D ≤ l`;
in the first case the quotient is `(n-D)/D`, in the second `(n-D)/l`. -/
lemma floor_div_max_cast_lcm2 {n D l : ℕ} (hn : D ≤ n) (hD : 0 < D) :
    ⌊((n:ℝ)/D - 1)/max 1 ((l:ℝ)/D)⌋₊ = (n - D)/max D l := by
  have hDn : (0:ℝ) < D := by exact_mod_cast hD
  have hsub : (n:ℝ)/D - 1 = ((n - D : ℕ) : ℝ)/D := by
    rw [eq_div_iff (ne_of_gt hDn), sub_mul, div_mul_cancel₀ _ (ne_of_gt hDn), one_mul,
      Nat.cast_sub hn]
  rw [hsub]
  rcases le_total l D with hl | hl
  · have hmax1 : max 1 ((l:ℝ)/D) = 1 := by
      rw [max_eq_left]
      rw [div_le_one hDn]; exact_mod_cast hl
    rw [hmax1, div_one, max_eq_left hl, Nat.floor_div_natCast, Nat.floor_natCast]
  · have hmax1 : max 1 ((l:ℝ)/D) = (l:ℝ)/D := by
      rw [max_eq_right]
      rw [le_div_iff₀ hDn, one_mul]; exact_mod_cast hl
    have hl0 : (l:ℝ) ≠ 0 := by
      have : 0 < l := lt_of_lt_of_le hD hl
      exact_mod_cast ne_of_gt this
    have hdiv : (((n - D : ℕ) : ℝ)/D)/((l:ℝ)/D) = ((n - D : ℕ) : ℝ)/l := by
      field_simp
    rw [hmax1, max_eq_right hl, hdiv, Nat.floor_div_natCast, Nat.floor_natCast]

/-- The denominator `b = (n + (l - D))/max D l` of the paper's Lemma `lcm-2` (2) at `k = D`
equals `a + 1` where `a = (n - D)/max D l` (for `D ≤ n`, `0 < D`).

If `l ≤ D` then `max D l = D`, `l - D = 0`, and `n/D = (n-D)/D + 1`; if `D ≤ l` then
`max D l = l` and `n + (l-D) = (n-D) + l`, so `(n + (l-D))/l = (n-D)/l + 1`. -/
lemma nat_add_sub_div_max_lcm2 {n D l : ℕ} (hn : D ≤ n) (hD : 0 < D) :
    (n + (l - D))/max D l = (n - D)/max D l + 1 := by
  rcases le_total l D with hl | hl
  · have hmax : max D l = D := max_eq_left hl
    rw [hmax, Nat.sub_eq_zero_of_le hl, Nat.add_zero,
      ← Nat.add_div_right (n - D) hD, Nat.sub_add_cancel hn]
  · have hmax : max D l = l := max_eq_right hl
    have hl0 : 0 < l := lt_of_lt_of_le hD hl
    have h1 : n + (l - D) = (n - D) + l := by omega
    rw [hmax, h1, Nat.add_div_right (n - D) hl0]

/-- The right-hand side of the paper's Lemma `lcm-2` (2) at `k = D`, `l = ⌊ξD⌋` is exactly
`D` times the model function with parameter `⌊ξD⌋/D` evaluated at `n/D`.

Write `l := ⌊ξ*D⌋₊`, `M := max D l`, `a := (n-D)/M`, `b := (n + (l-D))/M` (truncated
subtraction `l - D`).  One has `b = a+1`: if `l ≤ D` then `M = D`, `a = n/D - 1`, `b = n/D`;
if `D ≤ l` then `M = l` and `n + (l-D) = (n-D) + l` gives `b = (n-D)/l + 1 = a+1`.
Also `⌊(n/D - 1)/max 1 (l/D)⌋ = a`: in the case `l ≤ D` we have `max 1 (l/D) = 1` and
`a = n/D - 1`; in the case `D ≤ l` we have `max 1 (l/D) = l/D` and the quotient is
`(n-D)/l`.  Then use the sibling lemma `modelFun_eq_H` (in
`Submission.Work.Holonomy3.modelFun_eq_H`; it provides both
`modelFun_eq_H : modelFun w t = H ⌊(t-1)/max 1 w⌋ + (t/(⌊(t-1)/max 1 w⌋+1) - w)⁺` for
`0 ≤ w`, `1 ≤ t`, and the floor identity `floor_div_max_eq`) to rewrite
`modelFun (l/D) (n/D)`, and note that for `D > 0`
`D * (n/(D*(a+1)) - l/D)⁺ = (n/(a+1) - l)⁺`. -/
theorem lcmBound_eq_modelFun (D : ℕ) (hD : 1 ≤ D) (ξ : ℝ) (hξ0 : 0 ≤ ξ) {n : ℕ} (hn : D ≤ n) :
    (D : ℝ) * Submission.CDT.Lcm2Bound.H ((n - D) / max D ⌊ξ * D⌋₊)
      + max ((n : ℝ) / (((n + (⌊ξ * D⌋₊ - D)) / max D ⌊ξ * D⌋₊ : ℕ) : ℝ) - (⌊ξ * D⌋₊ : ℝ)) 0
    = (D : ℝ) * Submission.CDT.IntegratedLcm.modelFun ((⌊ξ * D⌋₊ : ℝ) / (D : ℝ)) ((n : ℝ) / (D : ℝ)) := by
  have hD0 : (0:ℝ) < D := by exact_mod_cast hD
  have hDpos : 0 < D := hD
  have hnD : (1:ℝ) ≤ (n:ℝ)/D := by
    rw [le_div_iff₀ hD0, one_mul]; exact_mod_cast hn
  have hw : (0:ℝ) ≤ (⌊ξ * D⌋₊ : ℝ)/D := div_nonneg (by positivity) (le_of_lt hD0)
  rw [modelFun_eq_H ((⌊ξ * D⌋₊ : ℝ)/(D:ℝ)) hw ((n:ℝ)/D) hnD]
  have hfloor := floor_div_max_cast_lcm2 (l := ⌊ξ * D⌋₊) hn hDpos
  have hb := nat_add_sub_div_max_lcm2 (l := ⌊ξ * D⌋₊) hn hDpos
  rw [hfloor, hb, mul_add]
  congr 1
  rw [mul_max_of_nonneg _ _ (le_of_lt hD0), mul_zero]
  congr 1
  field_simp

end Work.Holonomy3
