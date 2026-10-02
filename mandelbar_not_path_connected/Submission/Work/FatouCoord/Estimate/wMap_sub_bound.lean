import Mathlib
import Submission.Work.FatouCoord.Setup

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouCoord.Estimate

open Work.FatouCoord
open scoped Topology
open Set Filter Metric Function

/-!
# The chart dynamics is a translation up to `O (1/w ^ 2)`

We show that for `w` in the chart with large real part,
`wMap f w = w + 1 + (1 - a)/w + O (1/w ^ 2)`.

Writing `z = -1/w` and `u = z * h z`, the chart dynamics in terms of the germ is
`wMap f w - w = h z / (1 + u)` (this is `wMap_sub_eq`), so the difference to be bounded is

`h z / (1 + z h z) - 1 + (1 - a) z`.

Writing `h z = 1 + a z + e` with `‖e‖ ≤ A ‖z‖^2`, a short computation gives

`h z / (1 + z h z) - 1 + (1 - a) z
   = (e * (1 - z + (1 - a) z^2) + (1 - 2a) z^2 + (1 - a) a z^3) / (1 + z h z)`,

and the numerator is `O (‖z‖^2) = O (1/‖w‖^2)` while the denominator is bounded below by `1/2`.
That is the content of the two auxiliary lemmas below.
-/

/-- If `‖z‖ ≤ 1/4` and `‖H z‖ ≤ 2` then `‖1 + z * H z‖ ≥ 1/2`. -/
private theorem norm_one_add_mul_ge_half {z : ℂ} {H : ℂ → ℂ} (hz : ‖z‖ ≤ 1 / 4)
    (hbd : ‖H z‖ ≤ 2) : (1 / 2 : ℝ) ≤ ‖1 + z * H z‖ := by
  have h1 : ‖z * H z‖ ≤ 1 / 2 := by
    rw [norm_mul]
    calc ‖z‖ * ‖H z‖ ≤ (1 / 4) * 2 := by
          exact mul_le_mul hz hbd (norm_nonneg _) (by norm_num)
      _ = 1 / 2 := by norm_num
  have h2 : ‖(1 : ℂ)‖ ≤ ‖1 + z * H z‖ + ‖z * H z‖ := by
    simpa using norm_sub_le (1 + z * H z) (z * H z)
  rw [norm_one] at h2
  linarith

/-- The algebraic core of the expansion: if `h z = 1 + a z + e` with `‖e‖ ≤ A ‖z‖²`, `‖h z‖ ≤ 2`
and `‖z‖ ≤ 1/4`, then `h z / (1 + z h z) = 1 - (1 - a) z + O (‖z‖²)`. -/
private theorem key_estimate {H : ℂ → ℂ} {a z : ℂ} {A : ℝ} (hA : 0 ≤ A) (hz : ‖z‖ ≤ 1 / 4)
    (hclose : ‖H z - 1 - a * z‖ ≤ A * ‖z‖ ^ 2) (hbd : ‖H z‖ ≤ 2) :
    ‖H z / (1 + z * H z) - 1 + (1 - a) * z‖
      ≤ 2 * (A * (2 + ‖1 - a‖) + ‖1 - 2 * a‖ + ‖1 - a‖ * ‖a‖) * ‖z‖ ^ 2 := by
  have hznn : 0 ≤ ‖z‖ := norm_nonneg z
  have hz1 : ‖z‖ ≤ 1 := by linarith
  have hsqnn : 0 ≤ ‖z‖ ^ 2 := sq_nonneg _
  have hsq1 : ‖z‖ ^ 2 ≤ 1 := pow_le_one₀ hznn hz1
  have hcb1 : ‖z‖ ^ 3 ≤ ‖z‖ ^ 2 := by
    rw [pow_succ]
    exact mul_le_of_le_one_right hsqnn hz1
  have hden : (1 / 2 : ℝ) ≤ ‖1 + z * H z‖ := norm_one_add_mul_ge_half hz hbd
  set D : ℂ := 1 + z * H z with hD
  have hD0 : D ≠ 0 := by
    intro h0
    rw [h0] at hden
    norm_num at hden
  have hkey : H z / D - 1 + (1 - a) * z
      = ((H z - 1 - a * z) * (1 - z + (1 - a) * z ^ 2) + (1 - 2 * a) * z ^ 2
          + (1 - a) * a * z ^ 3) / D := by
    have e1 : H z / D - 1 = (H z - D) / D := by
      rw [show (1 : ℂ) = D / D from (div_self hD0).symm]
      rw [← sub_div]
    have e2 : (1 - a) * z = ((1 - a) * z * D) / D := by
      rw [mul_div_assoc, div_self hD0, mul_one]
    rw [e1, e2, ← add_div]
    congr 1
    rw [hD]
    ring
  have hfac : ‖1 - z + (1 - a) * z ^ 2‖ ≤ 2 + ‖1 - a‖ := by
    have h2 : ‖1 - z‖ ≤ 1 + ‖z‖ := by
      simpa using norm_sub_le (1 : ℂ) z
    have h3 : ‖(1 - a) * z ^ 2‖ ≤ ‖1 - a‖ := by
      rw [norm_mul, norm_pow]
      calc ‖1 - a‖ * ‖z‖ ^ 2 ≤ ‖1 - a‖ * 1 :=
            mul_le_mul_of_nonneg_left hsq1 (norm_nonneg _)
        _ = ‖1 - a‖ := mul_one _
    linarith [norm_add_le (1 - z) ((1 - a) * z ^ 2)]
  have hterm1 : ‖(H z - 1 - a * z) * (1 - z + (1 - a) * z ^ 2)‖
      ≤ A * (2 + ‖1 - a‖) * ‖z‖ ^ 2 := by
    rw [norm_mul]
    calc ‖H z - 1 - a * z‖ * ‖1 - z + (1 - a) * z ^ 2‖
        ≤ (A * ‖z‖ ^ 2) * (2 + ‖1 - a‖) :=
          mul_le_mul hclose hfac (norm_nonneg _) (mul_nonneg hA hsqnn)
      _ = A * (2 + ‖1 - a‖) * ‖z‖ ^ 2 := by ring
  have hterm2 : ‖(1 - 2 * a) * z ^ 2‖ ≤ ‖1 - 2 * a‖ * ‖z‖ ^ 2 := by
    rw [norm_mul, norm_pow]
  have hterm3 : ‖(1 - a) * a * z ^ 3‖ ≤ ‖1 - a‖ * ‖a‖ * ‖z‖ ^ 2 := by
    rw [norm_mul, norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left hcb1 (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hN1 : ‖(H z - 1 - a * z) * (1 - z + (1 - a) * z ^ 2) + (1 - 2 * a) * z ^ 2
      + (1 - a) * a * z ^ 3‖
      ≤ (A * (2 + ‖1 - a‖) + ‖1 - 2 * a‖ + ‖1 - a‖ * ‖a‖) * ‖z‖ ^ 2 := by
    have h4 := norm_add_le ((H z - 1 - a * z) * (1 - z + (1 - a) * z ^ 2) + (1 - 2 * a) * z ^ 2)
        ((1 - a) * a * z ^ 3)
    have h5 := norm_add_le ((H z - 1 - a * z) * (1 - z + (1 - a) * z ^ 2)) ((1 - 2 * a) * z ^ 2)
    linarith [hterm1, hterm2, hterm3, h4, h5]
  rw [hkey, norm_div]
  have hKnn : 0 ≤ A * (2 + ‖1 - a‖) + ‖1 - 2 * a‖ + ‖1 - a‖ * ‖a‖ := by
    have h1 : 0 ≤ A * (2 + ‖1 - a‖) := mul_nonneg hA (by positivity)
    have h2 : 0 ≤ ‖1 - a‖ * ‖a‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    linarith [norm_nonneg (1 - 2 * a)]
  calc ‖(H z - 1 - a * z) * (1 - z + (1 - a) * z ^ 2) + (1 - 2 * a) * z ^ 2
        + (1 - a) * a * z ^ 3‖ / ‖D‖
      ≤ ((A * (2 + ‖1 - a‖) + ‖1 - 2 * a‖ + ‖1 - a‖ * ‖a‖) * ‖z‖ ^ 2) / (1 / 2) :=
        div_le_div₀ (mul_nonneg hKnn hsqnn) hN1 (by norm_num) hden
    _ = 2 * (A * (2 + ‖1 - a‖) + ‖1 - 2 * a‖ + ‖1 - a‖ * ‖a‖) * ‖z‖ ^ 2 := by ring

theorem wMap_sub_bound {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ} (hb : ParabolicBounds f h a r A A') :
    ∃ N C : ℝ, 0 < N ∧ 0 ≤ C ∧ 1 / r < N ∧ ∀ w : ℂ, N < w.re → ‖wMap f w - w - 1 - (1 - a) / w‖ ≤ C / ‖w‖ ^ 2 := by
  refine ⟨max (1 / r + 1) 5, 2 * (A * (2 + ‖1 - a‖) + ‖1 - 2 * a‖ + ‖1 - a‖ * ‖a‖), ?_, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  · have h1 : 0 ≤ A * (2 + ‖1 - a‖) := mul_nonneg hb.hA (by positivity)
    have h2 : 0 ≤ ‖1 - a‖ * ‖a‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    linarith [norm_nonneg (1 - 2 * a : ℂ)]
  · exact lt_of_lt_of_le (lt_add_one _) (le_max_left _ _)
  · intro w hw
    have hwr5 : (5 : ℝ) < w.re := lt_of_le_of_lt (le_max_right _ _) hw
    have hwr0 : 0 < w.re := lt_trans (by norm_num) hwr5
    have hwr1 : 1 / r + 1 < w.re := lt_of_le_of_lt (le_max_left _ _) hw
    have hnormw : 1 / r < ‖w‖ := by
      have h2 : 1 / r + 1 < ‖w‖ := lt_of_lt_of_le hwr1 (Complex.re_le_norm w)
      linarith
    have hw0 : w ≠ 0 := by
      intro h0
      rw [h0] at hwr0
      simp at hwr0
    have hnorm5 : (5 : ℝ) < ‖w‖ := lt_of_lt_of_le hwr5 (Complex.re_le_norm w)
    have hz_ball : -1 / w ∈ ball 0 r := by
      rw [mem_ball_zero_iff]
      exact norm_neg_one_div_lt hb.hr hw0 hnormw
    have hz4 : ‖-1 / w‖ ≤ 1 / 4 := by
      have hn : ‖-1 / w‖ = (‖w‖)⁻¹ := by rw [norm_div, norm_neg, norm_one, one_div]
      rw [hn]
      have hlt : (‖w‖)⁻¹ < (5 : ℝ)⁻¹ := by
        simpa [one_div] using one_div_lt_one_div_of_lt (show (0 : ℝ) < 5 by norm_num) hnorm5
      have h54 : (5 : ℝ)⁻¹ ≤ 1 / 4 := by norm_num
      linarith
    have hclose : ‖h (-1 / w) - 1 - a * (-1 / w)‖ ≤ A * ‖-1 / w‖ ^ 2 := hb.h_close _ hz_ball
    have hbd : ‖h (-1 / w)‖ ≤ 2 := hb.h_bound _ hz_ball
    have hhalf := norm_one_add_mul_ge_half hz4 hbd
    have hden0 : 1 + (-1 / w) * h (-1 / w) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hhalf
      linarith
    have hsub := wMap_sub_eq hb.hr hb.f_eq hwr0 hnormw hden0
    have hge := key_estimate hb.hA hz4 hclose hbd
    have hCeq : 2 * (A * (2 + ‖1 - a‖) + ‖1 - 2 * a‖ + ‖1 - a‖ * ‖a‖) * ‖-1 / w‖ ^ 2
        = 2 * (A * (2 + ‖1 - a‖) + ‖1 - 2 * a‖ + ‖1 - a‖ * ‖a‖) / ‖w‖ ^ 2 := by
      rw [norm_div, norm_neg, norm_one, one_div, inv_pow, div_eq_mul_inv]
    have heq : h (-1 / w) / (1 + (-1 / w) * h (-1 / w)) - 1 + (1 - a) * (-1 / w)
        = h (-1 / w) / (1 + (-1 / w) * h (-1 / w)) - 1 - (1 - a) / w := by ring
    rw [heq, hCeq] at hge
    rw [hsub]
    exact hge

end Work.FatouCoord.Estimate
