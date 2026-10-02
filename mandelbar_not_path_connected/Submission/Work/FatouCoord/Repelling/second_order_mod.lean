import Mathlib
import Submission.Work.FatouCoord.Setup
import Submission.Work.FatouCoord.Estimate.wMap_iterate_deriv_bound

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The chart dynamics is a translation by `1` up to `O(1/w^2)`, uniformly in the phase

The companion file `Estimate/wMap_sub_bound` proves
`wMap f w = w + 1 + (1 - a)/w + O(‖w‖ ^ (-2))` under the hypothesis `N < w.re` for a large
level `N`.  Here we prove the *phase-independent* version: the same estimate holds for every
`w` with `‖w‖ > 1/r` and `‖w‖ ≥ 4`, with no restriction on the argument of `w`.

This is what the repelling-petal arguments need, since on the repelling side the points of
interest may have large modulus but real part of either sign.

The proof is a direct computation in the chart.  Writing `z = -1/w` and `u = z * h z`, the
chart dynamics in terms of the germ is `wMap f w - w = h z / (1 + u)` (here `wMap_sub_eq`
generalised to the hypothesis `w ≠ 0`), so the difference to be bounded is

`h z / (1 + z h z) - 1 + (1 - a) z`

Writing `h z = 1 + a z + e` with `‖e‖ ≤ A ‖z‖^2`, a computation gives

`h z / (1 + z h z) - 1 + (1 - a) z
   = (e * (1 - z + (1 - a) z ^ 2) + (1 - 2a) z ^ 2 + (1 - a) a z ^ 3) / (1 + z h z)`,

whose numerator is `O(‖z‖^2) = O(1/‖w‖^2)` and whose denominator is bounded below by `1/2`.
-/

open scoped Topology
open Set Filter Metric Function

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace Work.FatouCoord.Repelling

open Work.FatouCoord

noncomputable section

variable {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ} {z w : ℂ}

/-! ## Chart identities without the real-part hypothesis -/

/-- `Work.FatouCoord.wMap_eq` with `0 < w.re` weakened to `w ≠ 0` (which is all its proof
uses, and which is available from `1 / r < ‖w‖` and `0 < r`). -/
theorem wMap_eq_ne {r : ℝ} (hr : 0 < r) (hf : ∀ z ∈ ball 0 r, f z = z + z ^ 2 * h z) {w : ℂ}
    (hw0 : w ≠ 0) (hN : 1 / r < ‖w‖) : wMap f w = w / (1 + (-1 / w) * h (-1 / w)) := by
  have hz : -1 / w ∈ ball 0 r := by
    simpa [mem_ball_zero_iff] using norm_neg_one_div_lt hr hw0 hN
  have hzw : -1 / (-1 / w) = w := by field_simp
  have h1 : f (-1 / w) = (-1 / w) * (1 + (-1 / w) * h (-1 / w)) := by
    rw [hf (-1 / w) hz]; ring
  simp only [wMap, chart]
  rw [h1, div_mul_eq_div_div, hzw]

/-- `Work.FatouCoord.wMap_sub_eq` with `0 < w.re` weakened to `w ≠ 0`. -/
theorem wMap_sub_eq_ne {r : ℝ} (hr : 0 < r) (hf : ∀ z ∈ ball 0 r, f z = z + z ^ 2 * h z)
    {w : ℂ} (hw0 : w ≠ 0) (hN : 1 / r < ‖w‖) (hne : 1 + (-1 / w) * h (-1 / w) ≠ 0) :
    wMap f w - w = h (-1 / w) / (1 + (-1 / w) * h (-1 / w)) := by
  have key : w * ((-1 / w) * h (-1 / w)) = -h (-1 / w) := by field_simp
  have hsub : (wMap f w - w) * (1 + (-1 / w) * h (-1 / w)) = h (-1 / w) := by
    rw [wMap_eq_ne hr hf hw0 hN, sub_mul, div_mul_cancel₀ _ hne]
    rw [show w - w * (1 + (-1 / w) * h (-1 / w))
        = -(w * ((-1 / w) * h (-1 / w))) by ring, key, neg_neg]
  calc wMap f w - w
      = ((wMap f w - w) * (1 + (-1 / w) * h (-1 / w))) / (1 + (-1 / w) * h (-1 / w)) :=
        (mul_div_cancel_right₀ _ hne).symm
    _ = h (-1 / w) / (1 + (-1 / w) * h (-1 / w)) := by rw [hsub]

/-! ## The algebraic expansion -/

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
and `‖z‖ ≤ 1/4`, then `h z / (1 + z h z) = 1 - (1 - a) z + O(‖z‖²)`. -/
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

/-! ## The main theorem -/

theorem second_order_mod {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ} (hb : ParabolicBounds f h a r A A') :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℂ, 1 / r < ‖x‖ → 4 ≤ ‖x‖ → ‖wMap f x - x - 1 - (1 - a) / x‖ ≤ K / ‖x‖ ^ 2 := by
  refine ⟨2 * (A * (2 + ‖1 - a‖) + ‖1 - 2 * a‖ + ‖1 - a‖ * ‖a‖), ?_, ?_⟩
  · have h1 : 0 ≤ A * (2 + ‖1 - a‖) := mul_nonneg hb.hA (by positivity)
    have h2 : 0 ≤ ‖1 - a‖ * ‖a‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    linarith [norm_nonneg (1 - 2 * a : ℂ)]
  · intro x hx hx4
    have hnw : 0 < ‖x‖ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4) hx4
    have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hnw)
    have hz_ball : -1 / x ∈ ball 0 r := by
      rw [mem_ball_zero_iff]
      exact norm_neg_one_div_lt hb.hr hx0 hx
    have hz4 : ‖-1 / x‖ ≤ 1 / 4 := by
      rw [norm_div, norm_neg, norm_one]
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) hx4
    have hclose : ‖h (-1 / x) - 1 - a * (-1 / x)‖ ≤ A * ‖-1 / x‖ ^ 2 := hb.h_close _ hz_ball
    have hbd : ‖h (-1 / x)‖ ≤ 2 := hb.h_bound _ hz_ball
    have hhalf := norm_one_add_mul_ge_half hz4 hbd
    have hden0 : 1 + (-1 / x) * h (-1 / x) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hhalf
      linarith
    have hsub := wMap_sub_eq_ne hb.hr hb.f_eq hx0 hx hden0
    have hge := key_estimate hb.hA hz4 hclose hbd
    have hCeq : 2 * (A * (2 + ‖1 - a‖) + ‖1 - 2 * a‖ + ‖1 - a‖ * ‖a‖) * ‖-1 / x‖ ^ 2
        = 2 * (A * (2 + ‖1 - a‖) + ‖1 - 2 * a‖ + ‖1 - a‖ * ‖a‖) / ‖x‖ ^ 2 := by
      rw [norm_div, norm_neg, norm_one, one_div, inv_pow, div_eq_mul_inv]
    have heq : h (-1 / x) / (1 + (-1 / x) * h (-1 / x)) - 1 + (1 - a) * (-1 / x)
        = h (-1 / x) / (1 + (-1 / x) * h (-1 / x)) - 1 - (1 - a) / x := by ring
    rw [heq, hCeq] at hge
    rw [hsub]
    exact hge

end

end Work.FatouCoord.Repelling
