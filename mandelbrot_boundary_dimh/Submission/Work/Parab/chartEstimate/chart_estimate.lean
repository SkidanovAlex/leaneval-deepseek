import Mathlib
import Submission.Work.FatouCoord.Setup
import Submission.Work.FatouCoord.Estimate.wMap_sub_bound
import Submission.Work.FatouCoord.Estimate.coordError_deriv_bound
import Submission.Work.Parab.chartEstimate.wMap_deriv_bound

namespace Work.Parab.chartEstimate

open Work.FatouCoord
open scoped Topology
open Set Filter Metric Function

set_option linter.unusedVariables false

variable {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ} {w z : ℂ}

/-! ## The chart dynamics in terms of the germ, without a sign condition on `Re w`

The library lemmas `wMap_eq`, `wMap_sub_eq` are stated with the hypothesis `0 < w.re`, but
that hypothesis is only used to know `w ≠ 0`.  Since a large modulus of `w` already forces
`w ≠ 0` and `-1/w ∈ ball 0 r`, both lemmas hold with `w.re > 0` weakened to `w ≠ 0`. -/

/-- The chart dynamics in terms of the germ, with a modulus hypothesis. -/
theorem wMap_eq_norm (hr : 0 < r) (hf : ∀ z ∈ ball 0 r, f z = z + z ^ 2 * h z) {w : ℂ}
    (hw0 : w ≠ 0) (hN : 1 / r < ‖w‖) :
    wMap f w = w / (1 + (-1 / w) * h (-1 / w)) := by
  have hz : -1 / w ∈ ball 0 r := by
    simpa [mem_ball_zero_iff] using norm_neg_one_div_lt hr hw0 hN
  have hzw : -1 / (-1 / w) = w := by field_simp
  have h1 : f (-1 / w) = (-1 / w) * (1 + (-1 / w) * h (-1 / w)) := by
    rw [hf (-1 / w) hz]; ring
  simp only [wMap, chart]
  rw [h1, div_mul_eq_div_div, hzw]

/-- The "defect" `wMap f w - w` of the pull-back from being a translation, with a modulus
hypothesis. -/
theorem wMap_sub_eq_norm (hr : 0 < r) (hf : ∀ z ∈ ball 0 r, f z = z + z ^ 2 * h z) {w : ℂ}
    (hw0 : w ≠ 0) (hN : 1 / r < ‖w‖) (hne : 1 + (-1 / w) * h (-1 / w) ≠ 0) :
    wMap f w - w = h (-1 / w) / (1 + (-1 / w) * h (-1 / w)) := by
  have key : w * ((-1 / w) * h (-1 / w)) = -h (-1 / w) := by field_simp
  have hsub : (wMap f w - w) * (1 + (-1 / w) * h (-1 / w)) = h (-1 / w) := by
    rw [wMap_eq_norm hr hf hw0 hN, sub_mul, div_mul_cancel₀ _ hne]
    rw [show w - w * (1 + (-1 / w) * h (-1 / w))
        = -(w * ((-1 / w) * h (-1 / w))) by ring, key, neg_neg]
  calc wMap f w - w
      = ((wMap f w - w) * (1 + (-1 / w) * h (-1 / w))) / (1 + (-1 / w) * h (-1 / w)) :=
        (mul_div_cancel_right₀ _ hne).symm
    _ = h (-1 / w) / (1 + (-1 / w) * h (-1 / w)) := by rw [hsub]

/-- If `‖z‖ ≤ 1/4` and `‖H z‖ ≤ 2` then `‖1 + z * H z‖ ≥ 1/2`. -/
theorem norm_one_add_mul_ge_half {z : ℂ} {H : ℂ → ℂ} (hz : ‖z‖ ≤ 1 / 4)
    (hbd : ‖H z‖ ≤ 2) : (1 / 2 : ℝ) ≤ ‖1 + z * H z‖ := by
  have h1 : ‖z * H z‖ ≤ 1 / 2 := by
    rw [norm_mul]
    calc ‖z‖ * ‖H z‖ ≤ (1 / 4) * 2 :=
          mul_le_mul hz hbd (norm_nonneg _) (by norm_num)
      _ = 1 / 2 := by norm_num
  have h2 : ‖(1 : ℂ)‖ ≤ ‖1 + z * H z‖ + ‖z * H z‖ := by
    simpa using norm_sub_le (1 + z * H z) (z * H z)
  rw [norm_one] at h2
  linarith

/-! ## The value estimate -/

/-- `wMap f w = w + 1 + O(1/w)` uniformly in the direction of `w`. -/
theorem wMap_value_bound (hb : ParabolicBounds f h a r A A') {w : ℂ}
    (hw : max (1 / r + 1) 5 < ‖w‖) :
    ‖wMap f w - w - 1‖ ≤ 2 * (A + ‖a‖ + 2) / ‖w‖ := by
  have hNr : 1 / r < ‖w‖ := by
    have h1 : (1 : ℝ) / r < max (1 / r + 1) 5 :=
      lt_of_lt_of_le (by linarith) (le_max_left _ _)
    linarith
  have h5 : (5 : ℝ) < ‖w‖ := lt_of_le_of_lt (le_max_right (1 / r + 1) (5 : ℝ)) hw
  have hwn : 0 < ‖w‖ := by linarith
  have hw0 : w ≠ 0 := by intro h0; rw [h0] at hwn; simp at hwn
  have hz : -1 / w ∈ ball 0 r := by
    rw [mem_ball_zero_iff]; exact norm_neg_one_div_lt hb.hr hw0 hNr
  have hzn : ‖-1 / w‖ = 1 / ‖w‖ := by rw [norm_div, norm_neg, norm_one]
  have hz4 : ‖-1 / w‖ ≤ 1 / 4 := by
    rw [hzn, div_le_iff₀ hwn]; linarith
  have hbd : ‖h (-1 / w)‖ ≤ 2 := hb.h_bound _ hz
  have hhalf := norm_one_add_mul_ge_half hz4 hbd
  have hDne : 1 + (-1 / w) * h (-1 / w) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hhalf; linarith
  have hsub := wMap_sub_eq_norm hb.hr hb.f_eq hw0 hNr hDne
  have hval : wMap f w - w - 1
      = (h (-1 / w) - 1 - (-1 / w) * h (-1 / w)) / (1 + (-1 / w) * h (-1 / w)) := by
    rw [hsub, div_sub' hDne]
    congr 1
    ring
  have hsq : ‖-1 / w‖ ^ 2 ≤ ‖-1 / w‖ := by
    have h1 : ‖-1 / w‖ ≤ 1 := by linarith
    nlinarith [norm_nonneg (-1 / w : ℂ)]
  have h1 : ‖h (-1 / w) - 1‖ ≤ A * ‖-1 / w‖ + ‖a‖ * ‖-1 / w‖ := by
    have hcl := hb.h_close (-1 / w) hz
    have heq : h (-1 / w) - 1 = (h (-1 / w) - 1 - a * (-1 / w)) + a * (-1 / w) := by ring
    have hA2 : A * ‖-1 / w‖ ^ 2 ≤ A * ‖-1 / w‖ := mul_le_mul_of_nonneg_left hsq hb.hA
    rw [heq]
    calc ‖(h (-1 / w) - 1 - a * (-1 / w)) + a * (-1 / w)‖
        ≤ ‖h (-1 / w) - 1 - a * (-1 / w)‖ + ‖a * (-1 / w)‖ := norm_add_le _ _
      _ ≤ A * ‖-1 / w‖ ^ 2 + ‖a‖ * ‖-1 / w‖ := by rw [norm_mul]; linarith
      _ ≤ A * ‖-1 / w‖ + ‖a‖ * ‖-1 / w‖ := by linarith
  have h3 : ‖(-1 / w) * h (-1 / w)‖ ≤ 2 * ‖-1 / w‖ := by
    calc ‖(-1 / w) * h (-1 / w)‖ = ‖-1 / w‖ * ‖h (-1 / w)‖ := norm_mul _ _
      _ ≤ ‖-1 / w‖ * 2 := mul_le_mul_of_nonneg_left hbd (norm_nonneg _)
      _ = 2 * ‖-1 / w‖ := by ring
  have hnum : ‖h (-1 / w) - 1 - (-1 / w) * h (-1 / w)‖ ≤ (A + ‖a‖ + 2) * ‖-1 / w‖ := by
    calc ‖h (-1 / w) - 1 - (-1 / w) * h (-1 / w)‖
        = ‖(h (-1 / w) - 1) - (-1 / w) * h (-1 / w)‖ := rfl
      _ ≤ ‖h (-1 / w) - 1‖ + ‖(-1 / w) * h (-1 / w)‖ := norm_sub_le _ _
      _ ≤ (A * ‖-1 / w‖ + ‖a‖ * ‖-1 / w‖) + 2 * ‖-1 / w‖ := by linarith
      _ = (A + ‖a‖ + 2) * ‖-1 / w‖ := by ring
  rw [hval, norm_div]
  calc ‖h (-1 / w) - 1 - (-1 / w) * h (-1 / w)‖ / ‖1 + (-1 / w) * h (-1 / w)‖
      ≤ ((A + ‖a‖ + 2) * ‖-1 / w‖) / (1 / 2) :=
        div_le_div₀ (mul_nonneg (by linarith [hb.hA, norm_nonneg a]) (norm_nonneg _)) hnum
          (by norm_num) hhalf
    _ = 2 * (A + ‖a‖ + 2) / ‖w‖ := by rw [hzn]; ring

/-! ## Assembly -/

theorem chart_estimate {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}
    (hb : Work.FatouCoord.ParabolicBounds f h a r A A') :
    ∃ N K : ℝ, 0 < N ∧ 1 / r < N ∧ 0 ≤ K ∧
      ∀ ζ : ℂ, N < ‖ζ‖ → ‖Work.FatouCoord.wMap f ζ - (ζ + 1)‖ ≤ K / ‖ζ‖ ∧
        ‖deriv (Work.FatouCoord.wMap f) ζ - 1‖ ≤ K / ‖ζ‖ ^ 2 := by
  have hC1 : (0 : ℝ) ≤ 2 * (A + ‖a‖ + 2) := by nlinarith [hb.hA, norm_nonneg a]
  have hC2 : (0 : ℝ) ≤ 4 * (A' + 4) := by nlinarith [hb.hA']
  refine ⟨max (1 / r + 1) 5, max (2 * (A + ‖a‖ + 2)) (4 * (A' + 4)), ?_, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le (by have := one_div_pos.mpr hb.hr; linarith) (le_max_left _ _)
  · exact lt_of_lt_of_le (lt_add_one _) (le_max_left _ _)
  · exact le_trans hC1 (le_max_left _ _)
  · intro ζ hζ
    have h5 : (5 : ℝ) < ‖ζ‖ := lt_of_le_of_lt (le_max_right (1 / r + 1) (5 : ℝ)) hζ
    have hnorm1 : (1 : ℝ) ≤ ‖ζ‖ := by linarith
    have hv := wMap_value_bound hb hζ
    have hd : ‖deriv (Work.FatouCoord.wMap f) ζ - 1‖ ≤ 4 * (A' + 4) / ‖ζ‖ ^ 2 :=
      wMap_deriv_bound hb hζ
    have hK1 : 2 * (A + ‖a‖ + 2) ≤ max (2 * (A + ‖a‖ + 2)) (4 * (A' + 4)) := le_max_left _ _
    have hK2 : 4 * (A' + 4) ≤ max (2 * (A + ‖a‖ + 2)) (4 * (A' + 4)) := le_max_right _ _
    constructor
    · calc ‖Work.FatouCoord.wMap f ζ - (ζ + 1)‖ = ‖Work.FatouCoord.wMap f ζ - ζ - 1‖ := by
            rw [show Work.FatouCoord.wMap f ζ - (ζ + 1) = Work.FatouCoord.wMap f ζ - ζ - 1
                by ring]
        _ ≤ 2 * (A + ‖a‖ + 2) / ‖ζ‖ := hv
        _ ≤ max (2 * (A + ‖a‖ + 2)) (4 * (A' + 4)) / ‖ζ‖ := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_right hK1 (inv_nonneg.mpr (norm_nonneg ζ))
    · have hstep2 : 4 * (A' + 4) / ‖ζ‖ ^ 2
          ≤ max (2 * (A + ‖a‖ + 2)) (4 * (A' + 4)) / ‖ζ‖ ^ 2 := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right hK2 (inv_nonneg.mpr (by positivity))
      exact le_trans hd hstep2

end Work.Parab.chartEstimate
