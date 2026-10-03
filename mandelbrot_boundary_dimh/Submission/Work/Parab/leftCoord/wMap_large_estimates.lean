import Mathlib
import Submission.Work.FatouCoord.Setup
import Submission.Work.FatouCoord.Estimate.wMap_iterate_deriv_bound

/-!
# Direction-free estimates for the chart dynamics `wMap`

For a parabolic germ `f z = z + z ^ 2 h z` collected in `ParabolicBounds f h a r A A'`
the conjugate dynamics `wMap f w = -1 / f (-1 / w)` is defined for *every* `w` with
`1 / r < ‖w‖` (then `-1 / w` lies in the disc of the hypotheses) — no sign condition on
`Re w` is needed.  We extract from this the two-term asymptotic

`wMap f w = w + 1 + (1 - a) / w + O(1 / ‖w‖ ^ 2)`,  `deriv (wMap f) w = 1 + O(1 / ‖w‖ ^ 2)`,

uniformly in the direction of `w`; the first estimate `‖wMap f w - (w + 1)‖ = O(1/‖w‖)`
follows from the second one.  This is the form needed to iterate `wMap` along orbits that
leave every half-plane.
-/

namespace Work.Parab.leftCoord

open Work.FatouCoord
open scoped Topology
open Set Filter Metric Function

noncomputable section

variable {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}

/-! ## A denominator bound and the algebraic core of the expansion -/

/-- If `‖z‖ ≤ 1/4` and `‖H z‖ ≤ 2` then `‖1 + z * H z‖ ≥ 1/2`. -/
private theorem norm_one_add_mul_ge_half {z : ℂ} {H : ℂ → ℂ} (hz : ‖z‖ ≤ 1 / 4)
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

/-- The algebraic core of the expansion: if `H z = 1 + a z + e` with `‖e‖ ≤ A ‖z‖²`,
`‖H z‖ ≤ 2` and `‖z‖ ≤ 1/4`, then `H z / (1 + z H z) = 1 - (1 - a) z + O(‖z‖²)`.

Writing `D = 1 + z H z` (so `‖D‖ ≥ 1/2`) one computes exactly

`H z / D - 1 + (1 - a) z
  = ((H z - 1 - a z) * (1 - z + (1 - a) z^2) + (1 - 2 a) z^2 + (1 - a) a z^3) / D`.

The first-order terms in `z` cancel; the numerator is `O(‖z‖²)` and `‖D‖ ≥ 1/2`. -/
private theorem chartCorrection_secondOrder {H : ℂ → ℂ} {a z : ℂ} {A : ℝ} (hA : 0 ≤ A)
    (hz : ‖z‖ ≤ 1 / 4) (hclose : ‖H z - 1 - a * z‖ ≤ A * ‖z‖ ^ 2) (hbd : ‖H z‖ ≤ 2) :
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
    have h4 := norm_add_le
      ((H z - 1 - a * z) * (1 - z + (1 - a) * z ^ 2) + (1 - 2 * a) * z ^ 2)
      ((1 - a) * a * z ^ 3)
    have h5 := norm_add_le ((H z - 1 - a * z) * (1 - z + (1 - a) * z ^ 2))
      ((1 - 2 * a) * z ^ 2)
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

/-! ## The second-order expansion of `wMap` -/

/-- `wMap f w = w + 1 + (1 - a)/w + O(1/‖w‖²)`, uniformly in the direction of `w`. -/
private theorem wMap_second_order_bound (hb : ParabolicBounds f h a r A A') :
    ∃ R K : ℝ, 0 < R ∧ 1 / r < R ∧ 0 ≤ K ∧ ∀ w : ℂ, R < ‖w‖ →
      ‖wMap f w - (w + 1 + (1 - a) / w)‖ ≤ K / ‖w‖ ^ 2 := by
  refine ⟨max (1 / r) 4 + 1,
    2 * (A * (2 + ‖1 - a‖) + ‖1 - 2 * a‖ + ‖1 - a‖ * ‖a‖), ?_, ?_, ?_, ?_⟩
  · have h1 : 0 < 1 / r := one_div_pos.mpr hb.hr
    have h2 : (0 : ℝ) < max (1 / r) 4 := lt_of_lt_of_le h1 (le_max_left _ _)
    linarith
  · have h2 : (1 : ℝ) / r ≤ max (1 / r) 4 := le_max_left _ _
    linarith
  · have h1 : 0 ≤ A * (2 + ‖1 - a‖) := mul_nonneg hb.hA (by positivity)
    have h2 : 0 ≤ ‖1 - a‖ * ‖a‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    linarith [norm_nonneg (1 - 2 * a : ℂ)]
  · intro w hw
    have h4 : (4 : ℝ) ≤ ‖w‖ := by
      have h : (4 : ℝ) ≤ max (1 / r) 4 := le_max_right _ _
      linarith
    have h1r : 1 / r < ‖w‖ := by
      have h : (1 : ℝ) / r ≤ max (1 / r) 4 := le_max_left _ _
      linarith
    have hwn : 0 < ‖w‖ := by linarith
    have hw0 : w ≠ 0 := by intro h0; rw [h0] at hwn; simp at hwn
    have hz : -1 / w ∈ ball 0 r := by
      rw [mem_ball_zero_iff]; exact norm_neg_one_div_lt hb.hr hw0 h1r
    have hzn : ‖-1 / w‖ = 1 / ‖w‖ := by rw [norm_div, norm_neg, norm_one]
    have hz4 : ‖-1 / w‖ ≤ 1 / 4 := by
      rw [hzn, div_le_iff₀ hwn]; linarith
    have hfe : f (-1 / w) = (-1 / w) * (1 + (-1 / w) * h (-1 / w)) := by
      rw [hb.f_eq (-1 / w) hz]; ring
    have hmap : wMap f w = w / (1 + (-1 / w) * h (-1 / w)) := by
      rw [wMap_apply, hfe, div_mul_eq_div_div]
      congr 1
      field_simp
    rw [hmap]
    set s : ℂ := (-1 / w) * h (-1 / w) with hs
    have hws : w * s = - h (-1 / w) := by rw [hs]; field_simp
    have hsle : ‖s‖ ≤ 1 / 2 := by
      rw [hs, norm_mul]
      have h2 : ‖h (-1 / w)‖ ≤ 2 := hb.h_bound _ hz
      calc ‖-1 / w‖ * ‖h (-1 / w)‖ ≤ (1 / ‖w‖) * 2 := by
            rw [hzn]
            exact mul_le_mul_of_nonneg_left h2 (by positivity)
        _ ≤ 1 / 2 := by
            rw [div_mul_eq_mul_div, div_le_iff₀ hwn]; nlinarith
    have h1s : 1 + s ≠ 0 := by
      intro h0
      have hs1 : s = -1 := by linear_combination h0
      rw [hs1] at hsle
      norm_num at hsle
    have hsubw : w / (1 + s) - w = h (-1 / w) / (1 + s) := by
      field_simp
      have e : (-(1 / w) : ℂ) = -1 / w := by ring
      rw [e]
      linear_combination -hws
    have hkey : w / (1 + s) - (w + 1 + (1 - a) / w)
        = h (-1 / w) / (1 + s) - 1 + (1 - a) * (-1 / w) := by
      calc w / (1 + s) - (w + 1 + (1 - a) / w)
          = (w / (1 + s) - w) - 1 - (1 - a) / w := by ring
        _ = h (-1 / w) / (1 + s) - 1 - (1 - a) / w := by rw [hsubw]
        _ = h (-1 / w) / (1 + s) - 1 + (1 - a) * (-1 / w) := by ring
    rw [hkey]
    simp only [hs]
    have hcore := chartCorrection_secondOrder hb.hA hz4 (hb.h_close (-1 / w) hz)
      (hb.h_bound (-1 / w) hz)
    have hrhs : 2 * (A * (2 + ‖1 - a‖) + ‖1 - 2 * a‖ + ‖1 - a‖ * ‖a‖) * ‖-1 / w‖ ^ 2
        = 2 * (A * (2 + ‖1 - a‖) + ‖1 - 2 * a‖ + ‖1 - a‖ * ‖a‖) / ‖w‖ ^ 2 := by
      rw [hzn, div_pow, one_pow, mul_one_div]
    linarith [hcore, hrhs]

/-! ## The estimates requested by the left-coordinate construction -/

theorem wMap_large_estimates {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}
    (hb : Work.FatouCoord.ParabolicBounds f h a r A A') :
    ∃ R K : ℝ, 0 < R ∧ 1 / r < R ∧ 0 ≤ K ∧
      ∀ ζ : ℂ, R < ‖ζ‖ →
        ‖Work.FatouCoord.wMap f ζ - (ζ + 1)‖ ≤ K / ‖ζ‖ ∧
        ‖Work.FatouCoord.wMap f ζ - (ζ + 1 + (1 - a) / ζ)‖ ≤ K / ‖ζ‖ ^ 2 ∧
        ‖deriv (Work.FatouCoord.wMap f) ζ - 1‖ ≤ K / ‖ζ‖ ^ 2 := by
  obtain ⟨R₂, K₂, hR₂, hr₂, hK₂, h2⟩ := wMap_second_order_bound hb
  set K : ℝ := max (K₂ + ‖1 - a‖) (max K₂ (Work.FatouCoord.Estimate.Kderiv A')) with hK
  set R : ℝ := max R₂ (max (1 / r) 4) + 1 with hR
  have hK₂le : K₂ ≤ K := by
    rw [hK]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hKle : K₂ + ‖1 - a‖ ≤ K := by rw [hK]; exact le_max_left _ _
  have hKdle : Work.FatouCoord.Estimate.Kderiv A' ≤ K := by
    rw [hK]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hKnonneg : 0 ≤ K := by
    rw [hK]
    exact le_trans (by linarith [hK₂, norm_nonneg (1 - a : ℂ)]) (le_max_left _ _)
  refine ⟨R, K, ?_, ?_, hKnonneg, ?_⟩
  · have h1 : 0 < 1 / r := one_div_pos.mpr hb.hr
    have h2 : (0 : ℝ) < max R₂ (max (1 / r) 4) :=
      lt_of_lt_of_le h1 (le_trans (le_max_left _ _) (le_max_right _ _))
    rw [hR]; linarith
  · have h2 : (1 : ℝ) / r ≤ max R₂ (max (1 / r) 4) :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    rw [hR]; linarith
  · intro ζ hζ
    have hR₂' : R₂ < ‖ζ‖ := by
      have h : R₂ ≤ max R₂ (max (1 / r) 4) := le_max_left _ _
      rw [hR] at hζ; linarith
    have h4 : (4 : ℝ) ≤ ‖ζ‖ := by
      have h : (4 : ℝ) ≤ max R₂ (max (1 / r) 4) :=
        le_trans (le_max_right _ _) (le_max_right _ _)
      rw [hR] at hζ; linarith
    have h1r : 1 / r < ‖ζ‖ := by
      have h : (1 : ℝ) / r ≤ max R₂ (max (1 / r) 4) :=
        le_trans (le_max_left _ _) (le_max_right _ _)
      rw [hR] at hζ; linarith
    have hnorm1 : (1 : ℝ) ≤ ‖ζ‖ := by linarith
    have hnormpos : (0 : ℝ) < ‖ζ‖ := by linarith
    have h2ζ : ‖Work.FatouCoord.wMap f ζ - (ζ + 1 + (1 - a) / ζ)‖ ≤ K₂ / ‖ζ‖ ^ 2 :=
      h2 ζ hR₂'
    refine ⟨?_, ?_, ?_⟩
    · have he : Work.FatouCoord.wMap f ζ - (ζ + 1)
          = (Work.FatouCoord.wMap f ζ - (ζ + 1 + (1 - a) / ζ)) + (1 - a) / ζ := by ring
      have hA : K₂ / ‖ζ‖ ^ 2 ≤ K₂ / ‖ζ‖ := by
        have hle : (‖ζ‖ ^ 2)⁻¹ ≤ ‖ζ‖⁻¹ := inv_anti₀ hnormpos (by nlinarith)
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left hle hK₂
      have hsum : K₂ / ‖ζ‖ + ‖1 - a‖ / ‖ζ‖ = (K₂ + ‖1 - a‖) / ‖ζ‖ := by ring
      calc ‖Work.FatouCoord.wMap f ζ - (ζ + 1)‖
          = ‖(Work.FatouCoord.wMap f ζ - (ζ + 1 + (1 - a) / ζ)) + (1 - a) / ζ‖ := by
            rw [he]
        _ ≤ ‖Work.FatouCoord.wMap f ζ - (ζ + 1 + (1 - a) / ζ)‖ + ‖(1 - a) / ζ‖ :=
            norm_add_le _ _
        _ ≤ K₂ / ‖ζ‖ ^ 2 + ‖1 - a‖ / ‖ζ‖ := by
            rw [norm_div]
            exact add_le_add h2ζ le_rfl
        _ ≤ K₂ / ‖ζ‖ + ‖1 - a‖ / ‖ζ‖ := by linarith
        _ = (K₂ + ‖1 - a‖) / ‖ζ‖ := hsum
        _ ≤ K / ‖ζ‖ := div_le_div_of_nonneg_right hKle (norm_nonneg _)
    · calc ‖Work.FatouCoord.wMap f ζ - (ζ + 1 + (1 - a) / ζ)‖ ≤ K₂ / ‖ζ‖ ^ 2 := h2ζ
        _ ≤ K / ‖ζ‖ ^ 2 := div_le_div_of_nonneg_right hK₂le (by positivity)
    · have hd := Work.FatouCoord.Estimate.deriv_wMap_bound_aux hb h1r h4
      calc ‖deriv (Work.FatouCoord.wMap f) ζ - 1‖
          ≤ Work.FatouCoord.Estimate.Kderiv A' / ‖ζ‖ ^ 2 := hd
        _ ≤ K / ‖ζ‖ ^ 2 := div_le_div_of_nonneg_right hKdle (by positivity)

end

end Work.Parab.leftCoord
