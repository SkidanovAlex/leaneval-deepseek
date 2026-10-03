import Mathlib
import Submission.Work.Pert.RatioBasic

/-!
# `Work.Pert.ratio_sub_ratio_le`

Elementary perturbation estimate behind Shishikura's §4.2/(A.4) comparison of the model
quantity `u / (1 + t * u)` at `(u, t) = (ut, t)` with the datum `h0 / (1 + t0 * h0)`.

The proof splits the difference at the two intermediate quantities `ut / (1 + t * ut)` and
`ut / (1 + t0 * ut)`, which gives three completely explicit estimates
(`ratio_piece1_u0`, `ratio_piece2_t`, `ratio_piece3_h0`).
-/

namespace Work.Pert

set_option linter.unusedVariables false

/-- Piece 1: replacing the factor `u0` by `1` costs at most `4 η`, using `‖u0‖ ≥ 1/2` and
`‖u0 - 1‖ ≤ η` (and `‖t‖ ≤ 1/16`, `‖ut‖ ≤ 3/2 + η` to keep the denominator `1 + t * ut`
away from `0`). -/
theorem ratio_piece1_u0 {u0 ut t : ℂ} {η : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1 / 1000) (hu0 : 1 / 2 ≤ ‖u0‖) (hu0' : ‖u0 - 1‖ ≤ η)
    (ht : ‖t‖ ≤ 1 / 16) (hut : ‖ut‖ ≤ 3 / 2 + η) :
    ‖ut / (u0 * (1 + t * ut)) - ut / (1 + t * ut)‖ ≤ 4 * η := by
  have hηnn : (0 : ℝ) ≤ η := hη.le
  have hu0ne : u0 ≠ 0 := by
    intro h; rw [h, norm_zero] at hu0; norm_num at hu0
  have hWlb : 9 / 10 ≤ ‖1 + t * ut‖ := by
    refine le_norm_one_add ?_
    calc ‖t * ut‖ = ‖t‖ * ‖ut‖ := norm_mul t ut
      _ ≤ (1 / 16) * (3 / 2 + η) := mul_le_mul ht hut (norm_nonneg _) (by norm_num)
      _ ≤ (1 / 16) * (3 / 2 + 1 / 1000) := by nlinarith [hη1]
      _ ≤ 1 - 9 / 10 := by norm_num
  have hWne : (1 + t * ut) ≠ 0 := by
    intro h; rw [h, norm_zero] at hWlb; norm_num at hWlb
  have h1u : ‖1 - u0‖ ≤ η := by
    have : (1 : ℂ) - u0 = -(u0 - 1) := by ring
    rw [this, norm_neg]; exact hu0'
  have hid : ut / (u0 * (1 + t * ut)) - ut / (1 + t * ut)
      = ut * (1 - u0) / (u0 * (1 + t * ut)) := by
    field_simp
  rw [hid]
  refine norm_div_le_of (rb := 9 / 20) (r := 4 * η) (by norm_num) ?_ (by linarith) ?_
  · rw [norm_mul]
    have hb : (1 / 2 : ℝ) * (9 / 10) ≤ ‖u0‖ * ‖1 + t * ut‖ :=
      mul_le_mul hu0 hWlb (by norm_num) (norm_nonneg _)
    have hc : (9 : ℝ) / 20 = (1 / 2) * (9 / 10) := by norm_num
    rw [hc]; exact hb
  · rw [norm_mul]
    have h := mul_le_mul hut h1u (norm_nonneg _) (by linarith)
    have h2 : (3 / 2 + η) * η ≤ 4 * η * (9 / 20) := by nlinarith [hη1, hηnn]
    linarith

/-- Piece 2: replacing `t` by `t0` costs at most `4 δ₂`, using `‖t - t0‖ ≤ δ₂` and the bounds on
`‖t‖`, `‖t0‖`, `‖ut‖` which keep both denominators `≥ 9/10`. -/
theorem ratio_piece2_t {ut t t0 : ℂ} {η δ₂ : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1 / 1000) (hδ₂ : 0 ≤ δ₂)
    (hC : ‖t - t0‖ ≤ δ₂) (ht : ‖t‖ ≤ 1 / 16) (ht0 : ‖t0‖ ≤ 1 / 64)
    (hut : ‖ut‖ ≤ 3 / 2 + η) :
    ‖ut / (1 + t * ut) - ut / (1 + t0 * ut)‖ ≤ 4 * δ₂ := by
  have hW1 : 9 / 10 ≤ ‖1 + t * ut‖ := by
    refine le_norm_one_add ?_
    calc ‖t * ut‖ = ‖t‖ * ‖ut‖ := norm_mul t ut
      _ ≤ (1 / 16) * (3 / 2 + η) := mul_le_mul ht hut (norm_nonneg _) (by norm_num)
      _ ≤ (1 / 16) * (3 / 2 + 1 / 1000) := by nlinarith [hη1]
      _ ≤ 1 - 9 / 10 := by norm_num
  have hW2 : 9 / 10 ≤ ‖1 + t0 * ut‖ := by
    refine le_norm_one_add ?_
    calc ‖t0 * ut‖ = ‖t0‖ * ‖ut‖ := norm_mul t0 ut
      _ ≤ (1 / 64) * (3 / 2 + η) := mul_le_mul ht0 hut (norm_nonneg _) (by norm_num)
      _ ≤ (1 / 64) * (3 / 2 + 1 / 1000) := by nlinarith [hη1]
      _ ≤ 1 - 9 / 10 := by norm_num
  have hW1ne : (1 + t * ut) ≠ 0 := by
    intro h; rw [h, norm_zero] at hW1; norm_num at hW1
  have hW2ne : (1 + t0 * ut) ≠ 0 := by
    intro h; rw [h, norm_zero] at hW2; norm_num at hW2
  have hid : ut / (1 + t * ut) - ut / (1 + t0 * ut)
      = ut * ut * (t0 - t) / ((1 + t * ut) * (1 + t0 * ut)) := by
    rw [div_sub_div (b := 1 + t * ut) (d := 1 + t0 * ut) ut ut hW1ne hW2ne]
    congr 1
    ring
  rw [hid]
  refine norm_div_le_of (rb := 81 / 100) (r := 4 * δ₂) (by norm_num) ?_ (by linarith) ?_
  · rw [norm_mul]
    have hb : (9 / 10 : ℝ) * (9 / 10) ≤ ‖1 + t * ut‖ * ‖1 + t0 * ut‖ :=
      mul_le_mul hW1 hW2 (by norm_num) (norm_nonneg _)
    have hc : (81 : ℝ) / 100 = (9 / 10) * (9 / 10) := by norm_num
    rw [hc]; exact hb
  · rw [norm_mul, norm_mul]
    have h1 : ‖ut‖ * ‖ut‖ ≤ (3 / 2 + η) * (3 / 2 + η) :=
      mul_le_mul hut hut (norm_nonneg _) (by linarith)
    have h2 : (3 / 2 + η) * (3 / 2 + η) ≤ 4 * (81 / 100) := by nlinarith [hη1, hη]
    have h3 : ‖t0 - t‖ ≤ δ₂ := by rw [norm_sub_rev]; exact hC
    calc ‖ut‖ * ‖ut‖ * ‖t0 - t‖ ≤ ((3 / 2 + η) * (3 / 2 + η)) * δ₂ :=
          mul_le_mul h1 h3 (norm_nonneg _) (by positivity)
      _ ≤ (4 * (81 / 100)) * δ₂ := by nlinarith [h2, hδ₂]
      _ = 4 * δ₂ * (81 / 100) := by ring

/-- Piece 3: replacing `ut` by `h0` in `ut / (1 + t0 * ut)`, at fixed `t0`, costs at most
`2 * (η + D δ₂)`; here the algebraic identity is exact, `f(u) - f(h) = (u - h)/((1+t0 u)(1+t0 h))`. -/
theorem ratio_piece3_h0 {ut hFt h0 t0 : ℂ} {D η δ₂ : ℝ}
    (hD : 0 ≤ D) (hη : 0 < η) (hη1 : η ≤ 1 / 1000) (hδ₂ : 0 ≤ δ₂)
    (hA : ‖ut - hFt‖ ≤ η) (hB : ‖hFt - h0‖ ≤ D * δ₂)
    (ht0 : ‖t0‖ ≤ 1 / 64) (hh0 : ‖h0‖ ≤ 3 / 2) (hut : ‖ut‖ ≤ 3 / 2 + η) :
    ‖ut / (1 + t0 * ut) - h0 / (1 + t0 * h0)‖ ≤ 2 * (η + D * δ₂) := by
  have hW1 : 9 / 10 ≤ ‖1 + t0 * ut‖ := by
    refine le_norm_one_add ?_
    calc ‖t0 * ut‖ = ‖t0‖ * ‖ut‖ := norm_mul t0 ut
      _ ≤ (1 / 64) * (3 / 2 + η) := mul_le_mul ht0 hut (norm_nonneg _) (by norm_num)
      _ ≤ (1 / 64) * (3 / 2 + 1 / 1000) := by nlinarith [hη1]
      _ ≤ 1 - 9 / 10 := by norm_num
  have hW2 : 9 / 10 ≤ ‖1 + t0 * h0‖ := by
    refine le_norm_one_add ?_
    calc ‖t0 * h0‖ = ‖t0‖ * ‖h0‖ := norm_mul t0 h0
      _ ≤ (1 / 64) * (3 / 2) := mul_le_mul ht0 hh0 (norm_nonneg _) (by norm_num)
      _ ≤ 1 - 9 / 10 := by norm_num
  have hW1ne : (1 + t0 * ut) ≠ 0 := by
    intro h; rw [h, norm_zero] at hW1; norm_num at hW1
  have hW2ne : (1 + t0 * h0) ≠ 0 := by
    intro h; rw [h, norm_zero] at hW2; norm_num at hW2
  have hid : ut / (1 + t0 * ut) - h0 / (1 + t0 * h0)
      = (ut - h0) / ((1 + t0 * ut) * (1 + t0 * h0)) := by
    rw [div_sub_div (b := 1 + t0 * ut) (d := 1 + t0 * h0) ut h0 hW1ne hW2ne]
    congr 1
    ring
  rw [hid]
  refine norm_div_le_of (rb := 81 / 100) (r := 2 * (η + D * δ₂)) (by norm_num) ?_ ?_ ?_
  · rw [norm_mul]
    have hb : (9 / 10 : ℝ) * (9 / 10) ≤ ‖1 + t0 * ut‖ * ‖1 + t0 * h0‖ :=
      mul_le_mul hW1 hW2 (by norm_num) (norm_nonneg _)
    have hc : (81 : ℝ) / 100 = (9 / 10) * (9 / 10) := by norm_num
    rw [hc]; exact hb
  · nlinarith [hD, hδ₂, hη.le]
  · have hdist : ‖ut - h0‖ ≤ η + D * δ₂ := by
      calc ‖ut - h0‖ = ‖(ut - hFt) + (hFt - h0)‖ := by congr 1; ring
        _ ≤ ‖ut - hFt‖ + ‖hFt - h0‖ := norm_add_le _ _
        _ ≤ η + D * δ₂ := add_le_add hA hB
    nlinarith [hdist, hD, hδ₂, hη.le]

theorem ratio_sub_ratio_le {u0 ut hFt h0 t t0 : ℂ} {D η δ₂ : ℝ}
    (hD : 0 ≤ D) (hη : 0 < η) (hη1 : η ≤ 1 / 1000) (hδ₂ : 0 ≤ δ₂)
    (hu0 : 1 / 2 ≤ ‖u0‖) (hu0' : ‖u0 - 1‖ ≤ η)
    (hA : ‖ut - hFt‖ ≤ η) (hB : ‖hFt - h0‖ ≤ D * δ₂)
    (hC : ‖t - t0‖ ≤ δ₂) (ht : ‖t‖ ≤ 1 / 16) (ht0 : ‖t0‖ ≤ 1 / 64)
    (hh0 : ‖h0‖ ≤ 3 / 2) (hhFt : ‖hFt‖ ≤ 3 / 2) (hut : ‖ut‖ ≤ 3 / 2 + η) :
    ‖ut / (u0 * (1 + t * ut)) - h0 / (1 + t0 * h0)‖ ≤ 20 * (D + 1) * (η + δ₂) := by
  have h1 := ratio_piece1_u0 hη hη1 hu0 hu0' ht hut
  have h2 := ratio_piece2_t hη hη1 hδ₂ hC ht ht0 hut
  have h3 := ratio_piece3_h0 hD hη hη1 hδ₂ hA hB ht0 hh0 hut
  have htri : ‖ut / (u0 * (1 + t * ut)) - h0 / (1 + t0 * h0)‖
      ≤ 4 * η + 4 * δ₂ + 2 * (η + D * δ₂) := by
    calc ‖ut / (u0 * (1 + t * ut)) - h0 / (1 + t0 * h0)‖
        ≤ ‖ut / (u0 * (1 + t * ut)) - ut / (1 + t * ut)‖
          + ‖ut / (1 + t * ut) - ut / (1 + t0 * ut)‖
          + ‖ut / (1 + t0 * ut) - h0 / (1 + t0 * h0)‖ :=
            norm_sub_le_of_sub_sub _ _ _ _
      _ ≤ 4 * η + 4 * δ₂ + 2 * (η + D * δ₂) := by linarith
  nlinarith [htri, hD, hη.le, hδ₂, mul_nonneg hD hη.le, mul_nonneg hD hδ₂]

end Work.Pert
