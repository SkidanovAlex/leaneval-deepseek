import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.closedBall_subset_Qm

/-!
# PERT · `PinFromCoord/gate_aux`

Elementary geometry of the lower gate `Qm ξ α` used by
`Work.Pert.PinFromCoord.strip_high_of_pin_fixed`.

`mem_Qm_iff` rewrites membership in `Qm ξ α = Qreg (some (ξ - 1/α)) (some (-ξ))` as the pair of
cone inequalities

* `A z := z.re + (1/α).re - ξ + |z.im + (1/α).im| > 0`  (vertex `ξ - 1/α`), and
* `B z := |z.im| - z.re - ξ > 0`                          (vertex `-ξ`).

For a point `α` with `InF1 α` one has `|(1/α).im| ≤ (1/α).re` (`im_inv_le_re`), and this makes `A`
dominate the "hyperbolic" quantity `z.re + |z.im| - ξ` (`A_ge`).  That is what turns the crude
`2ρ`-criterion `ball_subset_Qm_of_bounds` into a criterion whose constants are linear in the height
`|z.im|`: for the high part of the gate the whole disc of radius `ρ` about `z` lies in `Qm ξ α` as
soon as `ρ < z.re + (1/α).re - ξ` and `2ρ < B z`.
-/

namespace Work.Pert.PinFromCoord

open MandelDim Complex Set Metric

noncomputable section

/-- `InF1 α` (`|Im α| < Re α`) gives `|Im (1/α)| ≤ Re (1/α)` for the reciprocal. -/
theorem im_inv_le_re {α : ℂ} (h : MandelDim.InF1 α) : |(1 / α).im| ≤ (1 / α).re := by
  have hre : 0 < α.re := lt_of_le_of_lt (abs_nonneg _) h
  have hns : 0 < Complex.normSq α := Complex.normSq_pos.mpr (by
    intro h0
    rw [h0] at hre
    exact absurd hre (lt_irrefl 0))
  rw [one_div, Complex.inv_re, Complex.inv_im, abs_div, abs_neg, abs_of_pos hns]
  exact div_le_div_of_nonneg_right (le_of_lt h) hns.le

/-- For `|Im β| ≤ Re β` the cone function at the vertex `β` dominates `z.re + |z.im|`. -/
theorem A_ge {β z : ℂ} (hβ : |β.im| ≤ β.re) (ξ : ℝ) :
    |z.im| + z.re - ξ ≤ z.re + β.re - ξ + |z.im + β.im| := by
  have h1 : |z.im| ≤ |β.im| + |z.im + β.im| := by
    have h := abs_sub_abs_le_abs_sub z.im (-β.im)
    have h2 : |z.im - -β.im| = |z.im + β.im| := by ring_nf
    rw [h2] at h
    have h3 := abs_neg β.im ▸ h
    linarith [abs_nonneg β.im, abs_nonneg (z.im + β.im)]
  linarith

/-- **The disc criterion for the gate.**  If `ρ ≥ 0`, `|Im (1/α)| ≤ Re (1/α)`, and at the centre `z`
both cone functions have slack `> ρ` resp. `> 2ρ`, then the open disc of radius `ρ` about `z`
lies in `Qm ξ α`. -/
theorem ball_subset_Qm_of_bounds {ξ : ℝ} {α : ℂ} {z : ℂ} {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hIm : |(1 / α).im| ≤ (1 / α).re)
    (h1 : z.re + (1 / α).re - ξ > ρ)
    (h2 : |z.im| - z.re - ξ > 2 * ρ) :
    Metric.ball z ρ ⊆ Work.Pert.Qm ξ α := by
  intro ζ hζ
  rw [Metric.mem_ball, Complex.dist_eq] at hζ
  have hre : |ζ.re - z.re| < ρ := by
    have h := Complex.abs_re_le_norm (ζ - z)
    rw [Complex.sub_re] at h
    exact lt_of_le_of_lt h hζ
  have him : |ζ.im - z.im| < ρ := by
    have h := Complex.abs_im_le_norm (ζ - z)
    rw [Complex.sub_im] at h
    exact lt_of_le_of_lt h hζ
  have hre₁ : z.re - ρ < ζ.re := by linarith [(abs_lt.mp hre).1]
  have him₁ : |z.im| - ρ < |ζ.im| := by
    have h := abs_sub_abs_le_abs_sub z.im ζ.im
    rw [abs_sub_comm] at h
    linarith [(abs_lt.mp him).2, h]
  have hre₂ : ζ.re - z.re < ρ := (abs_lt.mp hre).2
  rw [Work.Pert.mem_Qm_iff]
  constructor
  · have h0 : (0 : ℝ) ≤ |ζ.im + (1 / α).im| := abs_nonneg _
    linarith
  · have : |ζ.im| - ζ.re - ξ ≥ (|z.im| - ρ) - (z.re + ρ) - ξ := by linarith
    linarith [h2]

/-- At a point of the high gate the first cone function dominates `|z.im| + z.re - ξ`; the two
cone functions therefore both exceed `|z.im| + z.re - ξ`, which is the quantity compared with the
covering radius. -/
theorem margins_ge {ξ : ℝ} {α z : ℂ} (hIm : |(1 / α).im| ≤ (1 / α).re) :
    |z.im| + z.re - ξ ≤ z.re + (1 / α).re - ξ + |z.im + (1 / α).im| ∧
      |z.im| + z.re - ξ ≤ |z.im| - z.re - ξ + 2 * z.re := by
  refine ⟨A_ge hIm ξ, ?_⟩
  linarith

end

end Work.Pert.PinFromCoord
