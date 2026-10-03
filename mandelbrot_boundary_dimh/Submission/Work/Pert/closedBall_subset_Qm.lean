import Mathlib
import Submission.Work.Pert.Setup

namespace Work.Pert

/-- Membership in the gate `Qm ξ₁ α` (`= Qreg (ξ₁ - 1/α) (-ξ₁)`), written as the two cone
inequalities of §4.2. -/
lemma mem_Qm_iff {ξ₁ : ℝ} {α : ℂ} {z : ℂ} :
    z ∈ Qm ξ₁ α ↔
      0 < z.re + (1 / α).re - ξ₁ + |z.im + (1 / α).im| ∧ 0 < |z.im| - z.re - ξ₁ := by
  simp [Qm, MandelDim.Qreg]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/-- A disk inside the gate `Qm ξ₁ α`: if `0 ≤ r`, `|Re c| ≤ a` and `|Im c| ≥ T + 3r + a`, then the
closed disk of radius `r` around `c` lies in `Qm ξ₁ α`.  Indeed a point `ζ` of the disk has
`|ζ.re| ≤ a + r` and `|ζ.im| ≥ T + 2r + a`, and both gate inequalities
(`ζ.re + Re(1/α) - ξ₁ + |ζ.im + Im(1/α)| > 0`, `|ζ.im| - ζ.re - ξ₁ > 0`) follow for `T` large
enough depending only on `ξ₁` and `α`. -/
theorem closedBall_subset_Qm {ξ₁ : ℝ} {α : ℂ} :
    ∃ T : ℝ, 0 < T ∧ ∀ (c : ℂ) (a r : ℝ), 0 ≤ r → |c.re| ≤ a → T + 3 * r + a ≤ |c.im| →
      Metric.closedBall c r ⊆ Qm ξ₁ α := by
  refine ⟨|ξ₁| + |(1 / α).re| + |(1 / α).im| + 1, by positivity, ?_⟩
  intro c a r hr hre him ζ hζ
  rw [Metric.mem_closedBall, dist_eq_norm] at hζ
  -- coordinate bounds for the centre of the disk
  have hreζ : |ζ.re - c.re| ≤ r := by
    have h := Complex.abs_re_le_norm (ζ - c)
    rw [Complex.sub_re] at h
    exact le_trans h hζ
  have himζ : |ζ.im - c.im| ≤ r := by
    have h := Complex.abs_im_le_norm (ζ - c)
    rw [Complex.sub_im] at h
    exact le_trans h hζ
  have hzre_ub : ζ.re ≤ a + r := by
    have h1 : ζ.re - c.re ≤ r := (abs_le.1 hreζ).2
    linarith [le_abs_self c.re]
  have hzre_lb : -(a + r) ≤ ζ.re := by
    have h1 : -r ≤ ζ.re - c.re := (abs_le.1 hreζ).1
    linarith [neg_abs_le c.re]
  have hzim : |ξ₁| + |(1 / α).re| + |(1 / α).im| + 1 + 2 * r + a ≤ |ζ.im| := by
    have h1 : |c.im| - |ζ.im| ≤ |c.im - ζ.im| := abs_sub_abs_le_abs_sub c.im ζ.im
    rw [abs_sub_comm] at h1
    linarith
  rw [mem_Qm_iff]
  constructor
  · have h1 : |ζ.im| - |(1 / α).im| ≤ |ζ.im + (1 / α).im| := by
      have h := abs_sub_abs_le_abs_sub ζ.im (-(1 / α).im)
      simpa using h
    have h2 : -|(1 / α).re| ≤ (1 / α).re := neg_abs_le _
    have h3 : -|ξ₁| ≤ -ξ₁ := neg_le_neg (le_abs_self ξ₁)
    linarith [abs_nonneg (1 / α).re, abs_nonneg (1 / α).im, abs_nonneg ξ₁]
  · have h3 : ξ₁ ≤ |ξ₁| := le_abs_self ξ₁
    linarith [abs_nonneg (1 / α).re, abs_nonneg (1 / α).im, abs_nonneg ξ₁]

end Work.Pert
