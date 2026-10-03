import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Interfaces.Parabolic

namespace Work.Pert

/-!
# PERT · `I_mul_half_eta_mem_Qm`

The point `i η/2` lies in the lower gate `Qm ξ₁ α = Qreg (some (ξ₁ - 1/α)) (some (-ξ₁))` as soon
as `η > 2ξ₁`.  Writing `b₁ = ξ₁ - 1/α`, `b₂ = -ξ₁`, the two defining inequalities at `z = i η/2`
are

* `-|z.im + (1/α).im| < (1/α).re - ξ₁`,
* `ξ₁ < |η/2|`,

and both follow from `InF1 α` (`|Im α| < Re α`, whence `|(1/α).im| ≤ (1/α).re`) together with
`η/2 > ξ₁`.
-/

noncomputable section

/-- `InF1` is preserved by inversion: `|Im (1/α)| ≤ Re (1/α)`. -/
lemma abs_im_one_div_le_re_one_div {α : ℂ} (hα : MandelDim.InF1 α) :
    |(1 / α).im| ≤ (1 / α).re := by
  have hαre : 0 < α.re := lt_of_le_of_lt (abs_nonneg α.im) hα
  have hαne : α ≠ 0 := by
    intro h; rw [h] at hαre; simp at hαre
  have hnsq : 0 < Complex.normSq α := Complex.normSq_pos.mpr hαne
  have hx : (1 / α).re = α.re / Complex.normSq α := by
    rw [one_div, Complex.inv_re]
  have hy : (1 / α).im = -α.im / Complex.normSq α := by
    rw [one_div, Complex.inv_im]
  rw [hy, hx, abs_div, abs_neg, abs_of_pos hnsq]
  exact div_le_div_of_nonneg_right (le_of_lt hα) (le_of_lt hnsq)

theorem I_mul_half_eta_mem_Qm {α : ℂ} {ξ₁ η : ℝ} (hξ : 0 < ξ₁) (hη : 2 * ξ₁ < η)
    (hα : MandelDim.InF1 α) : (Complex.I * (η / 2) : ℂ) ∈ Work.Pert.Qm ξ₁ α := by
  have habs : |(1 / α).im| ≤ (1 / α).re := abs_im_one_div_le_re_one_div hα
  have hpos : 0 < η / 2 := by linarith
  rw [Work.Pert.Qm, MandelDim.Qreg]
  simp only [Option.mem_some_iff, Set.mem_ofPred_eq, forall_eq']
  refine ⟨?_, ?_⟩
  · -- `-|z.im - b₁.im| < z.re - b₁.re` with `b₁ = ξ₁ - 1/α`
    have h1 : η / 2 - |(1 / α).im| ≤ |η / 2 + (1 / α).im| := by
      have h := abs_sub_abs_le_abs_sub (η / 2) (-(1 / α).im)
      rw [abs_neg, abs_of_nonneg (le_of_lt hpos), sub_neg_eq_add] at h
      exact h
    rw [show (Complex.I * (η / 2) - ((ξ₁ : ℂ) - 1 / α)).im = η / 2 + (1 / α).im from by simp,
      show (Complex.I * (η / 2) - ((ξ₁ : ℂ) - 1 / α)).re = (1 / α).re - ξ₁ from by simp]
    linarith
  · -- `z.re - b₂.re < |z.im - b₂.im|` with `b₂ = -ξ₁`
    rw [show (Complex.I * (η / 2) - -((ξ₁ : ℂ))).re = ξ₁ from by simp,
      show (Complex.I * (η / 2) - -((ξ₁ : ℂ))).im = η / 2 from by simp]
    rw [abs_of_pos hpos]
    linarith

end

end Work.Pert
