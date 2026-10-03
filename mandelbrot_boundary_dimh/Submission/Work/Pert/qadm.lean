import Mathlib
import Submission.Work.Pert.Basic

/-!
# PERT: admissibility of the two gate regions

`MandelDim.QAdm b₁ b₂` (`Re b₂ > Re b₁ + 4`) is the hypothesis under which the FATOU area produces
a Fatou coordinate on `Qreg b₁ b₂` (via `FatouExists`).  For the gates `Q(ξ₁, -ξ₁ + 1/α)` and
`Q(ξ₁ - 1/α, -ξ₁)` of Shishikura §4.2 this holds as soon as `α ∈ 𝓕₁` and `‖α‖` is small compared
with `1/ξ₁`, because `InF1 α` gives `Re (1/α) > 1/(2‖α‖)`.
-/

namespace Work.Pert

open MandelDim Complex

noncomputable section

/-- `InF1 α` bounds `Re (1/α)` below by `1/(2‖α‖)`. -/
theorem inv_re_lower {α : ℂ} (hF1 : InF1 α) : 1 / (2 * ‖α‖) < (1 / α).re := by
  have hre : 0 < α.re := lt_of_le_of_lt (abs_nonneg α.im) hF1
  have hnorm : 0 < ‖α‖ := norm_pos_iff.mpr (by intro h; rw [h] at hre; simp at hre)
  have hn2 : ‖α‖ ^ 2 = α.re ^ 2 + α.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hIm : α.im ^ 2 < α.re ^ 2 := by
    have h := abs_lt.mp hF1
    nlinarith [h.1, h.2, hre]
  have hlt : ‖α‖ < 2 * α.re := by
    have h : ‖α‖ ^ 2 < (2 * α.re) ^ 2 := by rw [hn2]; nlinarith
    nlinarith [norm_nonneg α, hre]
  have hinv : (1 / α).re = α.re / ‖α‖ ^ 2 := by
    simp only [one_div, Complex.inv_re, Complex.normSq_eq_norm_sq]
  rw [hinv, lt_div_iff₀ (pow_pos hnorm 2)]
  have h : 1 / (2 * ‖α‖) * ‖α‖ ^ 2 = ‖α‖ / 2 := by field_simp
  rw [h]; linarith

/-- Both gate regions of §4.2 are admissible, provided `‖α‖ ≤ 1/(4ξ₁ + 8)`. -/
theorem qadm {α : ℂ} (hF1 : InF1 α) {ξ₁ : ℝ} (hξ : 0 < ξ₁) (hsmall : 4 * ξ₁ + 8 ≤ 1 / ‖α‖) :
    QAdm (some (ξ₁ : ℂ)) (some (-(ξ₁ : ℂ) + 1 / α)) ∧
      QAdm (some ((ξ₁ : ℂ) - 1 / α)) (some (-(ξ₁ : ℂ))) := by
  have h := inv_re_lower hF1
  have h2 : 2 * ξ₁ + 4 < (1 / α).re := by
    have hA : 2 * ξ₁ + 4 ≤ 1 / ‖α‖ / 2 := by
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
      linarith
    have hB : 1 / ‖α‖ / 2 = 1 / (2 * ‖α‖) := by ring
    linarith [hA, hB]
  constructor
  · intro a ha b hb
    simp only [Option.mem_some_iff] at ha hb
    subst ha; subst hb
    simp only [Complex.ofReal_re, Complex.add_re, Complex.neg_re]
    linarith
  · intro a ha b hb
    simp only [Option.mem_some_iff] at ha hb
    subst ha; subst hb
    simp only [Complex.ofReal_re, Complex.sub_re, Complex.neg_re]
    linarith

end

end Work.Pert
