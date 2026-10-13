import Mathlib
import Submission.Work.WilG4c.LipDefs

namespace Work.WilG4c

theorem PsiLipOnI {p : ℕ} (ψ : (Fin p → ℝ) → ℝ → ℝ) (l : Fin p → ℝ) (βl : ℝ)
    (hC1 : ContDiffOn ℝ 1 (ψ l) Work.WilkG4c.I)
    (hb : ∀ s ∈ Work.WilkG4c.I, |deriv (ψ l) s| ≤ βl) :
    ∀ a ∈ Work.WilkG4c.I, ∀ b ∈ Work.WilkG4c.I, |ψ l a - ψ l b| ≤ βl * |a - b| := by
  have hdiff : ∀ x ∈ Work.WilkG4c.I, DifferentiableAt ℝ (ψ l) x := fun x hx =>
    hC1.differentiableOn_one.differentiableAt (isOpen_Ioo.mem_nhds hx)
  have hbound : ∀ x ∈ Work.WilkG4c.I, ‖deriv (ψ l) x‖ ≤ βl := fun x hx => by
    rw [Real.norm_eq_abs]; exact hb x hx
  intro a ha b hb'
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound (convex_Ioo (0:ℝ) 1) ha hb'
  simpa only [Real.norm_eq_abs, abs_sub_comm] using h

end Work.WilG4c
