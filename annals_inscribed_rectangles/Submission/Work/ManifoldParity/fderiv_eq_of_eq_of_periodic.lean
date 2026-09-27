import Mathlib
import Submission.Work.ManifoldParity.Defs

namespace Work.ManifoldParity

/-- The derivative of a periodic function is periodic with the same period. -/
theorem fderiv_periodic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {γ : ℝ → E} {T : ℝ} (hper : Function.Periodic γ T)
    (hd : ∀ t, DifferentiableAt ℝ γ t) : Function.Periodic (fderiv ℝ γ) T := by
  intro x
  have hdiff : DifferentiableAt ℝ (fun t : ℝ => t + T) x := by fun_prop
  have hfd : fderiv ℝ (γ ∘ (fun t : ℝ => t + T)) x = fderiv ℝ γ (x + T) := by
    rw [fderiv_comp x (hd (x + T)) hdiff]
    simp [fderiv_add_const]
  have hcomp : (γ ∘ (fun t : ℝ => t + T)) = γ := funext (fun t => hper t)
  rw [hcomp] at hfd
  exact hfd.symm

theorem fderiv_eq_of_eq_of_periodic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {γ : ℝ → E} {T a b : ℝ} (hper : Function.Periodic γ T)
    (hd : ∀ t, DifferentiableAt ℝ γ t) (h : ∃ k : ℤ, a = b + k * T) :
    fderiv ℝ γ a = fderiv ℝ γ b := by
  have hper' : Function.Periodic (fderiv ℝ γ) T := fderiv_periodic hper hd
  obtain ⟨k, rfl⟩ := h
  exact hper'.int_mul k b

end Work.ManifoldParity
