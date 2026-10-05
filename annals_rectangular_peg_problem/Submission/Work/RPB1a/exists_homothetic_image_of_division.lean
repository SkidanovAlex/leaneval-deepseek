import Mathlib
import Submission.Work.RPB1a.Defs

namespace Work.RPB1a

open Complex Set Metric
open scoped ContDiff Real

theorem exists_homothetic_image_of_division (γ : Circle → ℂ) {lam₁ a : ℝ} (hlam : 0 < lam₁)
    (ha : 0 < a) (F0 : ℂ) (e : ℝ) :
    ∃ lam : ℝ, 0 < lam ∧ ∃ b : ℂ, ∀ t : ℝ,
      (lam₁ : ℂ) * ((γ (Circle.exp (e * t)) - F0) / (a : ℂ)) ∈
        (fun z : ℂ => (lam : ℂ) * z + b) '' Set.range γ := by
  -- Every point of the claimed image is the image of `γ (Circle.exp (e*t))` itself,
  -- under the homothety `z ↦ (lam₁/a) z - (lam₁/a) F0`.
  refine ⟨lam₁ / a, div_pos hlam ha, -(((lam₁ / a : ℝ)) : ℂ) * F0, fun t => ?_⟩
  refine ⟨γ (Circle.exp (e * t)), ⟨Circle.exp (e * t), rfl⟩, ?_⟩
  field_simp
  push_cast
  ring

end Work.RPB1a
