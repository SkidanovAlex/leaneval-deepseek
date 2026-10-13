import Mathlib

namespace Work.WilE7.Chart

theorem injective_fderiv_of_eventually_leftInv {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {γ : E → F} {L : F →L[ℝ] E} {x : E} (hγ : DifferentiableAt ℝ γ x)
    (hL : ∀ᶠ y in nhds x, L (γ y) = y) : Function.Injective (fderiv ℝ γ x) := by
  intro u v huv
  have h2 : fderiv ℝ (fun y => L (γ y)) x = L.comp (fderiv ℝ γ x) := by
    rw [show (fun y => L (γ y)) = L ∘ γ from rfl, fderiv_comp x L.differentiableAt hγ]
    simp
  have h4 : fderiv ℝ (fun y => L (γ y)) x = fderiv ℝ id x :=
    Filter.EventuallyEq.fderiv_eq hL
  have key : ∀ w : E, w = L ((fderiv ℝ γ x) w) := by
    intro w
    have := congrArg (fun (T : E →L[ℝ] E) => T w) h2
    simp only [ContinuousLinearMap.comp_apply] at this
    rw [← this, h4]; simp
  rw [key u, key v, huv]

end Work.WilE7.Chart
