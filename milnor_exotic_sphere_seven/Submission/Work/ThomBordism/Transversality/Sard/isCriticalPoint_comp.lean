import Mathlib
import Submission.Work.ThomBordism.Transversality.Sard.Strat

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Criticality transfers to a composition

If `f` is critical at `γ u` (its derivative there is not surjective), then `f ∘ γ` is critical at
`u`, for `f` differentiable at `γ u` and `γ` differentiable at `u`: the derivative of the
composition is `d f_{γ u} ∘ d γ_u`, whose range is contained in that of `d f_{γ u}`.

This is the (linear-algebraic) heart of the observation that a critical point of a map restricted
to a smooth hypersurface remains critical for the restriction — the input of the "level set" step
of Sard's theorem.
-/

open MeasureTheory Set

namespace Work.ThomBordism.Transversality.Sard

open Work.ThomBordism.Transversality (IsCriticalPoint)

noncomputable section

theorem isCriticalPoint_comp {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → G} {γ : F → E} {u : F} (hf : DifferentiableAt ℝ f (γ u))
    (hγ : DifferentiableAt ℝ γ u) (hcrit : IsCriticalPoint f (γ u)) :
    IsCriticalPoint (fun u => f (γ u)) u := by
  rw [IsCriticalPoint] at hcrit ⊢
  intro hsurj
  have hchain : fderiv ℝ (fun u => f (γ u)) u
      = (fderiv ℝ f (γ u)).comp (fderiv ℝ γ u) := fderiv_comp u hf hγ
  rw [hchain] at hsurj
  exact hcrit fun v => by
    obtain ⟨w, hw⟩ := hsurj v
    exact ⟨fderiv ℝ γ u w, hw⟩

end

end Work.ThomBordism.Transversality.Sard
