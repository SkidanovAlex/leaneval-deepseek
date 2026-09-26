import Mathlib
import Submission.Work.TorusCover.Basic

/-!
# Winding vectors are invariant under circle reparametrisation

If `γ` has winding vector `v` with respect to a parametrised torus `psi`, then so does the
reparametrised curve `t ↦ γ (σ.f t)`, for any `CircleReparam σ`.

The point is that a period-shift periodic lift `Λ` of `γ` precomposed with `σ.f` is again a
lift: `ψMap` of it at `t` is `γ (σ.f t)`, it is continuous (a composition of continuous maps)
and it still advances by `periodShift v` over a period, because `σ.f (t + 2π) = σ.f t + 2π`
and `Λ (s + 2π) = Λ s + periodShift v`.
-/

open LeanEval.KnotTheory.PardonDistortion

namespace Work.TorusCover

theorem hasWinding_comp_circleReparam {psi : ℝ → ℝ → LeanEval.KnotTheory.PardonDistortion.R3}
    {γ : ℝ → LeanEval.KnotTheory.PardonDistortion.R3} {v : ℤ × ℤ}
    (h : Work.TorusCover.HasWinding psi γ v)
    (σ : LeanEval.KnotTheory.PardonDistortion.CircleReparam) :
    Work.TorusCover.HasWinding psi (fun t => γ (σ.f t)) v := by
  obtain ⟨Λ, hΛ⟩ := h
  refine ⟨fun t => Λ (σ.f t), ⟨?_, ?_⟩, ?_⟩
  · exact hΛ.continuous.comp σ.smooth.continuous
  · intro t
    exact hΛ.map_eq (σ.f t)
  · intro t
    show Λ (σ.f (t + 2 * Real.pi)) = Λ (σ.f t) + periodShift v
    rw [σ.periodic t]
    exact hΛ.shift (σ.f t)

end Work.TorusCover
