import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.StabilityFar.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The derivative of `u.uncurry` splits into its spatial and temporal blocks

If `(x,t) ↦ u x t` is differentiable at `(x,t)` with derivative `L`, then applying `L` to a
pair `(v,s)` splits as the spatial derivative `D_xu(x,t) v` plus `s` times the time derivative
`∂ₜu(x,t)`.  This is the pointwise form of `Work.StabilityFar.blockDeriv`.  The two blocks are
computed by composing `h` with the two coordinate embeddings `x ↦ (x,t)` and `t ↦ (x,t)`.
-/

open FiniteTimeSingularity

namespace Work.StabilityFar.Deriv

theorem hasFDerivAt_uncurry_apply {u : Work.StabilityFar.R3 → ℝ → Work.StabilityFar.R3}
    {L : (Work.StabilityFar.R3 × ℝ) →L[ℝ] Work.StabilityFar.R3}
    {x : Work.StabilityFar.R3} {t : ℝ}
    (h : HasFDerivAt (Function.uncurry u) L (x, t)) (v : Work.StabilityFar.R3) (s : ℝ) :
    L (v, s) = fderiv ℝ (u · t) x v + s • FiniteTimeSingularity.timeDeriv u x t := by
  have hsl := h.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) (E := Work.StabilityFar.R3) (F := ℝ) x t)
  have htt := h.comp t (hasFDerivAt_prodMk_right (𝕜 := ℝ) (E := Work.StabilityFar.R3) (F := ℝ) x t)
  have e1 : fderiv ℝ (u · t) x = L.comp (ContinuousLinearMap.inl ℝ Work.StabilityFar.R3 ℝ) := by
    simpa [Function.comp_def] using hsl.fderiv
  have e2 : FiniteTimeSingularity.timeDeriv u x t = L (0, 1) := by
    rw [FiniteTimeSingularity.timeDeriv, deriv]
    have := htt.fderiv
    change fderiv ℝ (u x) t = _ at this
    rw [this]
    rfl
  rw [e1, e2]
  rw [show (v, s) = (v, (0:ℝ)) + ((0:Work.StabilityFar.R3), s) by ext <;> simp]
  rw [map_add]
  rw [show ((0:Work.StabilityFar.R3), s) = s • ((0:Work.StabilityFar.R3), (1:ℝ)) by ext <;> simp]
  rw [map_smul]
  simp [ContinuousLinearMap.comp_apply]

end Work.StabilityFar.Deriv
