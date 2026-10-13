import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllSol.ShiftFT.ShiftPrimDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.ShiftFT.Aux2

/-- If `u` is jointly `C²` on the closed half-strip `ℝ × (0,π/2)`, then every `θ`-slice
`s ↦ u s θ` (`θ ∈ (0,π/2)`) is `C²`, hence in particular differentiable, and its `z`-derivative
`pz u · θ = ∂_z u(·,θ)` is again differentiable (the slice is `C²`, so `deriv` of the slice is
`C¹`).

The slice is obtained by composing the (smooth) map `s ↦ (s,θ)` with `Function.uncurry u`; since
the second coordinate of the image is `θ` itself (in the interval), the whole image lies in
`univ ×ˢ Ioo 0 (π/2)`. -/
theorem gcSliceData (u : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Differentiable ℝ (fun s : ℝ => u s θ))
    ∧ (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Differentiable ℝ (fun s : ℝ => Work.Spaces.pz u s θ)) := by
  -- every slice of `u` at `θ ∈ (0,π/2)` is globally `C²` on `ℝ`
  have hslice : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ContDiff ℝ 2 (fun s : ℝ => u s θ) := by
    intro θ hθ
    -- the parametrisation `s ↦ (s,θ)` is smooth …
    have hφ : ContDiff ℝ 2 (fun s : ℝ => (s, θ)) := by fun_prop
    -- … and takes all of `ℝ` into the half-strip
    have hmap : Set.MapsTo (fun s : ℝ => (s, θ)) Set.univ
        (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) := fun s _ => ⟨trivial, hθ⟩
    have h2 := hu.comp (contDiffOn_univ.mpr hφ) hmap
    rw [contDiffOn_univ] at h2
    have heq : (Function.uncurry u ∘ fun s : ℝ => (s, θ)) = fun s : ℝ => u s θ := by
      funext s; rfl
    rwa [heq] at h2
  constructor
  · -- differentiability of the slice
    intro θ hθ
    exact (hslice θ hθ).differentiable (by norm_num)
  · -- differentiability of the derivative of the slice
    intro θ hθ
    have h := ContDiff.differentiable_deriv_two (hslice θ hθ)
    simpa [Work.Spaces.pz] using h

end Work.FTS.EllSol.ShiftFT.Aux2
