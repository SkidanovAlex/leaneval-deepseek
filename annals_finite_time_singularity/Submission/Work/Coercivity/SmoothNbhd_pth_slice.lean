import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.Spaces.pth_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-- For a function `f` that is smooth on a neighbourhood of the closed quadrant and any
`s ≥ 0`, the angular slice `θ ↦ f s θ` is differentiable at every `θ ∈ [0,π/2]` with
derivative `pth f s θ = ∂_θ f (s,θ)`, and `θ ↦ pth f s θ` is interval integrable on
`[0,π/2]`. -/
theorem SmoothNbhd_pth_slice (f : ℝ → ℝ → ℝ) (hs : Spaces.SmoothNbhd f) (s : ℝ) (hs0 : 0 ≤ s) :
    (∀ θ ∈ Spaces.Iθ, HasDerivAt (fun θ' => f s θ') (Spaces.pth f s θ) θ) ∧
      IntervalIntegrable (fun θ => Spaces.pth f s θ) MeasureTheory.volume 0 (Real.pi / 2) := by
  -- The angular slice `θ ↦ f s θ` is `C^∞` on the open interval `(-1, π/2+1)`.
  have hsmooth : ContDiffOn ℝ ⊤ (fun t : ℝ => f s t) (Set.Ioo (-1 : ℝ) (π / 2 + 1)) := by
    have hp : ContDiffOn ℝ ⊤ (fun t : ℝ => (s, t)) (Set.Ioo (-1 : ℝ) (π / 2 + 1)) :=
      contDiffOn_const.prodMk contDiffOn_id
    have hmap : Set.MapsTo (fun t : ℝ => (s, t)) (Set.Ioo (-1 : ℝ) (π / 2 + 1))
        (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1)) := by
      intro t ht
      refine ⟨?_, ht⟩
      show (-1 : ℝ) < s
      linarith
    have h := hs.comp hp hmap
    simpa [Function.comp_def, Function.uncurry] using h
  constructor
  · intro θ hθ
    have hmem : θ ∈ Set.Ioo (-1 : ℝ) (π / 2 + 1) :=
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    have hd : DifferentiableAt ℝ (fun t : ℝ => f s t) θ :=
      (hsmooth.contDiffAt (isOpen_Ioo.mem_nhds hmem)).differentiableAt (by simp)
    simpa [Spaces.pth] using hd.hasDerivAt
  · have hcont := (Spaces.pth_integral f s hs hs0 (π / 2) Spaces.pi_half_mem_Iθ).2
    exact hcont.intervalIntegrable_of_Icc (by linarith [Real.pi_pos])

end Work.Coercivity
