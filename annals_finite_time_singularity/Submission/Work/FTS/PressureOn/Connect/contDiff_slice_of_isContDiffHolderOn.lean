import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.FTS.PressureOn.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Connect

theorem contDiff_slice_of_isContDiffHolderOn {α : NNReal}
    {v : Work.FTS.PressureOn.R3 → ℝ → Work.FTS.PressureOn.R3} {S τ : ℝ}
    (hstrip : IsContDiffHolderOn ℝ α v.uncurry (Set.univ ×ˢ Set.Icc 0 S))
    (hτ : τ ∈ Set.Icc 0 S) : ContDiff ℝ 1 (v · τ) := by
  -- The slice `x ↦ v x τ` is the composition of `v.uncurry` with the embedding
  -- `x ↦ (x, τ)`, which maps `univ` into the strip `univ ×ˢ Icc 0 S`.
  have h : ContDiffOn ℝ 1 (fun x : Work.FTS.PressureOn.R3 => (x, τ)) Set.univ := by fun_prop
  have h2 : ContDiffOn ℝ 1 (fun x : Work.FTS.PressureOn.R3 => v.uncurry (x, τ)) Set.univ :=
    hstrip.1.comp h (by intro x _; exact ⟨trivial, hτ⟩)
  rw [contDiffOn_univ] at h2
  exact h2

end Work.FTS.PressureOn.Connect
