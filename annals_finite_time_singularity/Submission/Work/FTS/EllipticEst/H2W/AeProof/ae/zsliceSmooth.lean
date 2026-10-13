import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.AeProof.ae

theorem zsliceSmooth {f : ℝ → ℝ → ℝ} {n : ℕ}
    (h : ContDiffOn ℝ n (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2)) :
    ContDiffOn ℝ n (fun z : ℝ => f z θ) (Set.Ioi 0) := by
  have hg : ContDiffOn ℝ n (fun z : ℝ => (z, θ)) (Set.Ioi 0) :=
    contDiffOn_id.prodMk contDiffOn_const
  have hcomp : ContDiffOn ℝ n (Function.uncurry f ∘ (fun z : ℝ => (z, θ))) (Set.Ioi 0) :=
    h.comp hg (fun z hz => ⟨hz, hθ⟩)
  simpa [Function.comp_def, Function.uncurry_apply_pair] using hcomp

end Work.FTS.EllipticEst.H2W.AeProof.ae
