import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.interpol_defs
import Submission.Work.Blocks.InterpTruncDefs
import Submission.Work.Blocks.InterpTrunc.sliceL2_le
import Submission.Work.Blocks.InterpTrunc.zF_abs_le
import Submission.Work.Blocks.InterpTrunc.mixInt_Icc_le_cut
import Submission.Work.Blocks.InterpTrunc.fourInt_cut
import Submission.Work.Blocks.InterpTrunc.cut_functional_le
import Submission.Work.Blocks.InterpTrunc.assembly

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Blocks

theorem interp_truncation :
    ∀ C : ℝ, 0 < C → (∀ (δ R : ℝ), 0 < δ → δ < R → ∀ (α : ℝ) (G : ℝ → ℝ → ℝ),
        0 < α → α ≤ 1 / 4 →
        (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry G)
          (Set.Ioi 0 ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1))) →
        (∀ z : ℝ, G z 0 = 0) → (∀ z : ℝ, G z (Real.pi / 2) = 0) →
        (∀ z : ℝ, z ∉ Set.Icc δ R → ∀ θ : ℝ, G z θ = 0) →
        Work.FTS.EllipticEst.FourInt G →
        α ^ 2 * Work.FTS.EllipticEst.mixInt G
          ≤ C * (α ^ 4 * Work.FTS.EllipticEst.ddInt G + Work.FTS.EllipticEst.ttInt G
              + α ^ 2 * Work.FTS.EllipticEst.dInt G)) →
    ∀ (α : ℝ) (G : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry G)
        (Set.Ioi 0 ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1))) →
      (∀ z : ℝ, G z 0 = 0) → (∀ z : ℝ, G z (Real.pi / 2) = 0) →
      Work.FTS.EllipticEst.FourInt G →
      α ^ 2 * Work.FTS.EllipticEst.mixInt G
        ≤ C * (α ^ 4 * Work.FTS.EllipticEst.ddInt G + Work.FTS.EllipticEst.ttInt G
            + α ^ 2 * Work.FTS.EllipticEst.dInt G) :=
  Work.Blocks.InterpTrunc.interp_truncation_aux
    (fun {φ : ℝ → ℝ} {K : ℝ} {k : ℕ} {G : ℝ → ℝ → ℝ}
      (hφ : Work.FTS.EllipticEst.IsZCut φ K) (hk : 2 ≤ k)
      (hG : Work.FTS.EllipticEst.ThetaU.SmoothOpenθ G) =>
        Work.Blocks.InterpTrunc.fourInt_cut hφ hk hG)
    (fun {φ : ℝ → ℝ} {K : ℝ} {G : ℝ → ℝ → ℝ}
      (hφ : Work.FTS.EllipticEst.IsZCut φ K)
      (hG : Work.FTS.EllipticEst.ThetaU.SmoothOpenθ G)
      (hF : Work.FTS.EllipticEst.FourInt G) {Ks Kf : ℝ} (hKs : 0 ≤ Ks) (hKf : 0 ≤ Kf)
      (hSl : ∀ z : ℝ, 0 < z →
        Work.Blocks.InterpTrunc.inn G z
          ≤ Ks * Work.Blocks.InterpTrunc.inn (Work.Spaces.pth (Work.Spaces.pth G)) z) =>
        Work.Blocks.InterpTrunc.cut_functional_le hφ hG hF hKs hKf hSl)

end Work.Blocks
