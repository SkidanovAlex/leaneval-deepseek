import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.LocData.Defs
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.H2.STQ.Basic
import Submission.Work.EllipticEst.Core.mixedSliceLe

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.OpenPkg.ProdOpen

open scoped Real Topology ContDiff

theorem leibniz_open_Dz :
    ∀ (j : ℕ) (f g : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.SmoothOpen f →
      Work.FTS.EllipticEst.SmoothOpen g → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DzIter j (fun z θ => f z θ * g z θ) z θ =
        ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
          * (Work.Spaces.DzIter b f z θ * Work.Spaces.DzIter (j - b) g z θ) := by
  intro j f g hf hg z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hfs : Work.EllipticEst.Core.SmoothZ0 (fun z' => f z' θ) := hf.curry_z hθ
  have hgs : Work.EllipticEst.Core.SmoothZ0 (fun z' => g z' θ) := hg.curry_z hθ
  have key := (Work.Spaces.DerivLike.iterate_mul Work.EllipticEst.Core.Zop_DerivLike0
    Work.EllipticEst.Core.SmoothZ0_FunClass j hfs hgs) (show z ∈ Set.Ioi (0 : ℝ) from hz)
  rw [show (fun z' => f z' θ) * (fun z' => g z' θ) = (fun z' => f z' θ * g z' θ)
    from rfl] at key
  rw [congrFun (Work.FTS.LocData.Zop_iterate_slice j (fun z' θ' => f z' θ' * g z' θ') θ) z,
    key]
  exact Finset.sum_congr rfl fun b _ => by
    rw [← congrFun (Work.FTS.LocData.Zop_iterate_slice b f θ) z,
      ← congrFun (Work.FTS.LocData.Zop_iterate_slice (j - b) g θ) z]

end Work.FTS.OpenPkg.ProdOpen
