import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.remov.cosBarIdents
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.EllipticEst.remov.slice_v_identities

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

theorem slice_gprime_v_ident (u g : ℝ → ℝ)
    (hu : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)))
    (hg : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv g θ
        = - Real.cos θ * deriv (fun t => deriv (fun s => deriv (fun r => u r / Real.cos r) s) t) θ
          + 4 * Real.sin θ * deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ
          - Real.cos θ * deriv (fun s => u s / Real.cos s) θ
          + 4 * Real.sin θ * (u θ / Real.cos θ) := by
  intro θ hθ
  -- `deriv g θ = deriv (Lzero1 u) θ`, expanded in terms of `u` (proved in
  -- `slice_gprime_ident`)
  have hg' := slice_gprime_ident u g hu hg θ hθ
  -- the three `u`-derivatives in terms of `v = u / cos θ` (`slice_v_identities`)
  obtain ⟨-, hu3, htu2, hu1⟩ := slice_v_identities u hu θ hθ
  rw [hg', hu3, htu2, hu1]
  ring

end Work.FTS.EllipticEst.remov
