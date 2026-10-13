import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.AngAWeak.SliceGronwallDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngAWeak

theorem sliceGronwallInterface (u : ℝ → ℝ)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4)) :
    ContinuousOn (Work.FTS.EllipticEst.AngAWeak.Fsq u) (Set.Icc θ (Real.pi / 4)) ∧
      ContinuousOn (deriv (Work.FTS.EllipticEst.AngAWeak.Fsq u)) (Set.Icc θ (Real.pi / 4)) ∧
        (∀ x ∈ Set.Icc θ (Real.pi / 4),
          HasDerivAt (Work.FTS.EllipticEst.AngAWeak.Fsq u)
            (deriv (Work.FTS.EllipticEst.AngAWeak.Fsq u) x) x) := by
  -- `Icc θ (π/4)` is contained in the open interval `(0, π/2)` on which `u` is smooth.
  have hI : Set.Icc θ (Real.pi / 4) ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    intro x hx
    exact ⟨lt_of_lt_of_le hθ.1 hx.1, lt_of_le_of_lt hx.2 (by linarith [Real.pi_pos])⟩
  -- On that open interval, `Fsq u = u ^ 2 + (deriv u) ^ 2` is `C^1`: `u` is `C^2`, hence
  -- `deriv u` is `C^1`, and both squares are `C^1`.
  have hFsq : ContDiffOn ℝ 1 (Fsq u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have h2 : ContDiffOn ℝ 2 u (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hsm 2
    have hd : ContDiffOn ℝ 1 (deriv u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      h2.deriv_of_isOpen isOpen_Ioo (by norm_num)
    have h1 : ContDiffOn ℝ 1 u (Set.Ioo (0 : ℝ) (Real.pi / 2)) := (hsm 1).mono (by rfl)
    have hsum : ContDiffOn ℝ 1
        (fun x => (u x) ^ 2 + (deriv u x) ^ 2) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (h1.pow 2).add (hd.pow 2)
    change ContDiffOn ℝ 1 (fun x => (u x) ^ 2 + (deriv u x) ^ 2)
      (Set.Ioo (0 : ℝ) (Real.pi / 2))
    exact hsum
  refine ⟨hFsq.continuousOn.mono hI, ?_, ?_⟩
  · -- `deriv (Fsq u)` is continuous on the open interval, hence on the closed subinterval.
    exact (hFsq.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl).mono hI
  · intro x hx
    exact ((hFsq.differentiableOn one_ne_zero).differentiableAt
      (isOpen_Ioo.mem_nhds (hI hx))).hasDerivAt

end Work.FTS.EllipticEst.AngAWeak
