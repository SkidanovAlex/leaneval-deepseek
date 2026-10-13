import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.remov.cosBarIdents

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology
open Filter

namespace Work.FTS.EllipticEst.remov

theorem slice5_idents (u g : ℝ → ℝ)
    (hu : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)))
    (hode : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) :
    (∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 u θ
        = -Real.cos θ * deriv (deriv (fun θ' => u θ' / Real.cos θ')) θ
          + 3 * Real.sin θ * deriv (fun θ' => u θ' / Real.cos θ') θ
          - 4 * Real.cos θ * (u θ / Real.cos θ)) ∧
    (∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv (deriv u) θ = Real.sin θ * deriv (fun θ' => u θ' / Real.cos θ') θ
        - 5 * Real.cos θ * (u θ / Real.cos θ) - g θ) ∧
    (∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv (deriv (deriv u)) θ
        = Real.sin θ * deriv (deriv (fun θ' => u θ' / Real.cos θ')) θ
          - 4 * Real.cos θ * deriv (fun θ' => u θ' / Real.cos θ') θ
          + 5 * Real.sin θ * (u θ / Real.cos θ) - deriv g θ) ∧
    (∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv (deriv (deriv (deriv u))) θ
        = Real.sin θ * deriv (deriv (deriv (fun θ' => u θ' / Real.cos θ'))) θ
          - 3 * Real.cos θ * deriv (deriv (fun θ' => u θ' / Real.cos θ')) θ
          + 9 * Real.sin θ * deriv (fun θ' => u θ' / Real.cos θ') θ
          + 5 * Real.cos θ * (u θ / Real.cos θ) - deriv (deriv g) θ) := by
  -- `cosBarIdents` gives the same four identities with `Lzero1 u` in place of `g`;
  -- `g` agrees with `Lzero1 u` on the whole interval, hence to first and second order
  -- near each interior point.
  have hCBI := cosBarIdents hu
  have hcong : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 u =ᶠ[𝓝 θ] g := by
    intro θ hθ
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with t ht
    exact hode t ht
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro θ hθ
    exact (hCBI θ hθ).1
  · intro θ hθ
    rw [(hCBI θ hθ).2.1, hode θ hθ]
  · intro θ hθ
    have hd : deriv (Work.FTS.EllipticEst.Lzero1 u) θ = deriv g θ :=
      (hcong θ hθ).deriv_eq
    rw [(hCBI θ hθ).2.2.1, hd]
  · intro θ hθ
    have hd : deriv (deriv (Work.FTS.EllipticEst.Lzero1 u)) θ = deriv (deriv g) θ :=
      ((hcong θ hθ).deriv).deriv_eq
    rw [(hCBI θ hθ).2.2.2, hd]

end Work.FTS.EllipticEst.remov
