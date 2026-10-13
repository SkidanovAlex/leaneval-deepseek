import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.Nonlinear.n4norm_exists
import Submission.Work.FTS.EllipticEst.UopHk.GsingFactsInterior

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.OpenPkg

/-- `L₁₂` is (definitionally) the paper's operator `Work.Elliptic.L12`: the iterated integral of
the angular density `∫_θ K(θ) g(s,θ)/s dθ` over `s ∈ (z,∞)`. -/
theorem ellL12_eq_constructionL12 (g : Work.FTS.Galerkin.Fn) (z : ℝ) :
    Work.Elliptic.L12 g z = Work.Construction.L12 g z := rfl

/-- **`z ↦ L₁₂(g)(z)` is differentiable at every `z > 0`** for an interior-smooth honest datum
`g ∈ ℋ⁴`.

`Work.Construction.L12 g` is the paper's `L₁₂` (`Work.Elliptic.L12`), so the statement is a
special case of `Work.FTS.EllipticEst.UopHk.contDiffOn_L12_of_smoothOpen_Hk`, which shows that
`L₁₂(F)` is `C^{k-1}` on `(0,∞)` with derivative `-3 F_*(z)/z` for every
`SmoothOpen F` with `HkMem α k F`, `k ≥ 2`; the hypothesis `HQo α 4 g` unfolds by definition to
exactly `SmoothOpen g ∧ HkMem α 4 g`. -/
theorem l12diff_field :
    ∀ (α : ℝ) (g : Work.FTS.Galerkin.Fn), 0 < α → α ≤ 1 → Work.FTS.VocabO.HQo α 4 g →
      ∀ z ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ (fun z' => Work.Construction.L12 g z') z := by
  intro α g _hα _hα1 hg z hz
  obtain ⟨hopen, hmem⟩ := hg
  have h := (Work.FTS.EllipticEst.UopHk.contDiffOn_L12_of_smoothOpen_Hk α 4 g hopen hmem
    (by norm_num)).2 z hz
  exact h.differentiableAt

end Work.FTS.OpenPkg
