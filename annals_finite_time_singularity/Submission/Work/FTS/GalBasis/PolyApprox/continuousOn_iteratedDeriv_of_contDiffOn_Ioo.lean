import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalBasis.PolyApprox

theorem continuousOn_iteratedDeriv_of_contDiffOn_Ioo {f : ℝ → ℝ} {c d a b : ℝ}
    (hC : ContDiffOn ℝ 4 f (Set.Ioo c d)) (hsub : Set.Icc a b ⊆ Set.Ioo c d)
    {i : ℕ} (hi : i ≤ 4) : ContinuousOn (iteratedDeriv i f) (Set.Icc a b) := by
  have h : ContinuousOn (iteratedDeriv i f) (Set.Ioo c d) := by
    have h1 : ContinuousOn (iteratedDerivWithin i f (Set.Ioo c d)) (Set.Ioo c d) :=
      ((contDiffOn_nat_iff_continuousOn_differentiableOn_deriv
        (𝕜 := ℝ) (n := 4) (f := f) (isOpen_Ioo.uniqueDiffOn)).mp hC).1 i hi
    exact h1.congr fun x hx => ((iteratedDerivWithin_of_isOpen (n := i) isOpen_Ioo) hx).symm
  exact h.mono hsub

end Work.FTS.GalBasis.PolyApprox
