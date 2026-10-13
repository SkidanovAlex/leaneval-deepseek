/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EComparison/EllPkgCls_E_sub.lean`

The closure `EComparison.EllPkgCls_sub` instantiated at the `E`-difference of two profiles `u`, `v`
of `ClassC`: the pair `(u - v, E u - E v)` is in the packages' class, as soon as the `L₁₂`-part of
the source is additive (the `hΘ` hypothesis, which is what `EComparison.L12_sub_HkMem` supplies:
`Theta α F = (1/(4α))·sin 2θ·L12 F z` is linear in `F` on `z ∈ Iz`).

This puts `E u - E v` on the same footing as `E (u - v)` — the latter being in the class by
`EComparison.EllPkgCls_of_pkg`, since `ClassC` is a subspace (`classC_sub`) and `hEll` therefore
applies to the difference profile.  A statement about *the class* (e.g. the delegated
`EComparison.HomClsSlotsZero`) can then compare the two, which is how the reduction
`EComparison.E_slots_diff_eq` produces the Lipschitz slot inputs of the Picard estimate.

(This lives in its own module and not in `Reduction.lean`, because it needs
`EComparison.EllPkgCls_sub`, which imports `Reduction`.)
-/
import Mathlib.Basic.Real.Basic
import Submission.Work.FTS.StrongEps.EComparison.Reduction
import Submission.Work.FTS.StrongEps.EComparison.EllPkgCls_sub

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.StrongEps.EComparison

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The closure instantiated at the `E`-difference.** -/
theorem EllPkgCls_E_sub_of_theta {α Ce : ℝ} {E : Fn → Fn}
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    {u v : Fn} (hu : Work.FTS.ClassC.ClassC α u) (hv : Work.FTS.ClassC.ClassC α v)
    (hΘ : ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      Work.Construction.Theta α (fun z θ => u z θ - v z θ) z θ
        = Work.Construction.Theta α u z θ - Work.Construction.Theta α v z θ) :
    EllPkgCls α Ce (fun z θ => u z θ - v z θ) (fun z θ => E u z θ - E v z θ) :=
  EllPkgCls_sub (EllPkgCls_of_pkg hEll hu) (EllPkgCls_of_pkg hEll hv) hΘ

end Work.FTS.StrongEps.EComparison
