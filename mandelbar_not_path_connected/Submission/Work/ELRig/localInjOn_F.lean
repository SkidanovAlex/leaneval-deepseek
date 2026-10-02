/-
# `Work.ELRig.localInjOn_F` — the holomorphic map `F` is locally injective off its critical set

`Work.EL.F c = (Tsq c)^[5]` is a (holomorphic) polynomial map.  A holomorphic function whose
derivative does not vanish at a point is locally injective there: this is the one-dimensional
case of the inverse function theorem.  We obtain it from Mathlib's inverse function theorem
`HasStrictDerivAt.eventually_left_inverse`, which produces a local left inverse
`HasStrictDerivAt.localInverse` of `f` near `z₁`; a local left inverse is precisely local
injectivity.

The only input on the function is that it is holomorphic, which for `F c` is immediate from
`Tsq c z = (z² + c̄)² + c` being a polynomial.
-/
import Mathlib
import Submission.Work.ELRig.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

namespace Work.ELRig

/-- `Tsq c` is an entire function. -/
theorem differentiable_Tsq (c : ℂ) : Differentiable ℂ (Work.Landing.Tsq c) := by
  show Differentiable ℂ (fun z : ℂ => (z ^ 2 + star c) ^ 2 + c)
  fun_prop

/-- `Work.EL.F c` is an entire function. -/
theorem differentiable_F (c : ℂ) : Differentiable ℂ (Work.EL.F c) := by
  rw [Work.EL.F]
  exact (differentiable_Tsq c).iterate 5

/-- **Local injectivity of `F c` at a point where its derivative does not vanish.**
This is the one-dimensional inverse function theorem: `F c` is holomorphic, hence strictly
differentiable, and a strict derivative that is invertible (i.e. nonzero in dimension one)
admits a local left inverse, which forces injectivity on a neighbourhood. -/
theorem localInjOn_F {c z₁ : ℂ} (hF : deriv (Work.EL.F c) z₁ ≠ 0) :
    ∃ ε > 0, Set.InjOn (Work.EL.F c) (Metric.ball z₁ ε) := by
  have han : AnalyticAt ℂ (Work.EL.F c) z₁ := (differentiable_F c).analyticAt z₁
  have hstrict : HasStrictDerivAt (Work.EL.F c) (deriv (Work.EL.F c) z₁) z₁ :=
    han.hasStrictDerivAt
  have hev : ∀ᶠ x in 𝓝 z₁,
      HasStrictDerivAt.localInverse (Work.EL.F c) (deriv (Work.EL.F c) z₁) z₁ hstrict hF
        (Work.EL.F c x) = x :=
    hstrict.eventually_left_inverse hF
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨ε, hε, ?_⟩
  intro x hx y hy hxy
  have hx' : HasStrictDerivAt.localInverse (Work.EL.F c) (deriv (Work.EL.F c) z₁) z₁ hstrict hF
      (Work.EL.F c x) = x := hsub hx
  have hy' : HasStrictDerivAt.localInverse (Work.EL.F c) (deriv (Work.EL.F c) z₁) z₁ hstrict hF
      (Work.EL.F c y) = y := hsub hy
  rw [hxy] at hx'
  exact hx'.symm.trans hy'

end Work.ELRig
