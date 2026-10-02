/-
# `Work.ELAssembly.b2_locInj_of` — `f_c^6` is injective near the branch point `b₂`

Area `Submission/Work/ELAssembly/` of the mandelbar project.  The assembly `Work.ELAssembly.Main`
needs the field `b2_locInj` of `CertGeometry`: the sixth iterate `F6 c = (Tsq c)^[3]` of the
holomorphic second return map is injective in a neighbourhood of the branch point `b₂`.

The branch point `b₂` is a fixed point of `Tsq c = (T_c)^[2]`, and the critical orbit of the
antiholomorphic quadratic `T_c` never hits `b₂`.  By the chain rule,

  `deriv ((Tsq c)^[k]) z = ∏_{i<k} deriv (Tsq c) ((Tsq c)^[i] z)`,

so the multiplier of an iterate at a point whose orbit stays off the critical orbit is nonzero:
this is `Work.ELRig.deriv_iterate_ne_zero_of_notMem_orbit`.  Applying it to `k = 3` and
`z = b₂` (whose `(Tsq c)`-orbit is the single point `b₂` by `hfix`) gives

  `deriv (F6 c) b₂ ≠ 0`.

Since `F6 c` is an entire function, the one-dimensional inverse function theorem (used in the
same form as in `Work.ELRig.localInjOn_F`) then yields local injectivity at `b₂`.
-/
import Mathlib
import Submission.Work.ELAssembly.Chains
import Submission.Work.ELRig.localInjOn_F
import Submission.Work.ELPull.critValues_tsqIterate

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.ELAssembly

/-- **Local injectivity at a point where the derivative does not vanish** (one-dimensional
inverse function theorem, in the general form used below).  A holomorphic `f : ℂ → ℂ` with
`deriv f z ≠ 0` is injective on some ball around `z`.

`AnalyticAt.hasStrictDerivAt` supplies a strict derivative at `z`, and
`HasStrictDerivAt.eventually_left_inverse` a local left inverse of `f`; a local left inverse is
exactly injectivity on a neighbourhood. -/
theorem localInjOn_of_deriv_ne_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f) {z : ℂ}
    (h : deriv f z ≠ 0) : ∃ ε > 0, Set.InjOn f (Metric.ball z ε) := by
  have han : AnalyticAt ℂ f z := hf.analyticAt z
  have hstrict : HasStrictDerivAt f (deriv f z) z := han.hasStrictDerivAt
  have hev : ∀ᶠ x in 𝓝 z,
      HasStrictDerivAt.localInverse f (deriv f z) z hstrict h (f x) = x :=
    hstrict.eventually_left_inverse h
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨ε, hε, ?_⟩
  intro x hx y hy hxy
  have hx' : HasStrictDerivAt.localInverse f (deriv f z) z hstrict h (f x) = x := hsub hx
  have hy' : HasStrictDerivAt.localInverse f (deriv f z) z hstrict h (f y) = y := hsub hy
  rw [hxy] at hx'
  exact hx'.symm.trans hy'

/-- `Work.ELNest.F6 c = (Tsq c)^[3]` is entire. -/
theorem differentiable_F6 (c : ℂ) : Differentiable ℂ (Work.ELNest.F6 c) := by
  rw [Work.ELNest.F6]
  exact (Work.ELRig.differentiable_Tsq c).iterate 3

/-- **The multiplier of `F6 c` at a fixed point of `Tsq c` off the critical orbit of
`Tantibar c` does not vanish.** -/
theorem deriv_F6_ne_zero_of {c b2 : ℂ} (hfix : Work.Landing.Tsq c b2 = b2)
    (hpost : ∀ n : ℕ, (LeanEval.ComplexAnalysis.Tantibar c)^[n] 0 ≠ b2) :
    deriv (Work.ELNest.F6 c) b2 ≠ 0 := by
  have hfix3 : ((Work.Landing.Tsq c)^[3]) b2 = b2 := Function.iterate_fixed hfix 3
  rw [Work.ELNest.F6]
  exact Work.ELRig.deriv_iterate_ne_zero_of_notMem_orbit (k := 3) (by norm_num) hpost hfix3

/-- **`f_c^6` is locally injective at the branch point `b₂`.**  Under the two hypotheses of the
assembly — `b₂` is fixed by `Tsq c` and the critical orbit of `T_c` misses `b₂` — the sixth
iterate `F6 c = (Tsq c)^[3]` is injective on some ball around `b₂`. -/
theorem b2_locInj_of {c : ℂ} {b2 : ℂ} (hfix : Work.Landing.Tsq c b2 = b2) (hpost : ∀ n : ℕ, (LeanEval.ComplexAnalysis.Tantibar c)^[n] 0 ≠ b2) : ∃ ρ > 0, Set.InjOn (Work.ELNest.F6 c) (Metric.ball b2 ρ) :=
  localInjOn_of_deriv_ne_zero (differentiable_F6 c)
    (deriv_F6_ne_zero_of hfix hpost)

end Work.ELAssembly
