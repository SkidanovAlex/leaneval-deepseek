import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.H2.Transport3Aux.power_hardy_boundary
import Submission.Work.FTS.H2.Transport3Aux.sin_weight_hardy
import Submission.Work.FTS.H2.Transport3Aux.sin_hardy_weak
import Submission.Work.FTS.EllSol.VthAux.traceAux.PowerHardyTrunc
import Submission.Work.FTS.EllSol.VthAux.traceAux.hardySinWeight
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.power_hardy_interval
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.setIntegral_Ioc_le_of_uniform_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `thetaHardyA` : the angular weighted Hardy inequality in the open class

The target is

```
∃ C > 0, ∀ α ∈ (0,1], ∀ f, C¹ on (0,π/2) →
  ∫_{Iθ} f² sin(2θ)^{-(1-α/10)} ≤ C/α² ∫_{Iθ} (sin(2θ) f')² sin(2θ)^{-γ} + C/α f(π/4)²
```

with `γ = 1 + α/10` (`Work.Spaces.gam`).  Setting `β = α/10`, the two weights are
`sin(2θ)^{β-1}` on the left and `sin(2θ)^{1-β}` on `(f')²` on the right, i.e. exactly the
sharp `sin(2θ)`-weighted Hardy pair with the *interior* boundary term at `π/4`
(`Work.FTS.H2.Transport3Aux.sin_weight_hardy`), but the hypothesis on `f` is only `C¹` on the
*open* interval — no continuity of `f` or of `deriv f` at `0` or `π/2` is available, and the
left-hand side is not assumed integrable.

The route is the standard truncation one:

* on a compact subinterval `[δ, π/4]` the power-weight Hardy inequality
  `Work.FTS.StrongPersist.N6Trans.SixRoute.power_hardy_interval` (delegated, sibling module)
  applies; comparing `sin(2θ)` with `θ` by Jordan's inequality and using
  `(4/π)^{β-1}(4/β²)(π/4)^{β+1} = 4/β²(π/4)²`, `(4/π)^{β-1}(2/β)(π/4)^β = π/(2β)`
  turns it into the truncated `sin`-weighted bound;
* the truncated bounds are uniform in `δ`, the left-hand integrand is
  `IntegrableOn (0,π/4)` by the truncation principle
  `Work.FTS.EllSol.VthAux.traceAux.integrableOn_of_forall_Ioc_le`, and the inequality passes
  to the limit `δ → 0⁺` by the monotone convergence lemma
  `Work.FTS.StrongPersist.N6Trans.SixRoute.setIntegral_Ioc_le_of_uniform_bound` (delegated);
* the right half `(π/4, π/2)` is the same statement for the mirror `u ↦ f(π/2 - u)`
  (under which `sin 2θ` is invariant), transported back with
  `Work.FTS.H2.Transport3Aux.mirror_sq_sin_rpow`, `...mirror_deriv_sq_integral_weak` and
  `Work.FTS.EllSol.VthAux.traceAux.reflectIntegrableOn_iff`.

The constants: `4/β²(π/4)² = 25π²/α² ≤ 40000/α²` and `π/β = 10π/α ≤ 40000/α`, so `C = 40000`
works.
-/

namespace Work.FTS.StrongPersist.N6Trans.SixRoute

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option maxHeartbeats 2000000

/- ## The two truncated-Hardy inputs

These are the delegated lemmas `FTS/StrongPersist/N6Trans/SixRoute/power_hardy_interval` and
`FTS/StrongPersist/N6Trans/SixRoute/setIntegral_Ioc_le_of_uniform_bound`, imported above. -/

/-! ## Elementary pointwise facts -/

/-- `sin (2θ) ≥ 0` on `Iθ`. -/
theorem sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `sin (2θ) > 0` for `0 < θ < π/2`. -/
theorem sin_two_pos_of_lt_half {θ : ℝ} (h0 : 0 < θ)
    (h2 : θ < Real.pi / 2) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)

/-- `HasDerivAt` for a `C¹` function on the open angular interval. -/
theorem hasDerivAt_of_contDiffOn_one {f : ℝ → ℝ}
    (hsm : ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2))) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : HasDerivAt f (deriv f θ) θ :=
  ((hsm.contDiffAt (Ioo_mem_nhds hθ.1 hθ.2)).differentiableAt_one).hasDerivAt

/-- The mirror of a `C¹` function on the open interval is `C¹`. -/
theorem contDiffOn_mirror_open {f : ℝ → ℝ}
    (hsm : ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ 1 (fun u : ℝ => f (Real.pi / 2 - u)) (Set.Ioo 0 (Real.pi / 2)) :=
  hsm.comp ((contDiffOn_const (c := Real.pi / 2)).sub contDiffOn_id)
    (fun x hx => ⟨by linarith [hx.2, Real.pi_pos], by linarith [hx.1]⟩)

end

end Work.FTS.StrongPersist.N6Trans.SixRoute
