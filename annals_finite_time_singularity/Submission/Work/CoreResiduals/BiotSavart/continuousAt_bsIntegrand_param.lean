/-
# `Work.CoreResiduals.BiotSavart.continuousAt_bsIntegrand_param`

Joint continuity at `(x₀,t₀)` of the parametrised Biot–Savart derivative integrand
`(x,t) ↦ bsIntegrand (ω(·,t)) x a` for a fixed `a ≠ x₀`.  This is the pointwise
continuity input to the dominated-convergence argument proving continuity of the
parametrised candidate derivative `(x,t) ↦ bsDerivCLM (ω(·,t)) ρ x`.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.CoreResiduals.BiotSavart.IntegrandDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Metric Filter Topology
open scoped Topology

set_option autoImplicit false

namespace Work.CoreResiduals.BiotSavart

open Work.StabilityFar.Decay

/-- **Joint continuity of the parametrised Biot–Savart derivative integrand.**

For a fixed `a ≠ x₀`, the map `(x,t) ↦ bsIntegrand (ω(·,t)) x a` is continuous at `(x₀,t₀)`,
using joint continuity of `ω` at `(x₀,t₀)`, continuity in `t` at `t₀` for each fixed `a`, and
continuity of `crossL` and of `kDerivCLM` away from the diagonal. -/
theorem continuousAt_bsIntegrand_param {ω : Work.LWP.R3 → ℝ → Work.LWP.R3}
    {x₀ : Work.LWP.R3} {t₀ : ℝ}
    (hjoint : ContinuousAt (fun q : Work.LWP.R3 × ℝ => ω q.1 q.2) (x₀, t₀))
    (htcont : ∀ a : Work.LWP.R3, ContinuousAt (fun t : ℝ => ω a t) t₀)
    {a : Work.LWP.R3} (ha : a ≠ x₀) :
    ContinuousAt (fun q : Work.LWP.R3 × ℝ =>
      bsIntegrand (fun y => ω y q.2) q.1 a) (x₀, t₀) := by
  have hOa : ContinuousAt (fun q : Work.LWP.R3 × ℝ => ω a q.2) (x₀, t₀) :=
    (htcont a).comp continuous_snd.continuousAt
  have h1 : ContinuousAt (fun q : Work.LWP.R3 × ℝ => crossL (ω a q.2 - ω q.1 q.2)) (x₀, t₀) :=
    continuous_crossL.continuousAt.comp (hOa.sub hjoint)
  have hsub : ContinuousAt (fun q : Work.LWP.R3 × ℝ => q.1 - a) (x₀, t₀) :=
    continuous_fst.continuousAt.sub continuousAt_const
  have h2 : ContinuousAt (fun q : Work.LWP.R3 × ℝ => kDerivCLM (q.1 - a)) (x₀, t₀) :=
    ContinuousAt.comp (x := (x₀, t₀)) (f := fun q : Work.LWP.R3 × ℝ => q.1 - a) (g := kDerivCLM)
      (continuousAt_kDerivCLM (b := x₀ - a) (sub_ne_zero.mpr (Ne.symm ha))) hsub
  have hcomp := h1.clm_comp h2
  simpa only [bsIntegrand] using hcomp

end Work.CoreResiduals.BiotSavart
