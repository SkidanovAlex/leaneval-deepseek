import Submission.Commons.Topology.Winding.hasArg_homotopy_invariant

/-!
# Wrapper exposing the winding-number machinery to `Submission/Work` lemmas

`Submission.Commons.Topology.Winding.HasArg f p` says that the closed curve `t ↦ f t - p` admits a
continuous `1`-periodic argument function, i.e. that it has winding number zero around `p`.

This module re-exports that machinery (and `hasArg_homotopy_invariant`) so that lemmas living under
`Submission/Work` can be stated in terms of it, and defines the round circle as a `1`-periodic
curve.
-/

namespace Work.Topology.Surface

open Set Metric

noncomputable section

/-- The round circle of radius `r` about `c`, as a `1`-periodic parametrised curve. -/
def circleCurve (c : ℂ) (r : ℝ) : ℝ → ℂ :=
  fun t => c + (r : ℂ) * Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)

@[simp] lemma circleCurve_apply (c : ℂ) (r t : ℝ) :
    circleCurve c r t = c + (r : ℂ) * Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) := rfl

end

end Work.Topology.Surface
