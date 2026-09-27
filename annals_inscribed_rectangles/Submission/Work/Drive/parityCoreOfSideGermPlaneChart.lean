import Mathlib
import Submission.Work.Drive.sideGermDefs
import Submission.Work.Drive.parityCore_of_dense_count
import Submission.Work.Drive.planeChartDefs
import Submission.Work.Drive.sideGermLocalconstUnconditional

/-!
# The `hdisj`-free assembly: `ParityCore γ` from the germ route's three inputs

`Work.Drive.parityCore_of_sideGerm` (`Submission/Work/Drive/sideGerm.lean:162`) derives
`Work.Drive.ParityCore γ` from the germ side value together with `hn2`, `hdense` — and, importantly,
from the same statement's `hdisj : ∀ x : Zc γ, Disjoint (chartDisk Q) (rotCapping x '' chartDisk Q)` and
`hQ : IsChartData Q`.  The `hdisj` slot is not obtainable from `w ∈ Zc γ` and the chart's clauses (the
`cap ∩ w·cap` piece is a genuine `2`-dimensional condition, and `Zc γ` may accumulate at `0`).

This file records the same conclusion with that slot **deleted**, in the shape the germ lane needs so
that the substitution is a diff rather than a cold start:

* the chart data becomes `hγne`, `hγinj : Function.Injective γ` and `hQ : IsPlaneChart γ hγne Q`;
* the local-constancy bullet is discharged by the *unconditional*
  `Work.Drive.sideGerm_localconst_of_planeChart_unconditional` (this session), not by `hdisj`.

Everything else — the `hn2` bullet, the `hdense` bullet and the call
`parityCore_of_countOnZc_dense (γ := γ) hγ (fun u v => sideGerm Ξ Q c (v - u)) (fun u v => by simp)` —
is copied from `parityCore_of_sideGerm`.  So this statement is *proved today* with `hn2` and `hdense` as
hypotheses, and becomes a proof of `ParityCore γ` with no hypotheses the route cannot supply as soon as
`Drive/hn2_sideGerm_reference` and `Drive/hdense_sideGerm` land; at that point the germ lane can delete
`sideGerm.lean`'s `parityCore_of_sideGerm` and `sideGerm.lean:139`'s old `sideGerm_spec`.
-/

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology

noncomputable section

/-- **`ParityCore γ` from the germ route, with no `hdisj`.** -/
theorem parityCore_of_sideGerm_planeChart {γ : Circle → ℝ × ℝ}
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ γ) {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace) (Q : ℂ → CappingSpace) (c : ℝ)
    (hγne : ∀ x : Circle, γ x ≠ 0) (hγinj : Function.Injective γ)
    (hQ : IsPlaneChart γ hγne Q)
    (hΞ : ChartPert Q m Ξ) (hc : 0 < c) (hcbot : ∀ p ∈ chartDisk Q, c < levelOf p)
    (hn2 : ∀ u v : UnitAddCircle, v - u ∈ Zc γ →
      sideGerm Ξ Q c (v - u) + sideGerm Ξ Q c (u - v) = 1)
    (hdense : ∀ a c' : UnitAddCircle, a ∈ Zc γ → c' ∈ Zc γ → a + c' ∈ Zc γ →
      (a, c') ∈ closure {q : UnitAddCircle × UnitAddCircle |
        q.1 ∈ Zc γ ∧ q.2 ∈ Zc γ ∧ q.1 + q.2 ∈ Zc γ ∧
          sideGerm Ξ Q c q.1 * sideGerm Ξ Q c (q.1 + q.2)
            + sideGerm Ξ Q c (-q.1) * sideGerm Ξ Q c q.2
            + sideGerm Ξ Q c (-(q.1 + q.2)) * sideGerm Ξ Q c (-q.2) = 1}) :
    ParityCore γ := by
  refine parityCore_of_countOnZc_dense (γ := γ) hγ (fun u v => sideGerm Ξ Q c (v - u))
    (fun u v => by simp) ?_ ?_ ?_
  · intro u v hv
    simpa using hn2 u v hv
  · intro x
    rw [nhds_subtype, Filter.eventually_comap]
    filter_upwards [sideGerm_localconst_of_planeChart_unconditional Ξ Q c hγne hγinj hQ hΞ hc
      hcbot x.2] with w hw a ha
    rw [ha]
    simpa using hw
  · intro a c' ha hc' hac
    simpa using hdense a c' ha hc' hac

end

end Work.Drive
