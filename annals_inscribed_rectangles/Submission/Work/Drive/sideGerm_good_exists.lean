import Mathlib
import Submission.Work.Drive.sgAssembly
import Submission.Work.Drive.exists_compact_chart_cover
import Submission.Work.Drive.exists_pos_norm_le_mem_of_compact
import Submission.Work.Drive.range_mfderiv_comp_surjective_linear
import Submission.Work.Drive.chartDiffRangeBridge
import Submission.Work.Drive.exists_forall_good_and_notMem_family_multi
import Submission.Work.Drive.sideGermDefs
import Submission.Work.Drive.genericRegularizationSquare
import Submission.Work.Drive.avoid_zeroSet_open
import Submission.Work.Drive.classTripleAssembly
import Submission.Work.Drive.geometricLocality

namespace Work.Drive

/-- **The Sard existence for the germ route**: good configurations accumulate at `0`.

This is obligation (1) of the proof plan of `Work.Drive.sideGerm_spec` (see the module docstring of
`Submission/Work/Drive/sideGerm.lean`): for every angle `w`, `GoodPair` holds for chart perturbations
of arbitrarily small norm.  Its content is a *parametric Sard* statement for the charted difference
system of the core loop and the clamped sweep on the box `[0,1] × unitBox 2` (a square system: 4
parameters, 4 equations in the 4-manifold `CappingSpace`), whose parameter-derivative is onto at every
zero because `t.1` and `t.2` are independently perturbed (`ChartPert` requires the parameter-derivative
of `t ↦ Ξ t p` to be onto at *every* `p : CappingSpace`) — so `(t.1,t.2) ↦ (loop position) − (sweep
position)` has onto derivative as the sum of the two ranges.  The two `generate`-bricks on disk are
`Work.Drive.exists_forall_good_square_on_compact_ball`
(`Submission/Work/Drive/genericRegularizationSquare.lean`, the `n`-unknowns/`n`-equations Sard on a
compact family) and `Work.Drive.avoid_zeroSet_open`
(`Submission/Work/Drive/avoid_zeroSet_open.lean`, the σ-compact-exhaustion/Baire form for excluding
meets on the box boundary — the boundary faces `q.1 ∈ {0,1}`, `q.2 i ∈ {0,1}` are finitely many
lower-dimensional systems, whose zero sets have empty interior by that lemma, and the union of
finitely many closed sets with empty interior has empty interior, so the good parameters are dense);
`Work.Drive.classTripleAssembly` is the existing worked example of the same pattern (build the
coordinate system of a charted family, produce the small perturbation by the square Sard).

No disjointness hypothesis is needed: `GoodPair` says nothing about the planes being disjoint. -/
theorem sideGerm_good_exists {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → Work.Drive.CappingSpace → Work.Drive.CappingSpace)
    (Q : ℂ → Work.Drive.CappingSpace)
    (c : ℝ) (hΞ : Work.Drive.ChartPert Q m Ξ) (hQ : Work.Drive.IsSmoothChart Q) (hc : 0 < c)
    (w : UnitAddCircle) :
    Filter.Frequently (fun t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) =>
      Work.Drive.GoodAt Ξ Q c w t) (nhds 0) := by
  rw [Filter.frequently_iff]
  intro U hU
  obtain ⟨ε₀, hε₀, hsub⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨p, hpε, hgood⟩ :=
    Work.Drive.sgGoodPair_of_small Ξ Q c hΞ hQ w ε₀ hε₀
  refine ⟨(p, 0), hsub ?_, ?_⟩
  · have h1 : dist (p, (0 : EuclideanSpace ℝ (Fin m))) 0 = ‖p‖ := by
      simp [dist_eq_norm, Prod.norm_def]
    rw [Metric.mem_ball, h1]
    exact hpε
  · simpa [Work.Drive.GoodAt, Work.Drive.pertChart, hΞ.1] using hgood

end Work.Drive
