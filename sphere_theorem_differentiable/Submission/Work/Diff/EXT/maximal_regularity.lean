import Mathlib
import Submission.Work.Diff.EXT.maximal_regularity_glue
import Submission.Work.Diff.EXT.local_ext_closed
import Submission.Work.Diff.EXT.twoSided_of_within

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Regularity at the maximal time of a Ricci flow

`Work.Diff.EXT.maximal_regularity`: a smooth Ricci flow `G` on `[0,T)` with curvature bounded by `C`
extends to a jointly smooth family on a neighbourhood of `[0,T]`.

The proof is the (proved) reduction `maximal_regularity_of_inputs` of
`Submission/Work/Diff/EXT/maximal_regularity_glue.lean`, applied to the `H`-input
`local_ext_of_bounded_curv_closed` (`Submission/Work/Diff/EXT/local_ext_closed.lean`: Shi's
estimates ⟹ chart bounds ⟹ smooth extension across `T`) and the `K`-input `twoSided_of_within`
(the Borel/Whitney jet-matching extension to the left of `0`).

## State (updated)

`#print axioms Work.Diff.EXT.maximal_regularity` depends on `sorryAx` through exactly three
declarations (found by walking the dependency graph of the proof term):

* `Work.Diff.EXT.ConnCov.covKAExt_bound` (the `∇^{G 0}`-tower bounds of the connection difference,
  used by `conn_diff_cov_bounds` and hence by `chartBounds_of_shibounds`);
* `Work.Diff.EXT.ladderEfD_base` (the level-`0` reaction `R_0 = Q(Rm)` with all its jets);
* `Work.Diff.EXT.ladderEfD_step` (the recursion `R_{k+1} = ∇R_k + B_k` at the level of jets).

Everything else in the cone is `sorry`-free, in particular the Weitzenböck commutator `[Δ,∇]` of the
curvature tower, `Work.Diff.EXT.lapComm_tower`
(`Submission/Work/Diff/EXT/lapComm_tower.lean`, proved — assembled from the single-slot identity
`Work.Diff.EXT.lapCommInsT`/`Work.Diff.EXT.lapComm_insT`, the product rule
`Work.Diff.EXT.curvActT_deriv` and the componentwise bounds in that file) and its two supporting
modules `Submission/Work/Diff/EXT/lapComm_curvActT_deriv.lean` and
`Submission/Work/Diff/EXT/lapCommTowerFinal.lean`.  The one-sided curvature evolution at the initial
time is `Work.Diff.EXT.rmP_derivWithin_Ioi`
(`Submission/Work/Diff/EXT/rmP_derivWithin_Ioi.lean`), needed by `ladderEfD_base`.

Once those three land, `maximal_regularity` below needs no change.
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT


/-- **Regularity at the maximal time.**  A smooth Ricci flow `G` on `[0,T)` all of whose curvature
components in orthonormal frames are bounded by `C` extends to a *jointly smooth* family on a
neighbourhood of `[0,T]`: there are `ε > 0` and a smooth family `G'` with `G' = G` on `[0,T)`.
This is the `C^∞`-convergence step of the continuation theorem (Shi's local derivative estimates,
the metric equivalence `e^{-λt} g(0) ≤ g(t) ≤ e^{λt} g(0)`, and the bounded-geometry arguments in a
fixed finite atlas).  `(⊤ : ℕ∞)` is smoothness (`∞`), not analyticity. -/
theorem maximal_regularity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (G : ℝ → Submission.Diff.SMet I M) (T C : ℝ) (hT : 0 < T)
    (hflow : Submission.Diff.IsRicciFlow G T)
    (hbound : ∀ t ∈ Set.Ico 0 T, Submission.Diff.CurvBound (G t) C) :
    ∃ ε > 0, ∃ G' : ℝ → Submission.Diff.SMet I M,
      Submission.Diff.JointSmooth G' (Set.Ioo (-ε) (T + ε)) ∧ ∀ t ∈ Set.Ico 0 T, G' t = G t := by
  -- The `H`-input (the local extension across `T`) is provided by
  -- `Work.Diff.EXT.local_ext_of_bounded_curv_closed` (`Submission/Work/Diff/EXT/local_ext_closed.lean`),
  -- which instantiates the sorry-free reduction `local_ext_assembly` with the proved
  -- `ShiBounds` (`shibounds_of_interfaces`), `metric_equiv_of_curvBound`,
  -- `chartBounds_of_shibounds` and `local_ext_of_chart_bounds_v2`.
  -- The `K`-input (the extension to the left of `0`) is `twoSided_of_within` (proved).
  have hbound' : ∀ t ∈ Set.Ico 0 T, Submission.Diff.CurvBound (G t) (max C 0) := by
    intro t ht x e he i j k l
    exact le_trans (hbound t ht x e he i j k l) (le_max_left C 0)
  exact maximal_regularity_of_inputs (I := I) (M := M) G T hT hflow.1
    (local_ext_of_bounded_curv_closed (I := I) (M := M) G T (max C 0) hT hflow hbound')
    (twoSided_of_within (I := I) (M := M) G T hT hflow.1)

end Work.Diff.EXT
