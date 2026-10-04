import Mathlib
import Submission.Work.Diff.GE.ReactionDefs
import Submission.Work.Diff.GE.NablaRm
import Submission.Work.Diff.GE.EvolB.Zero
import Submission.Work.Diff.GE.EvolB.covRmSliceSmooth
import Submission.Work.Diff.GE.lapCovRmAt_zero_continuous

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The fixed-vector evolution estimate for `∇Rm` along a Ricci flow

There is a universal constant `C ≥ 0` such that along every smooth Ricci flow `G` on `[0,T)`, at
every `t ∈ [0,T)`, every `x : M` and all tangent vectors `v a b c d`, the component
`s ↦ (∇Rm)(G s)(v,a,b,c,d)` has a one-sided derivative `D` at `t` along `[0,T)`, bounded by the
corresponding component of the rough Laplacian `Δ∇Rm` plus `C |Rm| |∇Rm|` times the metric lengths
of the five arguments.  This is the analytic core of the `k = 1` case of the Shi-type estimates
used by the continuation argument of the Brendle–Schoen proof.

The GE area proves this in `Submission/Work/Diff/GE/EvolB/`:

* `Work.Diff.GE.EvolA.rmP_evol_fixed` — the fixed-vector curvature evolution
  `∂ₜ Rm = ΔRm + reactionMap(Rm)` (the classical computation on top of `LCVariation`);
* `Work.Diff.GE.EvolB.covRm_fixed_evol_le_interior_B` — the **interior** estimate (`t ∈ (0,T)`),
  obtained from the exact assembly of the evolution identity `∂ₜ∇Rm = ∇ΔRm + ∇(reactionMap Rm) −
  (connection-variation terms)` together with the three bounds `WeitzBound`, `ReactionBound` and
  `ConnVarB`;
* `Work.Diff.GE.EvolB.covRm_fixed_evol_le_zero_of` — the reduction of the **initial time** `t = 0`
  to the reparametrisation `τ ↦ τ²` (which turns the half-open interval into an open one), with the
  two inputs `Work.Diff.GE.EvolB.covRmSliceSmooth` (smoothness of the time slice) and
  `Work.Diff.GE.lapCovRmAt_zero_continuous` (continuity of `Δ∇Rm` at the initial time) supplied here
  by their proved forms.  This file is the `EXT`-area re-export of the resulting theorem.

Nothing in this file depends on a placeholder proof.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.evolX

theorem covRm_fixed_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M) (hLV : Submission.Diff.LCVariation I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (G : ℝ → Submission.Diff.SMet I M) (T : ℝ),
      Submission.Diff.IsRicciFlow G T →
      ∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ v a b c d : TangentSpace I x, ∃ D : ℝ,
        HasDerivWithinAt (fun s => Submission.Diff.covRm (G s) x v a b c d) D (Set.Ico 0 T) t ∧
        D ≤ Work.Diff.GE.lapCovRmAt (G t) x v a b c d
          + C * Real.sqrt (Submission.Diff.rmNormSq (G t) x)
              * Real.sqrt (Submission.Diff.dRmNormSq (G t) x)
            * (Real.sqrt ((G t).inner x v v) * Real.sqrt ((G t).inner x a a)
              * Real.sqrt ((G t).inner x b b) * Real.sqrt ((G t).inner x c c)
              * Real.sqrt ((G t).inner x d d)) := by
  obtain ⟨C, hC, hInt⟩ :=
    Work.Diff.GE.EvolB.covRm_fixed_evol_le_interior_B (I := I) (M := M) hLC hLV
  refine ⟨C, hC, ?_⟩
  intro G T hflow t ht x v a b c d
  rcases eq_or_lt_of_le ht.1 with h0 | hpos
  · subst h0
    refine Work.Diff.GE.EvolB.covRm_fixed_evol_le_zero_of (I := I) (M := M) ?_ ?_ hLC hLV hC
      (Work.Diff.GE.EvolB.covRmTimeDerivB_le_interior_of (I := I) (M := M) hLC hLV C hInt)
      G T ht.2 hflow x v a b c d
    · intro G' J hJ hG t₀ ht₀ x' v' a' b' c' d'
      exact Work.Diff.GE.EvolB.covRmSliceSmooth (I := I) (M := M) hLC hJ hG ht₀ x' v' a' b' c' d'
    · intro G' T' hflow' x' v' a' b' c' d'
      exact Work.Diff.GE.lapCovRmAt_zero_continuous (I := I) (M := M) hLC G' T' hflow'
        x' v' a' b' c' d'
  · exact hInt G T hflow t ⟨hpos, ht.2⟩ x v a b c d

end Work.Diff.EXT.evolX
