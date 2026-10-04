import Mathlib
import Submission.Work.Diff.GE.EvolB.Zero
import Submission.Work.Diff.GE.EvolB.covRmSliceSmooth_B
import Submission.Work.Diff.GE.EvolB.lapCovRmAt_continuousWithinAt_E

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The fixed-vector evolution estimate for `∇Rm` (`EvolB`)

`Work.Diff.GE.EvolB.hasDerivWithinAt_covRm_le_B` is the full statement of the fixed-vector estimate
for the covariant derivative of the curvature along a Ricci flow (the smooth-level form of the
roadmap lemma `Work.Diff.GE.hasDerivWithinAt_covRm_le`):

`∃ C ≥ 0`, for every Ricci flow `G` on `[0,T)`, every `t ∈ [0,T)`, every `x` and all tangent vectors
`v a b c d`, the component `s ↦ covRm (G s) x v a b c d` has a one-sided derivative at `t` along
`[0,T)`, bounded by `Δ∇Rm` at `t` plus `C |Rm| |∇Rm|` times the metric norms of the five arguments.

It is assembled from

* the **interior** estimate `Work.Diff.GE.EvolB.covRm_fixed_evol_le_interior_B` (`t ∈ (0,T)`), valid
  for `G` jointly smooth on the half-open interval `[0,T)`;
* the **initial-time** estimate `Work.Diff.GE.EvolB.covRm_fixed_evol_le_zero_of` (`t = 0`), which
  uses the reparametrisation `τ ↦ τ²` to turn the half-open interval into an open one, together with
  the two inputs
  `Work.Diff.GE.EvolB.covRmSliceSmooth_B` (the time slice of `∇Rm` is `C^∞` along a jointly smooth
  family) and `Work.Diff.GE.lapCovRmAt_continuousWithinAt_E` (continuity of `Δ∇Rm` at the initial
  time).
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.GE.EvolB

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [I.Boundaryless] [T2Space M] [CompactSpace M]

/-- **The evolution estimate for `∇Rm` under a Ricci flow** (fixed vectors; smooth level). -/
theorem hasDerivWithinAt_covRm_le_B (hLC : LCSmooth I M) (hLV : LCVariation I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (G : ℝ → SMet I M) (T : ℝ), IsRicciFlow G T →
      ∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ v a b c d : TangentSpace I x, ∃ D : ℝ,
        HasDerivWithinAt (fun s ↦ covRm (G s) x v a b c d) D (Set.Ico 0 T) t ∧
        D ≤ Work.Diff.GE.lapCovRmAt (G t) x v a b c d
          + C * Real.sqrt (rmNormSq (G t) x) * Real.sqrt (dRmNormSq (G t) x)
            * (Real.sqrt ((G t).inner x v v) * Real.sqrt ((G t).inner x a a)
              * Real.sqrt ((G t).inner x b b) * Real.sqrt ((G t).inner x c c)
              * Real.sqrt ((G t).inner x d d)) := by
  obtain ⟨C, hC, hInt⟩ := covRm_fixed_evol_le_interior_B (I := I) (M := M) hLC hLV
  refine ⟨C, hC, ?_⟩
  intro G T hflow t ht x v a b c d
  rcases eq_or_lt_of_le ht.1 with h0 | hpos
  · subst h0
    have hSlice : ∀ (G' : ℝ → SMet I M) {J : Set ℝ}, IsOpen J → JointSmooth G' J →
        ∀ t₀ ∈ J, ∀ x : M, ∀ v a b c d : TangentSpace I x,
          ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun t : ℝ ↦ covRm (G' t) x v a b c d) t₀ := by
      intro G' J hJ hG t₀ ht₀ x' v' a' b' c' d'
      exact Work.Diff.GE.EvolB.covRmSliceSmooth_B (I := I) (M := M) hLC hJ hG ht₀ x' v' a' b' c' d'
    have hBcont : ∀ (G' : ℝ → SMet I M) (T : ℝ), IsRicciFlow G' T → ∀ x : M,
        ∀ v a b c d : TangentSpace I x,
          ContinuousWithinAt (fun s : ℝ ↦ Work.Diff.GE.lapCovRmAt (G' s) x v a b c d)
            (Set.Ico 0 T) 0 := by
      intro G' T' hflow' x' v' a' b' c' d'
      exact Work.Diff.GE.lapCovRmAt_continuousWithinAt_E (I := I) (M := M) hLC
        G' T' hflow' x' v' a' b' c' d'
    exact covRm_fixed_evol_le_zero_of (I := I) (M := M) hSlice hBcont hLC hLV hC
      (covRmTimeDerivB_le_interior_of (I := I) (M := M) hLC hLV C hInt)
      G T ht.2 hflow x v a b c d
  · exact hInt G T hflow t ⟨hpos, ht.2⟩ x v a b c d

end Work.Diff.GE.EvolB
