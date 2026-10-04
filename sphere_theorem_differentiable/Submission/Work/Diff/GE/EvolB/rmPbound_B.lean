import Mathlib
import Submission.Work.Diff.GE.EvolB.NrmBounds
import Submission.Work.Diff.GE.rmP_norm_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The smooth-level bound `|Rm(u,b,c,d)| ≤ |Rm| |u| |b| |c| |d|` (`EvolB`)

`Work.Diff.GE.rmP_norm_bound_smooth` (in `Submission/Work/Diff/GE/connectionVariation_le.lean`)
carries the smooth-level proof of this bound, but that module's transitive closure pulls in
`Submission.Work.Diff.GE.covReactionFormAt_le_A`, which is being edited by another agent, so the
proof is re-run here (`EvolB` builds only on `rmP_norm_bound.lean`, whose auxiliary lemmas
`rmP_sum_four_extracted`, `onFrame_parseval_sq`, `sum4_coeff_sq_le` are already at the smooth
level and `sorry`-free).
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.GE.EvolB

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- `|rmP g x u b c d| ≤ |Rm| |u| |b| |c| |d|`, at the smooth level, in `nrm` notation. -/
theorem rmP_norm_le_B [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : LCSmooth I M) :
    ∀ (g : SMet I M) (x : M) (u b c d : TangentSpace I x),
      |rmP g x u b c d|
        ≤ Real.sqrt (rmNormSq g x) * nrm g x u * nrm g x b * nrm g x c * nrm g x d := by
  intro g x u b c d
  have hmain : |rmP g x u b c d|
      ≤ Real.sqrt (rmNormSq g x)
        * (Real.sqrt (g.inner x u u) * (Real.sqrt (g.inner x b b)
          * (Real.sqrt (g.inner x c c) * Real.sqrt (g.inner x d d)))) := by
    by_cases hn : 0 < Module.finrank ℝ E
    · have hkey := Work.Diff.GE.rmP_expansion hLC g x hn u b c d
      have hSU := Work.Diff.GE.onFrame_parseval_sq g x hn u
      have hSB := Work.Diff.GE.onFrame_parseval_sq g x hn b
      have hSC := Work.Diff.GE.onFrame_parseval_sq g x hn c
      have hSD := Work.Diff.GE.onFrame_parseval_sq g x hn d
      have hR : 0 ≤ rmNormSq g x := by
        show 0 ≤ ∑ i, ∑ j, ∑ k, ∑ l, rmC g x i j k l ^ 2
        exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
          Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => sq_nonneg _
      have hU : 0 ≤ g.inner x u u := by
        rw [← hSU]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
      have hB : 0 ≤ g.inner x b b := by
        rw [← hSB]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
      have hC : 0 ≤ g.inner x c c := by
        rw [← hSC]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
      have hD : 0 ≤ g.inner x d d := by
        rw [← hSD]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
      have hcs := Work.Diff.GE.sum4_coeff_sq_le (A := rmC g x)
        (a := fun i => g.inner x (onFrame g x i) u)
        (b := fun j => g.inner x (onFrame g x j) b)
        (c := fun k => g.inner x (onFrame g x k) c)
        (d := fun l => g.inner x (onFrame g x l) d)
      have hsq : (rmP g x u b c d) ^ 2
          ≤ rmNormSq g x * (g.inner x u u * (g.inner x b b * (g.inner x c c
              * g.inner x d d))) := by
        rw [hkey]
        refine le_trans hcs ?_
        rw [hSU, hSB, hSC, hSD]
        exact le_rfl
      have hsqrt : Real.sqrt (rmNormSq g x *
            (g.inner x u u * (g.inner x b b * (g.inner x c c * g.inner x d d))))
          = Real.sqrt (rmNormSq g x) * (Real.sqrt (g.inner x u u)
              * (Real.sqrt (g.inner x b b) * (Real.sqrt (g.inner x c c)
                * Real.sqrt (g.inner x d d)))) := by
        rw [Real.sqrt_mul hR, Real.sqrt_mul hU, Real.sqrt_mul hB, Real.sqrt_mul hC]
      calc |rmP g x u b c d| = Real.sqrt ((rmP g x u b c d) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
        _ ≤ Real.sqrt (rmNormSq g x *
              (g.inner x u u * (g.inner x b b * (g.inner x c c * g.inner x d d)))) :=
            Real.sqrt_le_sqrt hsq
        _ = Real.sqrt (rmNormSq g x) * (Real.sqrt (g.inner x u u)
              * (Real.sqrt (g.inner x b b) * (Real.sqrt (g.inner x c c)
                * Real.sqrt (g.inner x d d)))) := hsqrt
    · have h0 : Module.finrank ℝ E = 0 := Nat.eq_zero_of_not_pos hn
      have hzero : ∀ v : E, v = 0 := finrank_zero_iff_forall_zero.mp h0
      have hu : u = 0 := hzero u
      have hb : b = 0 := hzero b
      have hc : c = 0 := hzero c
      have hd : d = 0 := hzero d
      rw [hu, hb, hc, hd]
      simp [rmP]
  calc |rmP g x u b c d|
      ≤ Real.sqrt (rmNormSq g x)
        * (Real.sqrt (g.inner x u u) * (Real.sqrt (g.inner x b b)
          * (Real.sqrt (g.inner x c c) * Real.sqrt (g.inner x d d)))) := hmain
    _ = Real.sqrt (rmNormSq g x) * nrm g x u * nrm g x b * nrm g x c * nrm g x d := by
        rw [nrm_eq_sqrt, nrm_eq_sqrt, nrm_eq_sqrt, nrm_eq_sqrt]
        ring

end Work.Diff.GE.EvolB
