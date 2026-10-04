import Mathlib
import Submission.Diff.Evol
import Submission.Work.Diff.GE.NablaRm
import Submission.Work.Diff.GE.ReactionDefs
import Submission.Work.Diff.GE.frame_deps
import Submission.Work.Diff.GE.derivWithin_Ico_zero
import Submission.Work.Diff.GE.covRmFixedEvol
import Submission.Work.Diff.GE.covRmInteriorAbs
import Submission.Work.Diff.GE.covRmFrameSupplies
import Submission.Work.Diff.GE.covRm_fixed_evol_interior_final
import Submission.Work.Diff.GE.covRm_zero_c1
import Submission.Work.Diff.GE.lapCovRmAt_zero_continuous
import Submission.Work.Diff.GE.continuous_flow_quantities

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The absolute-value evolution estimate for `∇Rm` in a moving orthonormal frame

Assembly of `Work.Diff.GE.covRm_frame_evol_abs`.

* *interior* (`t ∈ Ioo 0 T`): the worked-out estimate `Work.Diff.GE.covRmTimeDeriv` (identity plus
  bound), supplied by the proved `Work.Diff.GE.covRm_fixed_evol_interior_final`, whose hypotheses are
  instantiated by `Work.Diff.GE.rmP_evol_fixed_within` (the curvature evolution
  `Work.Diff.GE.EvolA.rmP_evol_fixed`), `Work.Diff.GE.rmP4_update_hasDerivAt_rmP` (the moving-slot
  product rule), `Work.Diff.GE.reactionFormAt_diff_reactionMap`,
  `Work.Diff.GE.covLapRm_le_lapCovRm_abs'` (the *two-sided* Weitzenböck inequality, proved in
  `Submission/Work/Diff/GE/covRmInteriorAbs.lean`), `Work.Diff.GE.covReactionFormAt_le_reactionMap`,
  `Work.Diff.GE.covReactionFormAt_le_neg_reactionMap` and `Work.Diff.GE.connectionVariation_le`.
* *boundary* (`t = 0`): the limit argument `Work.Diff.GE.covRm_zero_boundary` (proved in
  `Submission/Work/Diff/GE/covRmInteriorAbs.lean`), fed with the continuity at `0` of the covariant
  derivative of the curvature (`Work.Diff.GE.covRm_zero_c1`), of the rough Laplacian `Δ∇Rm`
  (`Work.Diff.GE.lapCovRmAt_zero_continuous`) and of the norms
  (`Work.Diff.GE.normFactor_zero_continuous` below).
* the abstract passage from the fixed-vector estimate to the moving-frame estimate is
  `Work.Diff.GE.covRm_frame_evol_abs_of_pieces` (with `Work.Diff.GE.covRm_fixed_evol_abs` and
  `Work.Diff.GE.frame_evol_of_fixed`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.GE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
  [I.Boundaryless] [T2Space M] [CompactSpace M]

/-- The initial-time continuity of the norm factor `|Rm| |∇Rm| ‖v‖‖a‖‖b‖‖c‖‖d‖` along a Ricci
flow, feeding the boundary case of the fixed-vector estimate. -/
theorem normFactor_zero_continuous (hLC : LCSmooth I M)
    (G : ℝ → SMet I M) (T : ℝ) (hflow : IsRicciFlow G T) (x : M)
    (v a b c d : TangentSpace I x) :
    ContinuousWithinAt
      (fun s : ℝ ↦ Real.sqrt (rmNormSq (G s) x) * Real.sqrt (dRmNormSq (G s) x)
        * (Real.sqrt ((G s).inner x v v) * Real.sqrt ((G s).inner x a a)
          * Real.sqrt ((G s).inner x b b) * Real.sqrt ((G s).inner x c c)
          * Real.sqrt ((G s).inner x d d))) (Set.Ico 0 T) 0 := by
  by_cases hT : T ≤ 0
  · have hset : Set.Ico (0 : ℝ) T = ∅ := Set.Ico_eq_empty (not_lt.mpr hT)
    rw [hset]
    simp [ContinuousWithinAt, nhdsWithin_empty]
  · have hTpos : 0 < T := not_le.mp hT
    have h0mem : (0 : ℝ) ∈ Set.Ico 0 T := ⟨le_refl 0, hTpos⟩
    have hrm : ContinuousWithinAt (fun s : ℝ ↦ rmNormSq (G s) x) (Set.Ico 0 T) 0 :=
      (continuous_flow_quantities (I := I) (M := M) hLC G T hflow x).1
    have hdrm : ContinuousWithinAt (fun s : ℝ ↦ dRmNormSq (G s) x) (Set.Ico 0 T) 0 := by
      set ρ : ℝ := Real.sqrt T / 2 with hρdef
      have hρ : 0 < ρ := by positivity
      have hρT : ρ ^ 2 < T := by
        rw [hρdef, div_pow, Real.sq_sqrt hTpos.le]
        nlinarith
      have hsq := cfq_jointSmooth_sqFlow (I := I) (M := M) G hTpos hρ hρT hflow.1
      have h0 : (0 : ℝ) ∈ Set.Ioo (-ρ) ρ := ⟨by linarith, hρ⟩
      have hc : ContinuousAt (fun t : ℝ ↦ dRmNormSq (cfq_sqFlow G t) x) 0 :=
        cfq_dRmNormSq_continuousAt (I := I) (M := M) hLC isOpen_Ioo hsq h0 x
      refine cfq_continuousWithinAt_of_continuousAt_comp_sq
        (f := fun s : ℝ ↦ dRmNormSq (G s) x)
        (F := fun t : ℝ ↦ dRmNormSq (cfq_sqFlow G t) x) hTpos hc ?_
      intro s hs
      rw [show cfq_sqFlow G (Real.sqrt s) = G s from by
        show G ((Real.sqrt s) ^ 2) = G s
        rw [Real.sq_sqrt hs.1]]
    have hvv : ContinuousWithinAt (fun s : ℝ ↦ (G s).inner x v v) (Set.Ico 0 T) 0 :=
      (hflow.2 0 h0mem x v v).continuousWithinAt
    have haa : ContinuousWithinAt (fun s : ℝ ↦ (G s).inner x a a) (Set.Ico 0 T) 0 :=
      (hflow.2 0 h0mem x a a).continuousWithinAt
    have hbb : ContinuousWithinAt (fun s : ℝ ↦ (G s).inner x b b) (Set.Ico 0 T) 0 :=
      (hflow.2 0 h0mem x b b).continuousWithinAt
    have hcc : ContinuousWithinAt (fun s : ℝ ↦ (G s).inner x c c) (Set.Ico 0 T) 0 :=
      (hflow.2 0 h0mem x c c).continuousWithinAt
    have hdd : ContinuousWithinAt (fun s : ℝ ↦ (G s).inner x d d) (Set.Ico 0 T) 0 :=
      (hflow.2 0 h0mem x d d).continuousWithinAt
    exact ((hrm.sqrt.mul hdrm.sqrt).mul
      ((((hvv.sqrt.mul haa.sqrt).mul hbb.sqrt).mul hcc.sqrt).mul hdd.sqrt))

/-- The `t = 0` estimate for the fixed-vector components, from the interior estimate and the
continuity at `0` of the initial data. -/
theorem covRm_zero_boundary_abs (hLC : LCSmooth I M) (hLV : LCVariation I M) :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ (G : ℝ → SMet I M) (T : ℝ), IsRicciFlow G T →
      ∀ x : M, ∀ v a b c d : TangentSpace I x, ∃ D : ℝ,
        HasDerivWithinAt (fun s ↦ covRm (G s) x v a b c d) D (Set.Ico 0 T) 0 ∧
        |D - lapCovRmAt (G 0) x v a b c d|
          ≤ C₂ * Real.sqrt (rmNormSq (G 0) x) * Real.sqrt (dRmNormSq (G 0) x)
              * (Real.sqrt ((G 0).inner x v v) * Real.sqrt ((G 0).inner x a a)
                * Real.sqrt ((G 0).inner x b b) * Real.sqrt ((G 0).inner x c c)
                * Real.sqrt ((G 0).inner x d d)) := by
  obtain ⟨C₁, hC₁, hInt⟩ := covRm_fixed_evol_interior_final (I := I) (M := M) hLC hLV
    (rmP_evol_fixed_within (I := I) (M := M) hLC hLV)
    (lapRmAt_diff (I := I) (M := M) hLC)
    (reactionFormAt_diff_reactionMap (I := I) (M := M) hLC)
    (rmP4_update_hasDerivAt_rmP (I := I) (M := M) hLC hLV)
    (covLapRm_le_lapCovRm_abs' (I := I) (M := M) hLC)
    (covReactionFormAt_le_reactionMap (I := I) (M := M) hLC)
    (covReactionFormAt_le_neg_reactionMap (I := I) (M := M) hLC)
    (connectionVariation_le (I := I) (M := M) hLC hLV)
  exact covRm_zero_boundary (I := I) (M := M) hLC
    (covRm_zero_c1 (I := I) (M := M) hLC)
    (lapCovRmAt_zero_continuous (I := I) (M := M) hLC)
    (fun G T hflow x v a b c d =>
      normFactor_zero_continuous (I := I) (M := M) hLC G T hflow x v a b c d)
    C₁ hC₁ hInt

theorem covRm_frame_evol_abs
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M) (hLV : Submission.Diff.LCVariation I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (G : ℝ → Submission.Diff.SMet I M) (T : ℝ), Submission.Diff.IsRicciFlow G T →
      ∀ t ∈ Set.Ico 0 T, ∀ x : M,
      ∀ (e : ℝ → Fin (Module.finrank ℝ E) → TangentSpace I x)
        (edot : Fin (Module.finrank ℝ E) → TangentSpace I x) (K : ℝ), 0 ≤ K →
        (∀ᶠ s in nhdsWithin t (Set.Ico 0 T), Submission.Diff.IsONFrame (G s) x (e s)) →
        (∀ i, HasDerivWithinAt (fun s ↦ e s i) (edot i) (Set.Ico 0 T) t) →
        (∀ i, (G t).inner x (edot i) (edot i) ≤ K * Submission.Diff.rmNormSq (G t) x) →
        ∀ m i j k l : Fin (Module.finrank ℝ E), ∃ D : ℝ,
          HasDerivWithinAt
            (fun s ↦ Submission.Diff.covRm (G s) x (e s m) (e s i) (e s j) (e s k) (e s l)) D
            (Set.Ico 0 T) t ∧
          |D - Work.Diff.GE.lapCovRmAt (G t) x (e t m) (e t i) (e t j) (e t k) (e t l)|
              ≤ C * (1 + K) * Real.sqrt (Submission.Diff.rmNormSq (G t) x)
                  * Real.sqrt (Submission.Diff.dRmNormSq (G t) x) := by
  obtain ⟨C₁, hC₁, hInt⟩ := covRm_fixed_evol_interior_final (I := I) (M := M) hLC hLV
    (rmP_evol_fixed_within (I := I) (M := M) hLC hLV)
    (lapRmAt_diff (I := I) (M := M) hLC)
    (reactionFormAt_diff_reactionMap (I := I) (M := M) hLC)
    (rmP4_update_hasDerivAt_rmP (I := I) (M := M) hLC hLV)
    (covLapRm_le_lapCovRm_abs' (I := I) (M := M) hLC)
    (covReactionFormAt_le_reactionMap (I := I) (M := M) hLC)
    (covReactionFormAt_le_neg_reactionMap (I := I) (M := M) hLC)
    (connectionVariation_le (I := I) (M := M) hLC hLV)
  have hZero : ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ (G : ℝ → Submission.Diff.SMet I M) (T : ℝ),
      Submission.Diff.IsRicciFlow G T → ∀ x : M, ∀ v a b c d : TangentSpace I x, ∃ D : ℝ,
      HasDerivWithinAt (fun s ↦ covRm (G s) x v a b c d) D (Set.Ico 0 T) 0 ∧
      |D - lapCovRmAt (G 0) x v a b c d|
        ≤ C₂ * Real.sqrt (rmNormSq (G 0) x) * Real.sqrt (dRmNormSq (G 0) x)
            * (Real.sqrt ((G 0).inner x v v) * Real.sqrt ((G 0).inner x a a)
              * Real.sqrt ((G 0).inner x b b) * Real.sqrt ((G 0).inner x c c)
              * Real.sqrt ((G 0).inner x d d)) :=
    covRm_zero_boundary_abs (I := I) (M := M) hLC hLV
  exact covRm_frame_evol_abs_of_pieces (I := I) (M := M) hLC hLV ⟨C₁, hC₁, hInt⟩ hZero

end Work.Diff.GE
