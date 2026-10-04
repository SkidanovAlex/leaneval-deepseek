import Mathlib
import Submission.Work.Diff.GE.covRmFixedEvolDefs
import Submission.Work.Diff.GE.reaction_map_defs
import Submission.Work.Diff.GE.react.rmReact_contDiff
import Submission.Work.Diff.GE.react.rmReact_fderiv_bound
import Submission.Work.Diff.GE.react.rmReact_rot
import Submission.Work.Diff.GE.react.Xact_rot_clean
import Submission.Work.Diff.GE.EvolA.rmP_evol_fixed
import Submission.Work.Diff.GE.EvolA.rmReact_norm_le
import Submission.Work.Diff.GE.EvolB.rmP4_update_hasDerivAt_B
import Submission.Work.Diff.GE.lapRmAt_diff
import Submission.Work.Diff.GE.reactionFormAt_diff
import Submission.Work.Diff.GE.covLapRm_le_lapCovRm_abs
import Submission.Work.Diff.GE.covReactionFormAt_le_A
import Submission.Work.Diff.GE.connectionVariation_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Instantiations of the hypotheses of `Work.Diff.GE.covRm_fixed_evol_interior_final`

This file exhibits, for `F = Work.Diff.GE.reactionMap`, the hypotheses of the fixed-vector
evolution estimate `Work.Diff.GE.covRm_fixed_evol_interior_final` from the already proved pieces
of the workspace (`EvolA.rmP_evol_fixed`, `EvolB.rmP4_update_hasDerivAt_B`, `lapRmAt_diff`,
`reactionFormAt_diff`, `covLapRm_le_lapCovRm_abs`, `covReactionFormAt_le_A`,
`connectionVariation_le`, `react.rmReact_*`, `EvolA.reactionMap_norm_le`).
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.GE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
  [I.Boundaryless] [T2Space M] [CompactSpace M]

/-- `Work.Diff.GE.reactionMap` is `Work.Diff.GE.rmReact`. -/
theorem reactionMap_eq (n : ℕ) :
    (Work.Diff.GE.reactionMap : Curv4 n → Curv4 n) = Work.Diff.GE.rmReact n :=
  funext fun R => Work.Diff.GE.EvolA.reactionMap_eq_rmReact R

theorem reactionMap_contDiff (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.GE.reactionMap : Curv4 n → Curv4 n) := by
  rw [reactionMap_eq n]; exact react.rmReact_contDiff n

theorem reactionMap_fderiv_bound (n : ℕ) :
    ∃ CF' : ℝ, 0 ≤ CF' ∧ ∀ R : Curv4 n,
      ‖fderiv ℝ (Work.Diff.GE.reactionMap : Curv4 n → Curv4 n) R‖ ≤ CF' * ‖R‖ := by
  obtain ⟨C, hC, hb⟩ := react.rmReact_fderiv_bound n
  refine ⟨C, hC, fun R => ?_⟩
  rw [reactionMap_eq n]; exact hb R

/-- `Work.Diff.GE.reactionMap` is equivariant under the orthogonal action.  This replaces the route
through `Work.Diff.GE.react.rmReact_rot` (which is built on the *stated but unproved*
`Work.Diff.GE.react.Xact_rot`) by the proved `Work.Diff.GE.react.Xact_rot_clean`, so that every
consumer of this lemma is free of `sorryAx`. -/
theorem reactionMap_rot (n : ℕ) :
    ∀ A ∈ Matrix.orthogonalGroup (Fin n) ℝ, ∀ R : Curv4 n,
      (Work.Diff.GE.reactionMap : Curv4 n → Curv4 n) (rot A R) = rot A (Work.Diff.GE.reactionMap R) := by
  intro A hA R
  rw [reactionMap_eq n]
  show (fun R => Submission.Diff.Alg.Q R - Work.Diff.Evol.Xact R) (Submission.Diff.Alg.rot A R)
    = Submission.Diff.Alg.rot A ((fun R => Submission.Diff.Alg.Q R - Work.Diff.Evol.Xact R) R)
  rw [show (fun R => Submission.Diff.Alg.Q R - Work.Diff.Evol.Xact R)
      (Submission.Diff.Alg.rot A R)
      = Submission.Diff.Alg.Q (Submission.Diff.Alg.rot A R)
        - Work.Diff.Evol.Xact (Submission.Diff.Alg.rot A R) from rfl,
    react.Q_rot n A hA R, react.Xact_rot_clean n A hA R, react.rot_sub]

/-- The fixed-vector curvature evolution (the `hEvol` hypothesis of the final interior estimate). -/
theorem rmP_evol_fixed_within (hLC : LCSmooth I M) (hLV : LCVariation I M) :
    ∀ (G : ℝ → SMet I M) (T : ℝ), IsRicciFlow G T →
      ∀ t ∈ Set.Ioo 0 T, ∀ x : M, ∀ a b c d : TangentSpace I x,
      HasDerivWithinAt (fun s ↦ rmP (G s) x a b c d)
        (Work.Diff.GE.lapRmAt (G t) x a b c d
          + Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap (G t) x a b c d)
        (Set.Ico 0 T) t :=
  fun G T hGF t ht x a b c d =>
    (Work.Diff.GE.EvolA.rmP_evol_fixed hLC hLV G T hGF t ht x a b c d).hasDerivWithinAt

/-- The moving-slot product rule for `rmP` with `F = reactionMap` (the `hP13` hypothesis). -/
theorem rmP4_update_hasDerivAt_rmP (hLC : LCSmooth I M) (hLV : LCVariation I M) :
    ∀ (G : ℝ → SMet I M) (T : ℝ), IsRicciFlow G T →
      ∀ t ∈ Set.Ioo 0 T, ∀ x : M, ∀ (p : Fin 4 → TangentSpace I x) (j : Fin 4)
        (w : ℝ → TangentSpace I x) (w' : TangentSpace I x),
      HasDerivAt w w' t →
      HasDerivAt
        (fun s ↦ rmP (G s) x ((Function.update p j (w s)) 0)
          ((Function.update p j (w s)) 1) ((Function.update p j (w s)) 2)
          ((Function.update p j (w s)) 3))
        (Work.Diff.GE.lapRmAt (G t) x ((Function.update p j (w t)) 0)
            ((Function.update p j (w t)) 1) ((Function.update p j (w t)) 2)
            ((Function.update p j (w t)) 3)
          + Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap (G t) x
              ((Function.update p j (w t)) 0) ((Function.update p j (w t)) 1)
              ((Function.update p j (w t)) 2) ((Function.update p j (w t)) 3)
          + rmP (G t) x ((Function.update p j w') 0)
              ((Function.update p j w') 1) ((Function.update p j w') 2)
              ((Function.update p j w') 3)) t :=
  fun G T hGF t ht x p j w w' hw => by
    simpa only [Work.Diff.GE.EvolB.rmP4B, Work.Diff.GE.EvolB.lapRm4,
      Work.Diff.GE.EvolB.react4] using
      (Work.Diff.GE.EvolB.rmP4_update_hasDerivAt_B (I := I) (M := M) hLC hLV hGF ht x p j w w' hw)

/-- The differentiability of the reaction expression along a metric (the `hReactD` hypothesis). -/
theorem reactionFormAt_diff_reactionMap (hLC : LCSmooth I M) :
    ∀ (g : SMet I M) (x : M) (A B C D : Π y : M, TangentSpace I y),
      SmoothField (I := I) (M := M) A → SmoothField (I := I) (M := M) B →
      SmoothField (I := I) (M := M) C → SmoothField (I := I) (M := M) D →
      MDifferentiableAt I (modelWithCornersSelf ℝ ℝ)
        (fun y : M ↦ reactionFormAt Work.Diff.GE.reactionMap g y (A y) (B y) (C y) (D y)) x :=
  reactionFormAt_diff (I := I) (M := M) hLC
    (Work.Diff.GE.reactionMap : Curv4 (Module.finrank ℝ E) → Curv4 (Module.finrank ℝ E))
    (reactionMap_contDiff (Module.finrank ℝ E)) (reactionMap_rot (Module.finrank ℝ E))

/-- The reaction-derivative bound for `F = reactionMap` (the `hReactB` hypothesis). -/
theorem covReactionFormAt_le_reactionMap (hLC : LCSmooth I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (G : ℝ → SMet I M) (T : ℝ), IsRicciFlow G T →
      ∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ v a b c d : TangentSpace I x,
      Work.Diff.GE.covReactionFormAt Work.Diff.GE.reactionMap (G t) x v a b c d
        ≤ C * Real.sqrt (rmNormSq (G t) x) * Real.sqrt (dRmNormSq (G t) x)
            * (Real.sqrt ((G t).inner x v v) * Real.sqrt ((G t).inner x a a)
              * Real.sqrt ((G t).inner x b b) * Real.sqrt ((G t).inner x c c)
              * Real.sqrt ((G t).inner x d d)) :=
  covReactionFormAt_le_A (I := I) (M := M) hLC
    (Work.Diff.GE.reactionMap : Curv4 (Module.finrank ℝ E) → Curv4 (Module.finrank ℝ E))
    (reactionMap_contDiff (Module.finrank ℝ E))
    (Work.Diff.GE.EvolA.reactionMap_norm_le (Module.finrank ℝ E))
    (reactionMap_fderiv_bound (Module.finrank ℝ E))
    (reactionMap_rot (Module.finrank ℝ E))

/-- The rotation action is compatible with the pointwise negation of a curvature tensor. -/
private theorem rot_neg_aux {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (X : Curv4 n) :
    rot A (-X) = -rot A X := by
  funext i j k l
  simp only [rot, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

/-- The reaction-derivative bound for `F = -reactionMap` (the `hReactB2` hypothesis). -/
theorem covReactionFormAt_le_neg_reactionMap (hLC : LCSmooth I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (G : ℝ → SMet I M) (T : ℝ), IsRicciFlow G T →
      ∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ v a b c d : TangentSpace I x,
      Work.Diff.GE.covReactionFormAt (fun R ↦ -Work.Diff.GE.reactionMap R) (G t) x v a b c d
        ≤ C * Real.sqrt (rmNormSq (G t) x) * Real.sqrt (dRmNormSq (G t) x)
            * (Real.sqrt ((G t).inner x v v) * Real.sqrt ((G t).inner x a a)
              * Real.sqrt ((G t).inner x b b) * Real.sqrt ((G t).inner x c c)
              * Real.sqrt ((G t).inner x d d)) := by
  have hd : ContDiff ℝ (⊤ : ℕ∞)
      (fun R ↦ -(Work.Diff.GE.reactionMap : Curv4 (Module.finrank ℝ E) → Curv4 (Module.finrank ℝ E)) R) :=
    (reactionMap_contDiff (Module.finrank ℝ E)).neg
  have hb : ∃ CF : ℝ, 0 ≤ CF ∧ ∀ R : Curv4 (Module.finrank ℝ E),
      ‖(fun R ↦ -(Work.Diff.GE.reactionMap : Curv4 (Module.finrank ℝ E) → Curv4 (Module.finrank ℝ E)) R) R‖
        ≤ CF * ‖R‖ * ‖R‖ := by
    obtain ⟨C, hC, h⟩ := Work.Diff.GE.EvolA.reactionMap_norm_le (Module.finrank ℝ E)
    exact ⟨C, hC, fun R => by simpa only [Pi.neg_apply, norm_neg] using h R⟩
  have hdv : ∃ CF' : ℝ, 0 ≤ CF' ∧ ∀ R : Curv4 (Module.finrank ℝ E),
      ‖fderiv ℝ (fun R ↦ -(Work.Diff.GE.reactionMap : Curv4 (Module.finrank ℝ E) → Curv4 (Module.finrank ℝ E)) R) R‖
        ≤ CF' * ‖R‖ := by
    obtain ⟨C, hC, h⟩ := reactionMap_fderiv_bound (Module.finrank ℝ E)
    refine ⟨C, hC, fun R => ?_⟩
    rw [show (fun R ↦ -(Work.Diff.GE.reactionMap : Curv4 (Module.finrank ℝ E) → Curv4 (Module.finrank ℝ E)) R)
        = -(Work.Diff.GE.reactionMap : Curv4 (Module.finrank ℝ E) → Curv4 (Module.finrank ℝ E)) from rfl,
      fderiv_neg, norm_neg]
    exact h R
  have he : ∀ A ∈ Matrix.orthogonalGroup (Fin (Module.finrank ℝ E)) ℝ, ∀ R : Curv4 (Module.finrank ℝ E),
      (fun R ↦ -(Work.Diff.GE.reactionMap : Curv4 (Module.finrank ℝ E) → Curv4 (Module.finrank ℝ E)) R)
          (rot A R)
        = rot A ((fun R ↦ -(Work.Diff.GE.reactionMap : Curv4 (Module.finrank ℝ E) → Curv4 (Module.finrank ℝ E)) R) R) := by
    intro A hA R
    simp only [Pi.neg_apply]
    rw [reactionMap_rot (Module.finrank ℝ E) A hA R]
    exact (rot_neg_aux A (Work.Diff.GE.reactionMap R)).symm
  exact covReactionFormAt_le_A (I := I) (M := M) hLC
    (fun R ↦ -(Work.Diff.GE.reactionMap : Curv4 (Module.finrank ℝ E) → Curv4 (Module.finrank ℝ E)) R)
    hd hb hdv he

end Work.Diff.GE
