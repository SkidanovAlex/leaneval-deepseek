import Mathlib
import Submission.Diff.Evol
import Submission.Work.Diff.GE.NablaRm
import Submission.Work.Diff.GE.ReactionDefs
import Submission.Work.Diff.GE.covRmFixedEvolDefs
import Submission.Work.Diff.GE.FixAsm.mvfderiv_rmP_timeDeriv
import Submission.Work.Diff.GE.EvolB.lapRmAt_fields_diff_B
import Submission.Work.Diff.GE.EvolB.reactionFormAt_diff_B
import Submission.Work.Diff.GE.covRmFrameSupplies
import Submission.Work.Diff.GE.WeitzB.covLapRm_le_lapCovRm_metric
import Submission.Work.Diff.GE.connectionVariation_le
import Submission.Work.Diff.EXT.evolK_bridges
import Submission.Work.Diff.EXT.lapCovKRm_one_eq_lapCovRmAt
import Submission.Work.Diff.EXT.evolCompKFix_all
import Submission.Work.Diff.GE.derivWithin_Ico_zero

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The interior evolution estimate for `∇Rm` (absolute-value form), assembled for
`Work.Diff.GE.covRm_frame_evol_abs`

This file supplies the *interior* part of the fixed-vector evolution estimate of `∇Rm` needed by
`Work.Diff.GE.covRm_fixed_evol_abs`, in the two-sided (absolute value) form.

* `Work.Diff.GE.cov3Rm_antisymm_ab` : `∇³Rm` is antisymmetric in the first two curvature slots,
  transported from the EXT tower `Work.Diff.EXT.covKRm_antisymm_pair1` via the bridge
  `Work.Diff.EXT.covKRm_three_eq_cov3Rm`.
* `Work.Diff.GE.covLapRm_le_lapCovRm_abs'` : the two-sided Weitzenböck (Bochner) inequality
  `|∇_v(ΔRm) − Δ∇Rm| ≤ C |Rm| |∇Rm| ‖v‖‖a‖‖b‖‖c‖‖d‖`, obtained from the one-sided
  `Work.Diff.GE.WeitzB.covLapRm_le_lapCovRm_metric` by exchanging the slots `a ↔ b` (which multiplies
  both `covLapRmAt` and `lapCovRmAt` by `−1`, via the Weitzenböck trace identity and the
  antisymmetry of `∇³Rm`).
* `Work.Diff.GE.rmP_moving_deriv` : the product rule for the moving first slot of `rmP` along a
  Ricci flow, phrased with the *model-space* (`E`-valued) derivative of the connection, so that the
  instance mismatch between `TangentSpace I x` and `E` is handled once and for all.
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

/-! ## Antisymmetry of `∇³Rm` in its first two curvature slots -/

/-- `∇³Rm = cov3Rm` is antisymmetric in the two slots that form the first curvature pair. -/
theorem cov3Rm_antisymm_ab (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (w u v a b c d : TangentSpace I x) :
    cov3Rm g x w u v b a c d = - cov3Rm g x w u v a b c d := by
  have h1 := Work.Diff.EXT.covKRm_three_eq_cov3Rm (I := I) (M := M) hLC g x
    (fun i : Fin 3 => ![w, u, v] i) b a c d
  have h2 := Work.Diff.EXT.covKRm_three_eq_cov3Rm (I := I) (M := M) hLC g x
    (fun i : Fin 3 => ![w, u, v] i) a b c d
  have h3 := Work.Diff.EXT.covKRm_antisymm_pair1 (I := I) (M := M) g x 3
    (fun i : Fin 3 => ![w, u, v] i) a b c d
  have e0 : (fun i : Fin 3 => (![w, u, v] : Fin 3 → TangentSpace I x) i) 0 = w := rfl
  have e2 : (fun i : Fin 3 => (![w, u, v] : Fin 3 → TangentSpace I x) i) 2 = v := rfl
  simp only [e0, e2] at h1 h2
  rw [h2] at h3
  exact h1.symm.trans h3

/-! ## The two-sided Weitzenböck inequality -/

/-- **Two-sided Weitzenböck (Bochner) inequality for `∇Rm`.**  From the one-sided
`WeitzB.covLapRm_le_lapCovRm_metric` by exchanging the two slots `a ↔ b`. -/
theorem covLapRm_le_lapCovRm_abs' (hLC : LCSmooth I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : SMet I M) (x : M) (v a b c d : TangentSpace I x),
      |covLapRmAt g x v a b c d - lapCovRmAt g x v a b c d|
        ≤ C * Real.sqrt (rmNormSq g x) * Real.sqrt (dRmNormSq g x)
            * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x a a)
              * Real.sqrt (g.inner x b b) * Real.sqrt (g.inner x c c)
              * Real.sqrt (g.inner x d d)) := by
  obtain ⟨C, hC0, hone⟩ := Work.Diff.GE.WeitzB.covLapRm_le_lapCovRm_metric (I := I) (M := M) hLC
  refine ⟨C, hC0, ?_⟩
  intro g x v a b c d
  obtain ⟨F, hFs, hFON, -⟩ := Work.Diff.GE.onFrameONfield (I := I) (M := M) hLC g x
  have heq := Work.Diff.GE.WeitzB.covLapRm_sub_lapCovRm_eq_sum (I := I) (M := M) hLC g x F hFs hFON
    v a b c d
  have heq' := Work.Diff.GE.WeitzB.covLapRm_sub_lapCovRm_eq_sum (I := I) (M := M) hLC g x F hFs hFON
    v b a c d
  -- the trace flips sign under the exchange `a ↔ b`
  have hflip : covLapRmAt g x v b a c d - lapCovRmAt g x v b a c d
      = - (covLapRmAt g x v a b c d - lapCovRmAt g x v a b c d) := by
    rw [heq', heq, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [cov3Rm_antisymm_ab (I := I) (M := M) hLC g x v (F m x) (F m x) a b c d,
      cov3Rm_antisymm_ab (I := I) (M := M) hLC g x (F m x) (F m x) v a b c d]
    ring
  have hsym : Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x b b) * Real.sqrt (g.inner x a a)
        * Real.sqrt (g.inner x c c) * Real.sqrt (g.inner x d d)
      = Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b)
        * Real.sqrt (g.inner x c c) * Real.sqrt (g.inner x d d) := by ring
  have hlow : - (C * Real.sqrt (rmNormSq g x) * Real.sqrt (dRmNormSq g x)
      * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b)
        * Real.sqrt (g.inner x c c) * Real.sqrt (g.inner x d d)))
      ≤ covLapRmAt g x v a b c d - lapCovRmAt g x v a b c d := by
    have h := hone g x v b a c d
    rw [hsym] at h
    have h2 : covLapRmAt g x v b a c d - lapCovRmAt g x v b a c d
        ≤ C * Real.sqrt (rmNormSq g x) * Real.sqrt (dRmNormSq g x)
            * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b)
              * Real.sqrt (g.inner x c c) * Real.sqrt (g.inner x d d)) := by linarith
    linarith [hflip ▸ h2]
  have hup : covLapRmAt g x v a b c d - lapCovRmAt g x v a b c d
      ≤ C * Real.sqrt (rmNormSq g x) * Real.sqrt (dRmNormSq g x)
          * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b)
            * Real.sqrt (g.inner x c c) * Real.sqrt (g.inner x d d)) := by
    linarith [hone g x v a b c d]
  exact abs_le.mpr ⟨hlow, hup⟩

/-! ## Projections of the `4`-tuple `![a,b,c,d]` -/

section Vec4

variable {x : M}

@[simp] theorem upd4_zero (a b c d : TangentSpace I x) :
    (![a, b, c, d] : Fin 4 → TangentSpace I x) 0 = a := by
  simp [Matrix.cons_val_zero]

@[simp] theorem upd4_one (a b c d : TangentSpace I x) :
    (![a, b, c, d] : Fin 4 → TangentSpace I x) 1 = b := by
  simp [Matrix.cons_val_succ, Matrix.cons_val_zero]

@[simp] theorem upd4_two (a b c d : TangentSpace I x) :
    (![a, b, c, d] : Fin 4 → TangentSpace I x) 2 = c := by
  simp [Matrix.cons_val_succ, Matrix.cons_val_zero]

@[simp] theorem upd4_three (a b c d : TangentSpace I x) :
    (![a, b, c, d] : Fin 4 → TangentSpace I x) 3 = d := by
  simp [Matrix.cons_val_succ, Matrix.cons_val_zero]

end Vec4

/-- **Derivative of `rmP` with a moving slot.**  The moving slot is the `j`-th one; the first
variation of the connection is supplied in the model space `E`, so that the instance mismatch
between `TangentSpace I x` and `E` is confined to this lemma. -/
theorem rmP_update_deriv_E (hLC : LCSmooth I M) (hLV : LCVariation I M)
    (G : ℝ → SMet I M) (T : ℝ) (hflow : IsRicciFlow G T) {t : ℝ} (ht : t ∈ Set.Ioo 0 T)
    (x : M) (p : Fin 4 → TangentSpace I x) (j : Fin 4)
    (X : Π y : M, TangentSpace I y) (hX : SmoothField M X) (u : TangentSpace I x) (w' : E)
    (hw : HasDerivAt (fun s : ℝ ↦ ((lcOf (G s) X x u : TangentSpace I x) : E)) w' t) :
    HasDerivAt
      (fun s ↦ rmP (G s) x ((Function.update p j (lcOf (G s) X x u)) 0)
        ((Function.update p j (lcOf (G s) X x u)) 1) ((Function.update p j (lcOf (G s) X x u)) 2)
        ((Function.update p j (lcOf (G s) X x u)) 3))
      (lapRmAt (G t) x ((Function.update p j (lcOf (G t) X x u)) 0)
          ((Function.update p j (lcOf (G t) X x u)) 1) ((Function.update p j (lcOf (G t) X x u)) 2)
          ((Function.update p j (lcOf (G t) X x u)) 3)
        + reactionFormAt reactionMap (G t) x ((Function.update p j (lcOf (G t) X x u)) 0)
            ((Function.update p j (lcOf (G t) X x u)) 1)
            ((Function.update p j (lcOf (G t) X x u)) 2)
            ((Function.update p j (lcOf (G t) X x u)) 3)
        + rmP (G t) x ((Function.update p j (((w' : E) : TangentSpace I x))) 0)
            ((Function.update p j (((w' : E) : TangentSpace I x))) 1)
            ((Function.update p j (((w' : E) : TangentSpace I x))) 2)
            ((Function.update p j (((w' : E) : TangentSpace I x))) 3)) t := by
  have hw' : HasDerivAt (fun s : ℝ ↦ (lcOf (G s) X x u : TangentSpace I x))
      (((w' : E) : TangentSpace I x)) t := hw
  exact rmP4_update_hasDerivAt_rmP (I := I) (M := M) hLC hLV G T hflow t ht x p j
    (fun s : ℝ ↦ (lcOf (G s) X x u : TangentSpace I x)) (((w' : E) : TangentSpace I x)) hw'

/-! ## The interior evolution identity -/

/-- **The interior fixed-vector evolution identity for `∇Rm`.** -/
theorem covRm_interior_evol (hLC : LCSmooth I M) (hLV : LCVariation I M) :
    ∀ (G : ℝ → SMet I M) (T : ℝ), IsRicciFlow G T →
      ∀ t ∈ Set.Ioo 0 T, ∀ x : M, ∀ v a b c d : TangentSpace I x,
        HasDerivWithinAt (fun s ↦ covRm (G s) x v a b c d)
          (covRmTimeDeriv reactionMap G t x v a b c d) (Set.Ico 0 T) t := by
  intro G T hflow t ht x v a b c d
  letI hNAG : NormedAddCommGroup (TangentSpace I x) := inferInstanceAs (NormedAddCommGroup E)
  letI hNS : NormedSpace ℝ (TangentSpace I x) := inferInstanceAs (NormedSpace ℝ E)
  letI hFD : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  have hA : SmoothField M (smoothExt x a) := smoothExt_cmdiff x a
  have hB : SmoothField M (smoothExt x b) := smoothExt_cmdiff x b
  have hC : SmoothField M (smoothExt x c) := smoothExt_cmdiff x c
  have hD : SmoothField M (smoothExt x d) := smoothExt_cmdiff x d
  have hJs : JointSmooth G (Set.Ioo 0 T) :=
    hflow.1.mono (Set.prod_mono Set.Ioo_subset_Ico_self (Set.subset_univ _))
  -- the Clairaut step
  have hM := Work.Diff.GE.FixAsm.mvfderiv_rmP_timeDeriv (I := I) (M := M) hLC hLV G T hflow ht x v
    (smoothExt x a) (smoothExt x b) (smoothExt x c) (smoothExt x d) hA hB hC hD
  -- split the `mvfderiv` of the sum
  have hFcont : ContDiff ℝ ((⊤ : ENat) : WithTop ENat)
      (reactionMap : Curv4 (Module.finrank ℝ E) → Curv4 (Module.finrank ℝ E)) :=
    reactionMap_contDiff (Module.finrank ℝ E)
  have hFrot : ∀ A ∈ Matrix.orthogonalGroup (Fin (Module.finrank ℝ E)) ℝ,
      ∀ R : Curv4 (Module.finrank ℝ E),
        (reactionMap : Curv4 (Module.finrank ℝ E) → Curv4 (Module.finrank ℝ E))
            (rot A R) = rot A (reactionMap R) :=
    reactionMap_rot (Module.finrank ℝ E)
  have hsplit : mvfderiv I
        (fun y : M ↦ lapRmAt (G t) y ((smoothExt x a) y) ((smoothExt x b) y)
            ((smoothExt x c) y) ((smoothExt x d) y)
          + reactionFormAt reactionMap (G t) y ((smoothExt x a) y) ((smoothExt x b) y)
            ((smoothExt x c) y) ((smoothExt x d) y)) x v
      = mvfderiv I (fun y : M ↦ lapRmAt (G t) y ((smoothExt x a) y) ((smoothExt x b) y)
            ((smoothExt x c) y) ((smoothExt x d) y)) x v
        + mvfderiv I (fun y : M ↦ reactionFormAt reactionMap (G t) y ((smoothExt x a) y)
            ((smoothExt x b) y) ((smoothExt x c) y) ((smoothExt x d) y)) x v := by
    have h := congrArg (fun (L : TangentSpace I x →L[ℝ] ℝ) => L v)
      (mvfderiv_add
        (Work.Diff.GE.EvolB.lapRmAt_fields_diff_B (I := I) (M := M) hLC (G t) x _ _ _ _
          hA hB hC hD)
        (Work.Diff.GE.EvolB.reactionFormAt_diff_B (I := I) (M := M) hLC reactionMap hFcont hFrot
          (G t) x _ _ _ _ hA hB hC hD))
    have hsum_eq : (fun y : M ↦ lapRmAt (G t) y ((smoothExt x a) y) ((smoothExt x b) y)
          ((smoothExt x c) y) ((smoothExt x d) y))
        + (fun y : M ↦ reactionFormAt reactionMap (G t) y ((smoothExt x a) y) ((smoothExt x b) y)
          ((smoothExt x c) y) ((smoothExt x d) y))
        = (fun y : M ↦ lapRmAt (G t) y ((smoothExt x a) y) ((smoothExt x b) y)
          ((smoothExt x c) y) ((smoothExt x d) y)
          + reactionFormAt reactionMap (G t) y ((smoothExt x a) y) ((smoothExt x b) y)
          ((smoothExt x c) y) ((smoothExt x d) y)) := rfl
    rw [hsum_eq] at h
    simpa only [ContinuousLinearMap.add_apply] using h
  rw [hsplit] at hM
  -- the four connection-variation curves
  obtain ⟨wa, hwa, -⟩ := hLV G (Set.Ioo 0 T) isOpen_Ioo hJs t ht (smoothExt x v) (smoothExt x a)
    (smoothExt_cmdiff x v) hA x
  obtain ⟨wb, hwb, -⟩ := hLV G (Set.Ioo 0 T) isOpen_Ioo hJs t ht (smoothExt x v) (smoothExt x b)
    (smoothExt_cmdiff x v) hB x
  obtain ⟨wc, hwc, -⟩ := hLV G (Set.Ioo 0 T) isOpen_Ioo hJs t ht (smoothExt x v) (smoothExt x c)
    (smoothExt_cmdiff x v) hC x
  obtain ⟨wd, hwd, -⟩ := hLV G (Set.Ioo 0 T) isOpen_Ioo hJs t ht (smoothExt x v) (smoothExt x d)
    (smoothExt_cmdiff x v) hD x
  have hcva : HasDerivAt (fun s : ℝ ↦ ((lcOf (G s) (smoothExt x a) x v : TangentSpace I x) : E))
      wa t := by
    have h := hwa
    rw [smoothExt_apply x v] at h
    exact h
  have hcvb : HasDerivAt (fun s : ℝ ↦ ((lcOf (G s) (smoothExt x b) x v : TangentSpace I x) : E))
      wb t := by
    have h := hwb
    rw [smoothExt_apply x v] at h
    exact h
  have hcvc : HasDerivAt (fun s : ℝ ↦ ((lcOf (G s) (smoothExt x c) x v : TangentSpace I x) : E))
      wc t := by
    have h := hwc
    rw [smoothExt_apply x v] at h
    exact h
  have hcvd : HasDerivAt (fun s : ℝ ↦ ((lcOf (G s) (smoothExt x d) x v : TangentSpace I x) : E))
      wd t := by
    have h := hwd
    rw [smoothExt_apply x v] at h
    exact h
  -- the four correction terms
  have hP0 : HasDerivAt
      (fun s ↦ rmP (G s) x (lcOf (G s) (smoothExt x a) x v) b c d)
      (lapRmAt (G t) x (lcOf (G t) (smoothExt x a) x v) b c d
        + reactionFormAt reactionMap (G t) x (lcOf (G t) (smoothExt x a) x v) b c d
        + rmP (G t) x (wa : TangentSpace I x) b c d) t := by
    have h := rmP_update_deriv_E (I := I) (M := M) hLC hLV G T hflow ht x ![a, b, c, d] 0
      (smoothExt x a) hA v wa hcva
    simpa only [upd4_zero, upd4_one, upd4_two, upd4_three, Function.update_apply, Fin.isValue,
      Fin.reduceEq, ↓reduceIte, Fin.mk_one, Fin.reduceFinMk] using h
  have hP1 : HasDerivAt
      (fun s ↦ rmP (G s) x a (lcOf (G s) (smoothExt x b) x v) c d)
      (lapRmAt (G t) x a (lcOf (G t) (smoothExt x b) x v) c d
        + reactionFormAt reactionMap (G t) x a (lcOf (G t) (smoothExt x b) x v) c d
        + rmP (G t) x a (wb : TangentSpace I x) c d) t := by
    have h := rmP_update_deriv_E (I := I) (M := M) hLC hLV G T hflow ht x ![a, b, c, d] 1
      (smoothExt x b) hB v wb hcvb
    simpa only [upd4_zero, upd4_one, upd4_two, upd4_three, Function.update_apply, Fin.isValue,
      Fin.reduceEq, ↓reduceIte, Fin.mk_one, Fin.reduceFinMk] using h
  have hP2 : HasDerivAt
      (fun s ↦ rmP (G s) x a b (lcOf (G s) (smoothExt x c) x v) d)
      (lapRmAt (G t) x a b (lcOf (G t) (smoothExt x c) x v) d
        + reactionFormAt reactionMap (G t) x a b (lcOf (G t) (smoothExt x c) x v) d
        + rmP (G t) x a b (wc : TangentSpace I x) d) t := by
    have h := rmP_update_deriv_E (I := I) (M := M) hLC hLV G T hflow ht x ![a, b, c, d] 2
      (smoothExt x c) hC v wc hcvc
    simpa only [upd4_zero, upd4_one, upd4_two, upd4_three, Function.update_apply, Fin.isValue,
      Fin.reduceEq, ↓reduceIte, Fin.mk_one, Fin.reduceFinMk] using h
  have hP3 : HasDerivAt
      (fun s ↦ rmP (G s) x a b c (lcOf (G s) (smoothExt x d) x v))
      (lapRmAt (G t) x a b c (lcOf (G t) (smoothExt x d) x v)
        + reactionFormAt reactionMap (G t) x a b c (lcOf (G t) (smoothExt x d) x v)
        + rmP (G t) x a b c (wd : TangentSpace I x)) t := by
    have h := rmP_update_deriv_E (I := I) (M := M) hLC hLV G T hflow ht x ![a, b, c, d] 3
      (smoothExt x d) hD v wd hcvd
    simpa only [upd4_zero, upd4_one, upd4_two, upd4_three, Function.update_apply, Fin.isValue,
      Fin.reduceEq, ↓reduceIte, Fin.mk_one, Fin.reduceFinMk] using h
  -- the derivative of the connection curves is the model-space derivative
  have hdv : deriv (connVar G x a v) t = wa := hcva.deriv
  have hdw : deriv (connVar G x b v) t = wb := hcvb.deriv
  have hdx : deriv (connVar G x c v) t = wc := hcvc.deriv
  have hdy : deriv (connVar G x d v) t = wd := hcvd.deriv
  -- assemble
  have hmain : HasDerivWithinAt
      (fun s ↦ mvfderiv I (fun y : M ↦ rmP (G s) y ((smoothExt x a) y) ((smoothExt x b) y)
            ((smoothExt x c) y) ((smoothExt x d) y)) x v
          - rmP (G s) x (lcOf (G s) (smoothExt x a) x v) b c d
          - rmP (G s) x a (lcOf (G s) (smoothExt x b) x v) c d
          - rmP (G s) x a b (lcOf (G s) (smoothExt x c) x v) d
          - rmP (G s) x a b c (lcOf (G s) (smoothExt x d) x v))
      (mvfderiv I (fun y : M ↦ lapRmAt (G t) y ((smoothExt x a) y) ((smoothExt x b) y)
            ((smoothExt x c) y) ((smoothExt x d) y)) x v
        + mvfderiv I (fun y : M ↦ reactionFormAt reactionMap (G t) y ((smoothExt x a) y)
            ((smoothExt x b) y) ((smoothExt x c) y) ((smoothExt x d) y)) x v
        - (lapRmAt (G t) x (lcOf (G t) (smoothExt x a) x v) b c d
          + reactionFormAt reactionMap (G t) x (lcOf (G t) (smoothExt x a) x v) b c d
          + rmP (G t) x wa b c d)
        - (lapRmAt (G t) x a (lcOf (G t) (smoothExt x b) x v) c d
          + reactionFormAt reactionMap (G t) x a (lcOf (G t) (smoothExt x b) x v) c d
          + rmP (G t) x a wb c d)
        - (lapRmAt (G t) x a b (lcOf (G t) (smoothExt x c) x v) d
          + reactionFormAt reactionMap (G t) x a b (lcOf (G t) (smoothExt x c) x v) d
          + rmP (G t) x a b wc d)
        - (lapRmAt (G t) x a b c (lcOf (G t) (smoothExt x d) x v)
          + reactionFormAt reactionMap (G t) x a b c (lcOf (G t) (smoothExt x d) x v)
          + rmP (G t) x a b c wd)) (Set.Ico 0 T) t :=
    ((((hM.sub hP0.hasDerivWithinAt).sub hP1.hasDerivWithinAt).sub hP2.hasDerivWithinAt).sub
      hP3.hasDerivWithinAt)
  -- rewrite the function and the value
  have hfun : (fun s ↦ covRm (G s) x v a b c d)
      = (fun s ↦ mvfderiv I (fun y : M ↦ rmP (G s) y ((smoothExt x a) y) ((smoothExt x b) y)
            ((smoothExt x c) y) ((smoothExt x d) y)) x v
          - rmP (G s) x (lcOf (G s) (smoothExt x a) x v) b c d
          - rmP (G s) x a (lcOf (G s) (smoothExt x b) x v) c d
          - rmP (G s) x a b (lcOf (G s) (smoothExt x c) x v) d
          - rmP (G s) x a b c (lcOf (G s) (smoothExt x d) x v)) := by
    funext s
    simp only [covRm]
  have hval : covRmTimeDeriv reactionMap G t x v a b c d
      = (mvfderiv I (fun y : M ↦ lapRmAt (G t) y ((smoothExt x a) y) ((smoothExt x b) y)
            ((smoothExt x c) y) ((smoothExt x d) y)) x v
        + mvfderiv I (fun y : M ↦ reactionFormAt reactionMap (G t) y ((smoothExt x a) y)
            ((smoothExt x b) y) ((smoothExt x c) y) ((smoothExt x d) y)) x v
        - (lapRmAt (G t) x (lcOf (G t) (smoothExt x a) x v) b c d
          + reactionFormAt reactionMap (G t) x (lcOf (G t) (smoothExt x a) x v) b c d
          + rmP (G t) x wa b c d)
        - (lapRmAt (G t) x a (lcOf (G t) (smoothExt x b) x v) c d
          + reactionFormAt reactionMap (G t) x a (lcOf (G t) (smoothExt x b) x v) c d
          + rmP (G t) x a wb c d)
        - (lapRmAt (G t) x a b (lcOf (G t) (smoothExt x c) x v) d
          + reactionFormAt reactionMap (G t) x a b (lcOf (G t) (smoothExt x c) x v) d
          + rmP (G t) x a b wc d)
        - (lapRmAt (G t) x a b c (lcOf (G t) (smoothExt x d) x v)
          + reactionFormAt reactionMap (G t) x a b c (lcOf (G t) (smoothExt x d) x v)
          + rmP (G t) x a b c wd)) := by
    simp only [covRmTimeDeriv, covLapRmAt, covReactionFormAt, hdv, hdw, hdx, hdy]
    ring
  rw [hfun, hval]
  exact hmain




/-! ## The boundary (initial-time) estimate from the interior estimate -/

/-- **The `t = 0` case of the fixed-vector evolution estimate**, from the interior estimate and the
continuity at `0` of the initial data.  All three continuity inputs are hypotheses here; they are
supplied by `Work.Diff.GE.covRm_zero_c1` (`Q` and its within-derivative),
`Work.Diff.GE.lapCovRmAt_zero_continuous` and the continuity of the norms. -/
theorem covRm_zero_boundary (hLC : LCSmooth I M)
    (hQ : ∀ (G : ℝ → SMet I M) (T : ℝ), IsRicciFlow G T →
      ∀ x : M, ∀ v a b c d : TangentSpace I x,
        ContinuousWithinAt (fun s : ℝ ↦ covRm (G s) x v a b c d) (Set.Ico 0 T) 0 ∧
        ContinuousWithinAt
          (fun s : ℝ ↦ derivWithin (fun σ : ℝ ↦ covRm (G σ) x v a b c d) (Set.Ico 0 T) s)
          (Set.Ico 0 T) 0)
    (hB : ∀ (G : ℝ → SMet I M) (T : ℝ), IsRicciFlow G T →
      ∀ x : M, ∀ v a b c d : TangentSpace I x,
        ContinuousWithinAt (fun s : ℝ ↦ lapCovRmAt (G s) x v a b c d) (Set.Ico 0 T) 0)
    (hN : ∀ (G : ℝ → SMet I M) (T : ℝ), IsRicciFlow G T →
      ∀ x : M, ∀ v a b c d : TangentSpace I x,
        ContinuousWithinAt
          (fun s : ℝ ↦ Real.sqrt (rmNormSq (G s) x) * Real.sqrt (dRmNormSq (G s) x)
            * (Real.sqrt ((G s).inner x v v) * Real.sqrt ((G s).inner x a a)
              * Real.sqrt ((G s).inner x b b) * Real.sqrt ((G s).inner x c c)
              * Real.sqrt ((G s).inner x d d))) (Set.Ico 0 T) 0)
    (C₁ : ℝ) (hC₁ : 0 ≤ C₁)
    (hInt : ∀ (G : ℝ → SMet I M) (T : ℝ), IsRicciFlow G T →
      ∀ t ∈ Set.Ioo 0 T, ∀ x : M, ∀ v a b c d : TangentSpace I x,
        HasDerivWithinAt (fun s ↦ covRm (G s) x v a b c d)
          (covRmTimeDeriv reactionMap G t x v a b c d) (Set.Ico 0 T) t ∧
        |covRmTimeDeriv reactionMap G t x v a b c d - lapCovRmAt (G t) x v a b c d|
          ≤ C₁ * Real.sqrt (rmNormSq (G t) x) * Real.sqrt (dRmNormSq (G t) x)
              * (Real.sqrt ((G t).inner x v v) * Real.sqrt ((G t).inner x a a)
                * Real.sqrt ((G t).inner x b b) * Real.sqrt ((G t).inner x c c)
                * Real.sqrt ((G t).inner x d d))) :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ (G : ℝ → SMet I M) (T : ℝ), IsRicciFlow G T →
      ∀ x : M, ∀ v a b c d : TangentSpace I x, ∃ D : ℝ,
        HasDerivWithinAt (fun s ↦ covRm (G s) x v a b c d) D (Set.Ico 0 T) 0 ∧
        |D - lapCovRmAt (G 0) x v a b c d|
          ≤ C₂ * Real.sqrt (rmNormSq (G 0) x) * Real.sqrt (dRmNormSq (G 0) x)
              * (Real.sqrt ((G 0).inner x v v) * Real.sqrt ((G 0).inner x a a)
                * Real.sqrt ((G 0).inner x b b) * Real.sqrt ((G 0).inner x c c)
                * Real.sqrt ((G 0).inner x d d)) := by
  refine ⟨C₁, hC₁, ?_⟩
  intro G T hflow x v a b c d
  by_cases hT : 0 < T
  · have hTpos : 0 < T := hT
    have hmem_iff : ∀ t ∈ Set.Ioo (0 : ℝ) T,
        Set.Ico (0 : ℝ) T ∈ 𝓝 t := fun t ht =>
      Filter.mem_of_superset (IsOpen.mem_nhds isOpen_Ioo ht) Set.Ioo_subset_Ico_self
    have hL : ∀ t ∈ Set.Ioo (0 : ℝ) T,
        HasDerivAt (fun s ↦ covRm (G s) x v a b c d)
          (covRmTimeDeriv reactionMap G t x v a b c d) t := fun t ht =>
      (hInt G T hflow t ht x v a b c d).1.hasDerivAt (hmem_iff t ht)
    have hderivF : ∀ t ∈ Set.Ioo (0 : ℝ) T,
        HasDerivAt (fun s ↦ covRm (G s) x v a b c d)
          (derivWithin (fun σ : ℝ ↦ covRm (G σ) x v a b c d) (Set.Ico 0 T) t) t := by
      intro t ht
      have hd : derivWithin (fun σ : ℝ ↦ covRm (G σ) x v a b c d) (Set.Ico 0 T) t
          = covRmTimeDeriv reactionMap G t x v a b c d := by
        rw [derivWithin_of_mem_nhds (hmem_iff t ht)]
        exact (hL t ht).deriv
      rw [hd]
      exact hL t ht
    have hmain := derivWithin_Ico_zero (fun s ↦ covRm (G s) x v a b c d)
      (fun s ↦ derivWithin (fun σ : ℝ ↦ covRm (G σ) x v a b c d) (Set.Ico 0 T) s) T hTpos
      hderivF (hQ G T hflow x v a b c d).1 (hQ G T hflow x v a b c d).2
    refine ⟨derivWithin (fun σ : ℝ ↦ covRm (G σ) x v a b c d) (Set.Ico 0 T) 0, hmain, ?_⟩
    -- the bound, by passing to the limit `t → 0⁺`
    have hsub : 𝓝[Set.Ioo (0 : ℝ) T] 0 ≤ 𝓝[Set.Ico (0 : ℝ) T] 0 :=
      nhdsWithin_mono 0 Set.Ioo_subset_Ico_self
    have hFt : ∀ t ∈ Set.Ioo (0 : ℝ) T,
        derivWithin (fun σ : ℝ ↦ covRm (G σ) x v a b c d) (Set.Ico 0 T) t
          = covRmTimeDeriv reactionMap G t x v a b c d := by
      intro t ht
      rw [derivWithin_of_mem_nhds (hmem_iff t ht)]
      exact (hL t ht).deriv
    have hlim1 : Filter.Tendsto
        (fun t : ℝ ↦ |derivWithin (fun σ : ℝ ↦ covRm (G σ) x v a b c d) (Set.Ico 0 T) t
          - lapCovRmAt (G t) x v a b c d|) (𝓝[Set.Ioo (0 : ℝ) T] 0)
        (𝓝 |derivWithin (fun σ : ℝ ↦ covRm (G σ) x v a b c d) (Set.Ico 0 T) 0
          - lapCovRmAt (G 0) x v a b c d|) :=
      ((((hQ G T hflow x v a b c d).2.tendsto.mono_left hsub).sub
        ((hB G T hflow x v a b c d).tendsto.mono_left hsub)).abs)
    have hlim2 : Filter.Tendsto
        (fun t : ℝ ↦ C₁ * (Real.sqrt (rmNormSq (G t) x) * Real.sqrt (dRmNormSq (G t) x)
            * (Real.sqrt ((G t).inner x v v) * Real.sqrt ((G t).inner x a a)
              * Real.sqrt ((G t).inner x b b) * Real.sqrt ((G t).inner x c c)
              * Real.sqrt ((G t).inner x d d)))) (𝓝[Set.Ioo (0 : ℝ) T] 0)
        (𝓝 (C₁ * (Real.sqrt (rmNormSq (G 0) x) * Real.sqrt (dRmNormSq (G 0) x)
            * (Real.sqrt ((G 0).inner x v v) * Real.sqrt ((G 0).inner x a a)
              * Real.sqrt ((G 0).inner x b b) * Real.sqrt ((G 0).inner x c c)
              * Real.sqrt ((G 0).inner x d d))))) :=
      ((hN G T hflow x v a b c d).tendsto.mono_left hsub).const_mul C₁
    have hev : ∀ᶠ t in 𝓝[Set.Ioo (0 : ℝ) T] 0,
        |derivWithin (fun σ : ℝ ↦ covRm (G σ) x v a b c d) (Set.Ico 0 T) t
          - lapCovRmAt (G t) x v a b c d|
          ≤ C₁ * (Real.sqrt (rmNormSq (G t) x) * Real.sqrt (dRmNormSq (G t) x)
              * (Real.sqrt ((G t).inner x v v) * Real.sqrt ((G t).inner x a a)
                * Real.sqrt ((G t).inner x b b) * Real.sqrt ((G t).inner x c c)
                * Real.sqrt ((G t).inner x d d))) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [hFt t ht]
      have h := (hInt G T hflow t ht x v a b c d).2
      have he : C₁ * (Real.sqrt (rmNormSq (G t) x) * Real.sqrt (dRmNormSq (G t) x)
            * (Real.sqrt ((G t).inner x v v) * Real.sqrt ((G t).inner x a a)
              * Real.sqrt ((G t).inner x b b) * Real.sqrt ((G t).inner x c c)
              * Real.sqrt ((G t).inner x d d)))
          = C₁ * Real.sqrt (rmNormSq (G t) x) * Real.sqrt (dRmNormSq (G t) x)
              * (Real.sqrt ((G t).inner x v v) * Real.sqrt ((G t).inner x a a)
                * Real.sqrt ((G t).inner x b b) * Real.sqrt ((G t).inner x c c)
                * Real.sqrt ((G t).inner x d d)) := by ring
      rw [he]
      exact h
    have hfin := le_of_tendsto_of_tendsto (hb := left_nhdsWithin_Ioo_neBot hTpos) hlim1 hlim2 hev
    exact hfin.trans_eq (by
      show C₁ * (Real.sqrt (rmNormSq (G 0) x) * Real.sqrt (dRmNormSq (G 0) x)
            * (Real.sqrt ((G 0).inner x v v) * Real.sqrt ((G 0).inner x a a)
              * Real.sqrt ((G 0).inner x b b) * Real.sqrt ((G 0).inner x c c)
              * Real.sqrt ((G 0).inner x d d)))
        = C₁ * Real.sqrt (rmNormSq (G 0) x) * Real.sqrt (dRmNormSq (G 0) x)
            * (Real.sqrt ((G 0).inner x v v) * Real.sqrt ((G 0).inner x a a)
              * Real.sqrt ((G 0).inner x b b) * Real.sqrt ((G 0).inner x c c)
              * Real.sqrt ((G 0).inner x d d))
      ring)
  · have hset : Set.Ico (0 : ℝ) T = ∅ := Set.Ico_eq_empty hT
    refine ⟨lapCovRmAt (G 0) x v a b c d, ?_, ?_⟩
    · rw [hset, hasDerivWithinAt_iff_tendsto_slope, Set.empty_sdiff, nhdsWithin_empty]
      exact Filter.tendsto_bot
    · rw [sub_self, abs_zero]
      positivity

end Work.Diff.GE
