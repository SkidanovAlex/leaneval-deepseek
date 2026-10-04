import Mathlib
import Submission.Work.Diff.GE.EvolB.Defs
import Submission.Work.Diff.GE.EvolB.lapRmAt_fields_diff_B
import Submission.Work.Diff.GE.EvolB.reactionFormAt_diff_B
import Submission.Work.Diff.GE.EvolB.rmP4_update_hasDerivAt_B
import Submission.Work.Diff.GE.FixAsm.mvfderiv_rmP_timeDeriv
import Submission.Work.Diff.GE.react.rmReact_contDiff
import Submission.Work.Diff.GE.EvolB.ReactionRot
import Submission.Work.Diff.GE.reaction_map_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The assembly of the fixed-vector `∇Rm` evolution (`EvolB`)

`Work.Diff.GE.EvolB.covRm_fixed_evol_interior_B` is the (interior-time) identity

`∂ₜ (covRm (G ·) x v a b c d) = covRmTimeDerivB reactionMap G t x v a b c d`

for a Ricci flow `G`, `t ∈ (0,T)`:

* the derivative of the main term `s ↦ mvfderiv I (fun y ↦ rmP (G s) y (A y) … ) x v` is the
  Clairaut step `Work.Diff.GE.FixAsm.mvfderiv_rmP_timeDeriv`, which produces
  `mvfderiv I (fun y ↦ lapRmAt (G t) y (A y) … + reactionFormAt reactionMap (G t) y (A y) …) x v`;
  this splits over the sum because both summands are differentiable
  (`EvolB.lapRmAt_fields_diff_B`, `EvolB.reactionFormAt_diff_B`);
* the derivative of each of the four correction terms `s ↦ rmP (G s) x (∇_v A_slot) b c d` is the
  moving-slot product rule `EvolB.rmP4_update_hasDerivAt_B`;
* unfolding the definitions of `covLapRmAt`, `covReactionFormAt` and `covRmTimeDerivB` on both sides
  gives the stated value.
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
  {x : M}

/-- `Function.update` on the `4`-tuple `![a,b,c,d]` in slot `0`. -/
theorem update_four_zero (a b c d z : TangentSpace I x) :
    Function.update ![a, b, c, d] 0 z = ![z, b, c, d] := by
  funext j
  fin_cases j <;> simp

/-- `Function.update` on the `4`-tuple `![a,b,c,d]` in slot `1`. -/
theorem update_four_one (a b c d z : TangentSpace I x) :
    Function.update ![a, b, c, d] 1 z = ![a, z, c, d] := by
  funext j
  fin_cases j <;> simp

/-- `Function.update` on the `4`-tuple `![a,b,c,d]` in slot `2`. -/
theorem update_four_two (a b c d z : TangentSpace I x) :
    Function.update ![a, b, c, d] 2 z = ![a, b, z, d] := by
  funext j
  fin_cases j <;> simp

/-- `Function.update` on the `4`-tuple `![a,b,c,d]` in slot `3`. -/
theorem update_four_three (a b c d z : TangentSpace I x) :
    Function.update ![a, b, c, d] 3 z = ![a, b, c, z] := by
  funext j
  fin_cases j <;> simp


/-- Projection of the vector `![a,b,c,d]` at `0`. -/
@[simp] theorem vec4_zero (a b c d : TangentSpace I x) :
    (![a, b, c, d] : Fin 4 → TangentSpace I x) 0 = a := by
  simp [Matrix.cons_val_zero]

/-- Projection of the vector `![a,b,c,d]` at `1`. -/
@[simp] theorem vec4_one (a b c d : TangentSpace I x) :
    (![a, b, c, d] : Fin 4 → TangentSpace I x) 1 = b := by
  simp [Matrix.cons_val_succ, Matrix.cons_val_zero]

/-- Projection of the vector `![a,b,c,d]` at `2`. -/
@[simp] theorem vec4_two (a b c d : TangentSpace I x) :
    (![a, b, c, d] : Fin 4 → TangentSpace I x) 2 = c := by
  simp [Matrix.cons_val_succ, Matrix.cons_val_zero]

/-- Projection of the vector `![a,b,c,d]` at `3`. -/
@[simp] theorem vec4_three (a b c d : TangentSpace I x) :
    (![a, b, c, d] : Fin 4 → TangentSpace I x) 3 = d := by
  simp [Matrix.cons_val_succ, Matrix.cons_val_zero]

/-- **The interior fixed-vector evolution identity for `∇Rm`.** -/
theorem covRm_fixed_evol_interior_B
    (hLC : LCSmooth I M) (hLV : LCVariation I M)
    {G : ℝ → SMet I M} {T : ℝ} (hflow : IsRicciFlow G T)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T) (x : M) (v a b c d : TangentSpace I x) :
    HasDerivWithinAt (fun s ↦ covRm (G s) x v a b c d)
      (covRmTimeDerivB reactionMap G t x v a b c d) (Set.Ico 0 T) t := by
  have hA : SmoothField M (smoothExt x a) := smoothExt_cmdiff x a
  have hB : SmoothField M (smoothExt x b) := smoothExt_cmdiff x b
  have hC : SmoothField M (smoothExt x c) := smoothExt_cmdiff x c
  have hD : SmoothField M (smoothExt x d) := smoothExt_cmdiff x d
  -- ### the Clairaut step, and the split of the `mvfderiv` of the sum
  have hM := Work.Diff.GE.FixAsm.mvfderiv_rmP_timeDeriv (I := I) (M := M) hLC hLV G T hflow ht x v
    (smoothExt x a) (smoothExt x b) (smoothExt x c) (smoothExt x d) hA hB hC hD
  have hFcont : ContDiff ℝ ((⊤ : ENat) : WithTop ENat)
      (Work.Diff.GE.reactionMap : Curv4 (Module.finrank ℝ E) → Curv4 (Module.finrank ℝ E)) := by
    rw [show (Work.Diff.GE.reactionMap : Curv4 (Module.finrank ℝ E) →
          Curv4 (Module.finrank ℝ E))
        = Work.Diff.GE.rmReact (Module.finrank ℝ E) from
      funext fun R => Work.Diff.GE.EvolA.reactionMap_eq_rmReact R]
    exact Work.Diff.GE.react.rmReact_contDiff _
  have hFrot : ∀ A ∈ Matrix.orthogonalGroup (Fin (Module.finrank ℝ E)) ℝ,
      ∀ R : Curv4 (Module.finrank ℝ E),
        (Work.Diff.GE.reactionMap : Curv4 (Module.finrank ℝ E) → Curv4 (Module.finrank ℝ E))
            (Submission.Diff.Alg.rot A R)
          = Submission.Diff.Alg.rot A (Work.Diff.GE.reactionMap R) := by
    intro A hA R
    show Work.Diff.GE.reactionMap (Submission.Diff.Alg.rot A R)
      = Submission.Diff.Alg.rot A (Work.Diff.GE.reactionMap R)
    rw [Work.Diff.GE.EvolA.reactionMap_eq_rmReact, Work.Diff.GE.EvolA.reactionMap_eq_rmReact]
    exact Work.Diff.GE.EvolB.rmReact_rot_C _ A hA R
  have hsplit : mvfderiv I
        (fun y : M ↦ Work.Diff.GE.lapRmAt (G t) y ((smoothExt x a) y) ((smoothExt x b) y)
            ((smoothExt x c) y) ((smoothExt x d) y)
          + Work.Diff.GE.reactionFormAt reactionMap (G t) y ((smoothExt x a) y)
            ((smoothExt x b) y) ((smoothExt x c) y) ((smoothExt x d) y)) x v
      = mvfderiv I (fun y : M ↦ Work.Diff.GE.lapRmAt (G t) y ((smoothExt x a) y)
            ((smoothExt x b) y) ((smoothExt x c) y) ((smoothExt x d) y)) x v
        + mvfderiv I (fun y : M ↦ Work.Diff.GE.reactionFormAt reactionMap (G t) y
            ((smoothExt x a) y) ((smoothExt x b) y) ((smoothExt x c) y)
            ((smoothExt x d) y)) x v := by
    change mvfderiv I
        ((fun y : M ↦ Work.Diff.GE.lapRmAt (G t) y ((smoothExt x a) y) ((smoothExt x b) y)
            ((smoothExt x c) y) ((smoothExt x d) y))
          + (fun y : M ↦ Work.Diff.GE.reactionFormAt reactionMap (G t) y ((smoothExt x a) y)
            ((smoothExt x b) y) ((smoothExt x c) y) ((smoothExt x d) y))) x v
      = mvfderiv I (fun y : M ↦ Work.Diff.GE.lapRmAt (G t) y ((smoothExt x a) y)
            ((smoothExt x b) y) ((smoothExt x c) y) ((smoothExt x d) y)) x v
        + mvfderiv I (fun y : M ↦ Work.Diff.GE.reactionFormAt reactionMap (G t) y
            ((smoothExt x a) y) ((smoothExt x b) y) ((smoothExt x c) y)
            ((smoothExt x d) y)) x v
    have h := congrArg (fun (L : TangentSpace I x →L[ℝ] ℝ) => L v)
      (mvfderiv_add
        (lapRmAt_fields_diff_B (I := I) (M := M) hLC (G t) x _ _ _ _ hA hB hC hD)
        (reactionFormAt_diff_B (I := I) (M := M) hLC reactionMap hFcont hFrot
          (G t) x _ _ _ _ hA hB hC hD))
    simpa only [ContinuousLinearMap.add_apply] using h
  rw [hsplit] at hM
  -- ### the four connection-variation curves
  have hJs : JointSmooth G (Set.Ioo 0 T) :=
    hflow.1.mono (Set.prod_mono Set.Ioo_subset_Ico_self (Set.subset_univ _))
  obtain ⟨wa, hwa, -⟩ := hLV G (Set.Ioo 0 T) isOpen_Ioo hJs t ht (smoothExt x v) (smoothExt x a)
    (smoothExt_cmdiff x v) (smoothExt_cmdiff x a) x
  obtain ⟨wb, hwb, -⟩ := hLV G (Set.Ioo 0 T) isOpen_Ioo hJs t ht (smoothExt x v) (smoothExt x b)
    (smoothExt_cmdiff x v) (smoothExt_cmdiff x b) x
  obtain ⟨wc, hwc, -⟩ := hLV G (Set.Ioo 0 T) isOpen_Ioo hJs t ht (smoothExt x v) (smoothExt x c)
    (smoothExt_cmdiff x v) (smoothExt_cmdiff x c) x
  obtain ⟨wd, hwd, -⟩ := hLV G (Set.Ioo 0 T) isOpen_Ioo hJs t ht (smoothExt x v) (smoothExt x d)
    (smoothExt_cmdiff x v) (smoothExt_cmdiff x d) x
  have hcva : HasDerivAt (connVarB G x a v) (wa : TangentSpace I x) t := by
    have h := hwa
    rw [smoothExt_apply x v] at h
    exact h
  have hcvb : HasDerivAt (connVarB G x b v) (wb : TangentSpace I x) t := by
    have h := hwb
    rw [smoothExt_apply x v] at h
    exact h
  have hcvc : HasDerivAt (connVarB G x c v) (wc : TangentSpace I x) t := by
    have h := hwc
    rw [smoothExt_apply x v] at h
    exact h
  have hcvd : HasDerivAt (connVarB G x d v) (wd : TangentSpace I x) t := by
    have h := hwd
    rw [smoothExt_apply x v] at h
    exact h
  -- ### the four correction terms
  have hP0 : HasDerivAt (fun s ↦ rmP (G s) x (connVarB G x a v s) b c d)
      (Work.Diff.GE.lapRmAt (G t) x (connVarB G x a v t) b c d
        + Work.Diff.GE.reactionFormAt reactionMap (G t) x (connVarB G x a v t) b c d
        + rmP (G t) x wa b c d) t := by
    have h := rmP4_update_hasDerivAt_B (I := I) (M := M) hLC hLV hflow ht x
      ![a, b, c, d] 0 (connVarB G x a v) wa hcva
    simpa only [rmP4B, lapRm4, react4, Function.update_apply, Fin.isValue, Fin.reduceEq,
      ↓reduceIte, Fin.mk_one, Fin.reduceFinMk, vec4_zero, vec4_one, vec4_two, vec4_three] using h
  have hP1 : HasDerivAt (fun s ↦ rmP (G s) x a (connVarB G x b v s) c d)
      (Work.Diff.GE.lapRmAt (G t) x a (connVarB G x b v t) c d
        + Work.Diff.GE.reactionFormAt reactionMap (G t) x a (connVarB G x b v t) c d
        + rmP (G t) x a wb c d) t := by
    have h := rmP4_update_hasDerivAt_B (I := I) (M := M) hLC hLV hflow ht x
      ![a, b, c, d] 1 (connVarB G x b v) wb hcvb
    simpa only [rmP4B, lapRm4, react4, Function.update_apply, Fin.isValue, Fin.reduceEq,
      ↓reduceIte, Fin.mk_one, Fin.reduceFinMk, vec4_zero, vec4_one, vec4_two, vec4_three] using h
  have hP2 : HasDerivAt (fun s ↦ rmP (G s) x a b (connVarB G x c v s) d)
      (Work.Diff.GE.lapRmAt (G t) x a b (connVarB G x c v t) d
        + Work.Diff.GE.reactionFormAt reactionMap (G t) x a b (connVarB G x c v t) d
        + rmP (G t) x a b wc d) t := by
    have h := rmP4_update_hasDerivAt_B (I := I) (M := M) hLC hLV hflow ht x
      ![a, b, c, d] 2 (connVarB G x c v) wc hcvc
    simpa only [rmP4B, lapRm4, react4, Function.update_apply, Fin.isValue, Fin.reduceEq,
      ↓reduceIte, Fin.mk_one, Fin.reduceFinMk, vec4_zero, vec4_one, vec4_two, vec4_three] using h
  have hP3 : HasDerivAt (fun s ↦ rmP (G s) x a b c (connVarB G x d v s))
      (Work.Diff.GE.lapRmAt (G t) x a b c (connVarB G x d v t)
        + Work.Diff.GE.reactionFormAt reactionMap (G t) x a b c (connVarB G x d v t)
        + rmP (G t) x a b c wd) t := by
    have h := rmP4_update_hasDerivAt_B (I := I) (M := M) hLC hLV hflow ht x
      ![a, b, c, d] 3 (connVarB G x d v) wd hcvd
    simpa only [rmP4B, lapRm4, react4, Function.update_apply, Fin.isValue, Fin.reduceEq,
      ↓reduceIte, Fin.mk_one, Fin.reduceFinMk, vec4_zero, vec4_one, vec4_two, vec4_three] using h
  -- ### the value of the derivative
  letI hNAG : NormedAddCommGroup (TangentSpace I x) :=
    inferInstanceAs (NormedAddCommGroup E)
  letI hNS : NormedSpace ℝ (TangentSpace I x) := inferInstanceAs (NormedSpace ℝ E)
  have hderiv_a : deriv (connVarB G x a v) t = wa := hcva.deriv
  have hderiv_b : deriv (connVarB G x b v) t = wb := hcvb.deriv
  have hderiv_c : deriv (connVarB G x c v) t = wc := hcvc.deriv
  have hderiv_d : deriv (connVarB G x d v) t = wd := hcvd.deriv
  have hval : (mvfderiv I (fun y : M ↦ Work.Diff.GE.lapRmAt (G t) y ((smoothExt x a) y)
            ((smoothExt x b) y) ((smoothExt x c) y) ((smoothExt x d) y)) x v
        + mvfderiv I (fun y : M ↦ Work.Diff.GE.reactionFormAt reactionMap (G t) y
            ((smoothExt x a) y) ((smoothExt x b) y) ((smoothExt x c) y)
            ((smoothExt x d) y)) x v)
      - (Work.Diff.GE.lapRmAt (G t) x (connVarB G x a v t) b c d
        + Work.Diff.GE.reactionFormAt reactionMap (G t) x (connVarB G x a v t) b c d
        + rmP (G t) x wa b c d)
      - (Work.Diff.GE.lapRmAt (G t) x a (connVarB G x b v t) c d
        + Work.Diff.GE.reactionFormAt reactionMap (G t) x a (connVarB G x b v t) c d
        + rmP (G t) x a wb c d)
      - (Work.Diff.GE.lapRmAt (G t) x a b (connVarB G x c v t) d
        + Work.Diff.GE.reactionFormAt reactionMap (G t) x a b (connVarB G x c v t) d
        + rmP (G t) x a b wc d)
      - (Work.Diff.GE.lapRmAt (G t) x a b c (connVarB G x d v t)
        + Work.Diff.GE.reactionFormAt reactionMap (G t) x a b c (connVarB G x d v t)
        + rmP (G t) x a b c wd)
      = covRmTimeDerivB reactionMap G t x v a b c d := by
    simp only [covRmTimeDerivB, Work.Diff.GE.covLapRmAt, Work.Diff.GE.covReactionFormAt,
      hderiv_a, hderiv_b, hderiv_c, hderiv_d, connVarB]
    ring
  -- ### the function identity and the combination of the derivatives
  have hfun : ((fun s : ℝ ↦ mvfderiv I (fun y : M ↦ rmP (G s) y ((smoothExt x a) y)
          ((smoothExt x b) y) ((smoothExt x c) y) ((smoothExt x d) y)) x v)
        - (fun s : ℝ ↦ rmP (G s) x (connVarB G x a v s) b c d)
        - (fun s : ℝ ↦ rmP (G s) x a (connVarB G x b v s) c d)
        - (fun s : ℝ ↦ rmP (G s) x a b (connVarB G x c v s) d)
        - (fun s : ℝ ↦ rmP (G s) x a b c (connVarB G x d v s)))
      = (fun s : ℝ ↦ covRm (G s) x v a b c d) := by
    funext s
    simp only [Pi.sub_apply, covRm, connVarB]
  have hcomb := (((hM.sub hP0.hasDerivWithinAt).sub hP1.hasDerivWithinAt).sub
    hP2.hasDerivWithinAt).sub hP3.hasDerivWithinAt
  rw [hfun] at hcomb
  rw [hval] at hcomb
  exact hcomb

end Work.Diff.GE.EvolB
