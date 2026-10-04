import Mathlib
import Submission.Work.Diff.GE.EvolB.Assembly
import Submission.Work.Diff.GE.EvolB.WeitzBound
import Submission.Work.Diff.GE.EvolB.ReactionBound
import Submission.Work.Diff.GE.EvolB.ConnVarB
import Submission.Work.Diff.GE.EvolA.rmReact_norm_le
import Submission.Work.Diff.GE.react.rmReact_fderiv_bound
import Submission.Work.Diff.GE.EvolB.ReactionRot
import Submission.Work.Diff.GE.react.rmReact_contDiff
import Submission.Work.Diff.GE.reaction_map_defs
import Submission.Work.Diff.GE.curvbasic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The interior estimate for the fixed-vector evolution of `∇Rm` (`EvolB`)

`Work.Diff.GE.EvolB.covRm_fixed_evol_le_interior_B` is the estimate

`∂ₜ (covRm (G ·) x v a b c d) ≤ Δ∇Rm + C |Rm| |∇Rm| |v||a||b||c||d|`

at an interior time `t ∈ (0,T)` of a Ricci flow.  It is assembled from

* the evolution identity `EvolB.covRm_fixed_evol_interior_B`
  (`∂ₜ ∇Rm = ∇_v(ΔRm) + ∇_v(F(Rm)) − Σ_slot Rm(…, ∂ₜ∇_v A_slot, …)`);
* the Weitzenböck bound `EvolB.covLapRm_le_lapCovRm_B` for `∇_v(ΔRm) − Δ∇Rm`;
* the reaction-derivative bound `Work.Diff.GE.covReactionFormAt_le` for `∇_v(F(Rm))`;
* the connection-variation bound `Work.Diff.GE.connectionVariation_le` for the four slot terms,
  whose `∇_v A_slot`-derivative is identified with the `w` of `connectionVariation_le` by
  uniqueness of the Koszul characterisation `Work.Diff.GE.IsConnVar`.
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

/-- **Uniqueness of the connection-variation vector.**  `IsConnVar G t x X Y w` determines `w`
uniquely: two such vectors have the same pairing with every smooth field, in particular with the
`G t`-orthonormal frame `onFrame (G t) x`, and the expansion in that frame recovers the vector. -/
theorem IsConnVar_unique (hLC : LCSmooth I M)
    {G : ℝ → SMet I M} {T t : ℝ} {X Y : Π y : M, TangentSpace I y}
    {w w' : TangentSpace I x}
    (hw : Work.Diff.GE.IsConnVar G t x X Y w) (hw' : Work.Diff.GE.IsConnVar G t x X Y w') :
    w = w' := by
  have hframe : ∀ k : Fin (Module.finrank ℝ E),
      (G t).inner x w (Submission.Diff.onFrame (G t) x k)
        = (G t).inner x w' (Submission.Diff.onFrame (G t) x k) := by
    intro k
    have h1 := hw (smoothExt x (Submission.Diff.onFrame (G t) x k))
      (smoothExt_cmdiff x _)
    have h2 := hw' (smoothExt x (Submission.Diff.onFrame (G t) x k))
      (smoothExt_cmdiff x _)
    rw [smoothExt_apply] at h1 h2
    rw [h1, h2]
  by_cases hn : 0 < Module.finrank ℝ E
  · calc w = ∑ k, (G t).inner x w (Submission.Diff.onFrame (G t) x k)
          • Submission.Diff.onFrame (G t) x k :=
        (Work.Diff.GE.sum_smul_inner_eq_self (I := I) (M := M) (G t) x hn _
          (Work.Diff.GE.isONFrame_onFrame (I := I) (M := M) (G t) x) w).symm
    _ = ∑ k, (G t).inner x w' (Submission.Diff.onFrame (G t) x k)
          • Submission.Diff.onFrame (G t) x k :=
        Finset.sum_congr rfl fun k _ => by rw [hframe k]
    _ = w' := Work.Diff.GE.sum_smul_inner_eq_self (I := I) (M := M) (G t) x hn _
        (Work.Diff.GE.isONFrame_onFrame (I := I) (M := M) (G t) x) w'
  · have h0 : Module.finrank ℝ E = 0 := Nat.eq_zero_of_not_pos hn
    haveI : Subsingleton (TangentSpace I x) := by
      rw [← Module.finrank_zero_iff (R := ℝ) (M := TangentSpace I x)]; exact h0
    exact Subsingleton.elim w w'

/-- `Work.Diff.GE.reactionMap` is `C^∞`. -/
theorem reactionMap_contDiff_B (n : ℕ) :
    ContDiff ℝ ((⊤ : ENat) : WithTop ENat)
      (Work.Diff.GE.reactionMap : Curv4 n → Curv4 n) := by
  rw [show (Work.Diff.GE.reactionMap : Curv4 n → Curv4 n) = Work.Diff.GE.rmReact n from
    funext fun R => Work.Diff.GE.EvolA.reactionMap_eq_rmReact R]
  exact Work.Diff.GE.react.rmReact_contDiff n

/-- `Work.Diff.GE.reactionMap` is equivariant under the orthogonal action. -/
theorem reactionMap_rot_B (n : ℕ) :
    ∀ A ∈ Matrix.orthogonalGroup (Fin n) ℝ, ∀ R : Curv4 n,
      (Work.Diff.GE.reactionMap : Curv4 n → Curv4 n) (Submission.Diff.Alg.rot A R)
        = Submission.Diff.Alg.rot A (Work.Diff.GE.reactionMap R) := by
  intro A hA R
  show Work.Diff.GE.reactionMap (Submission.Diff.Alg.rot A R)
    = Submission.Diff.Alg.rot A (Work.Diff.GE.reactionMap R)
  rw [Work.Diff.GE.EvolA.reactionMap_eq_rmReact, Work.Diff.GE.EvolA.reactionMap_eq_rmReact]
  exact Work.Diff.GE.EvolB.rmReact_rot_C n A hA R

/-- `Work.Diff.GE.reactionMap` is quadratically bounded. -/
theorem reactionMap_norm_le_B (n : ℕ) :
    ∃ CF : ℝ, 0 ≤ CF ∧ ∀ R : Curv4 n,
      ‖(Work.Diff.GE.reactionMap : Curv4 n → Curv4 n) R‖ ≤ CF * ‖R‖ * ‖R‖ := by
  obtain ⟨C, hC, hb⟩ := Work.Diff.GE.EvolA.rmReact_norm_le n
  refine ⟨C, hC, fun R => ?_⟩
  rw [show (Work.Diff.GE.reactionMap : Curv4 n → Curv4 n) R = Work.Diff.GE.rmReact n R from
    Work.Diff.GE.EvolA.reactionMap_eq_rmReact R]
  exact hb R

/-- The `fderiv` of `Work.Diff.GE.reactionMap` is linearly bounded. -/
theorem reactionMap_fderiv_bound_B (n : ℕ) :
    ∃ CF' : ℝ, 0 ≤ CF' ∧ ∀ R : Curv4 n,
      ‖fderiv ℝ (Work.Diff.GE.reactionMap : Curv4 n → Curv4 n) R‖ ≤ CF' * ‖R‖ := by
  obtain ⟨C, hC, hb⟩ := Work.Diff.GE.react.rmReact_fderiv_bound n
  refine ⟨C, hC, fun R => ?_⟩
  rw [show (Work.Diff.GE.reactionMap : Curv4 n → Curv4 n) = Work.Diff.GE.rmReact n from
    funext fun R => Work.Diff.GE.EvolA.reactionMap_eq_rmReact R]
  exact hb R

/-- **The interior estimate for the fixed-vector evolution of `∇Rm`.**  There is a universal
constant `C ≥ 0` such that for every Ricci flow `G` on `[0,T)`, every `t ∈ (0,T)`, every `x` and all
tangent vectors `v, a, b, c, d`, the component `s ↦ covRm (G s) x v a b c d` is differentiable from
the right at `t` with a derivative dominated by `Δ∇Rm` plus `C |Rm| |∇Rm|` times the norms. -/
theorem covRm_fixed_evol_le_interior_B [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : LCSmooth I M) (hLV : LCVariation I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (G : ℝ → SMet I M) (T : ℝ), IsRicciFlow G T →
      ∀ t ∈ Set.Ioo 0 T, ∀ x : M, ∀ v a b c d : TangentSpace I x, ∃ D : ℝ,
        HasDerivWithinAt (fun s ↦ covRm (G s) x v a b c d) D (Set.Ico 0 T) t ∧
        D ≤ Work.Diff.GE.lapCovRmAt (G t) x v a b c d
          + C * Real.sqrt (rmNormSq (G t) x) * Real.sqrt (dRmNormSq (G t) x)
            * (Real.sqrt ((G t).inner x v v) * Real.sqrt ((G t).inner x a a)
              * Real.sqrt ((G t).inner x b b) * Real.sqrt ((G t).inner x c c)
              * Real.sqrt ((G t).inner x d d)) := by
  obtain ⟨CW, hCW0, hWeit⟩ := covLapRm_le_lapCovRm_B (I := I) (M := M) hLC
  obtain ⟨CR, hCR0, hReact⟩ := covReactionFormAt_le (I := I) (M := M) hLC
    (Work.Diff.GE.reactionMap : Curv4 (Module.finrank ℝ E) → Curv4 (Module.finrank ℝ E))
    (reactionMap_contDiff_B _) (reactionMap_norm_le_B _) (reactionMap_fderiv_bound_B _)
    (reactionMap_rot_B _)
  obtain ⟨CC, hCC0, hConn⟩ := connectionVariation_le (I := I) (M := M) hLC hLV
  refine ⟨CW + CR + CC, by linarith, ?_⟩
  intro G T hflow t ht x v a b c d
  letI hNAG : NormedAddCommGroup (TangentSpace I x) :=
    inferInstanceAs (NormedAddCommGroup E)
  letI hNS : NormedSpace ℝ (TangentSpace I x) := inferInstanceAs (NormedSpace ℝ E)
  have hid := covRm_fixed_evol_interior_B (I := I) (M := M) hLC hLV hflow ht x v a b c d
  refine ⟨covRmTimeDerivB reactionMap G t x v a b c d, hid, ?_⟩
  -- the connection-variation vectors of `connectionVariation_le`, identified with the derivatives
  obtain ⟨wa, wb, wc, wd, hwaI, hwbI, hwcI, hwdI, hconnbound⟩ :=
    hConn G T hflow t ht x v a b c d
  have hJs : JointSmooth G (Set.Ioo 0 T) :=
    hflow.1.mono (Set.prod_mono Set.Ioo_subset_Ico_self (Set.subset_univ _))
  obtain ⟨ua, hua, huaI⟩ := hLV G (Set.Ioo 0 T) isOpen_Ioo hJs t ht (smoothExt x v)
    (smoothExt x a) (smoothExt_cmdiff x v) (smoothExt_cmdiff x a) x
  obtain ⟨ub, hub, hubI⟩ := hLV G (Set.Ioo 0 T) isOpen_Ioo hJs t ht (smoothExt x v)
    (smoothExt x b) (smoothExt_cmdiff x v) (smoothExt_cmdiff x b) x
  obtain ⟨uc, huc, hucI⟩ := hLV G (Set.Ioo 0 T) isOpen_Ioo hJs t ht (smoothExt x v)
    (smoothExt x c) (smoothExt_cmdiff x v) (smoothExt_cmdiff x c) x
  obtain ⟨ud, hud, hudI⟩ := hLV G (Set.Ioo 0 T) isOpen_Ioo hJs t ht (smoothExt x v)
    (smoothExt x d) (smoothExt_cmdiff x v) (smoothExt_cmdiff x d) x
  have hua_eq : ua = wa := IsConnVar_unique (I := I) (M := M) (T := T) hLC huaI hwaI
  have hub_eq : ub = wb := IsConnVar_unique (I := I) (M := M) (T := T) hLC hubI hwbI
  have huc_eq : uc = wc := IsConnVar_unique (I := I) (M := M) (T := T) hLC hucI hwcI
  have hud_eq : ud = wd := IsConnVar_unique (I := I) (M := M) (T := T) hLC hudI hwdI
  have hda : deriv (connVarB G x a v) t = wa := by
    have h := hua
    rw [smoothExt_apply x v] at h
    have hc : HasDerivAt (connVarB G x a v) ua t := by
      show HasDerivAt (fun s : ℝ ↦
        ((lcOf (G s) (smoothExt x a) x v : TangentSpace I x) : E)) (ua : E) t
      exact h
    rw [← hua_eq]
    exact hc.deriv
  have hdb : deriv (connVarB G x b v) t = wb := by
    have h := hub
    rw [smoothExt_apply x v] at h
    have hc : HasDerivAt (connVarB G x b v) ub t := by
      show HasDerivAt (fun s : ℝ ↦
        ((lcOf (G s) (smoothExt x b) x v : TangentSpace I x) : E)) (ub : E) t
      exact h
    rw [← hub_eq]
    exact hc.deriv
  have hdc : deriv (connVarB G x c v) t = wc := by
    have h := huc
    rw [smoothExt_apply x v] at h
    have hc : HasDerivAt (connVarB G x c v) uc t := by
      show HasDerivAt (fun s : ℝ ↦
        ((lcOf (G s) (smoothExt x c) x v : TangentSpace I x) : E)) (uc : E) t
      exact h
    rw [← huc_eq]
    exact hc.deriv
  have hdd : deriv (connVarB G x d v) t = wd := by
    have h := hud
    rw [smoothExt_apply x v] at h
    have hc : HasDerivAt (connVarB G x d v) ud t := by
      show HasDerivAt (fun s : ℝ ↦
        ((lcOf (G s) (smoothExt x d) x v : TangentSpace I x) : E)) (ud : E) t
      exact h
    rw [← hud_eq]
    exact hc.deriv
  -- the three bounds
  have hW := hWeit (G t) x v a b c d
  have hR := hReact G T hflow t ⟨ht.1.le, ht.2⟩ x v a b c d
  have hZ : |rmP (G t) x wa b c d + rmP (G t) x a wb c d + rmP (G t) x a b wc d
      + rmP (G t) x a b c wd| ≤ CC * Real.sqrt (rmNormSq (G t) x)
        * Real.sqrt (dRmNormSq (G t) x)
        * (Real.sqrt ((G t).inner x v v) * Real.sqrt ((G t).inner x a a)
          * Real.sqrt ((G t).inner x b b) * Real.sqrt ((G t).inner x c c)
          * Real.sqrt ((G t).inner x d d)) := hconnbound
  have hD : covRmTimeDerivB reactionMap G t x v a b c d
      = (Work.Diff.GE.covLapRmAt (G t) x v a b c d
          + Work.Diff.GE.covReactionFormAt Work.Diff.GE.reactionMap (G t) x v a b c d)
        - (rmP (G t) x wa b c d + rmP (G t) x a wb c d + rmP (G t) x a b wc d
          + rmP (G t) x a b c wd) := by
    simp only [covRmTimeDerivB, hda, hdb, hdc, hdd]
    ring
  rw [hD]
  nlinarith [hW, hR, hZ, neg_le_abs (rmP (G t) x wa b c d + rmP (G t) x a wb c d
      + rmP (G t) x a b wc d + rmP (G t) x a b c wd),
    Real.sqrt_nonneg (rmNormSq (G t) x), Real.sqrt_nonneg (dRmNormSq (G t) x),
    Real.sqrt_nonneg ((G t).inner x v v), Real.sqrt_nonneg ((G t).inner x a a),
    Real.sqrt_nonneg ((G t).inner x b b), Real.sqrt_nonneg ((G t).inner x c c),
    Real.sqrt_nonneg ((G t).inner x d d)]

end Work.Diff.GE.EvolB
