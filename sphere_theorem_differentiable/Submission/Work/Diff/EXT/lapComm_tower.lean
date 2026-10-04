import Mathlib
import Submission.Work.Diff.EXT.reactDefs
import Submission.Work.Diff.Evol.ricci_identity_rm
import Submission.Work.Diff.EXT.curvNormK_frame_indep
import Submission.Work.Diff.EXT.covKRmExt_tensorial
import Submission.Work.Diff.EXT.covKRmExt_eval_bound
import Submission.Work.Diff.GE.swap_defs
import Submission.Work.Diff.GE.covRic_eq_sum_covRm
import Submission.Work.Diff.GE.swap_curvsection
import Submission.Work.Diff.EXT.commBoundDefs
import Submission.Work.Diff.EXT.Kpt_norm_bound
import Submission.Work.Diff.EXT.evolK_bridges
import Submission.Work.Diff.GE.covLapRm_sub_lapCovRm_summand_bound
import Submission.Work.Diff.GE.EvolB.NrmBounds
import Submission.Work.Diff.EXT.lapCommInsT
import Submission.Work.Diff.EXT.dCurvV_norm_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

section

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

local macro "Tf" : term => `((y : M) → TangentSpace I y)
local notation "consF" X:max F:max => (Fin.cons (α := fun _ : _ => Tf) X F)

/-! ## The `Ext`-pattern derivatives of the tower are the tower itself -/

/-- Updating a prepended tuple in a successor slot = prepending after updating the tail. -/
lemma upd_cons_succ {n : ℕ} (Y : Tf) (F : Fin n → Tf) (i : Fin n) (W : Tf) :
    Function.update (consF Y F) i.succ W = consF Y (Function.update F i W) := by
  funext j'
  simp only [Function.update_apply]
  split_ifs <;> simp_all

/-- **The exact recursion**, evaluated at a point (copy of `mvfderiv_ckt_gen` without the extra
`Boundaryless`/`CompactSpace` hypotheses of the original). -/
theorem mvfderiv_ckt_gen' (g : SMet I M) (k : ℕ) (F : Fin (k + 4) → Tf) (X : Tf) (x : M) :
    mvfderiv I (fun y : M => ckt g k F y) x (X x)
      = ckt g (k + 1) (consF X F) x
        + ∑ s : Fin (k + 4), ckt g k (Function.update F s (dirF g (F s) X)) x := by
  have h := congrFun (ckt_succ g k (consF X F)) x
  have hF' : (fun i : Fin (k + 4) => (consF X F) i.succ) = F := by
    funext i
    simp
  have h0 : (consF X F) 0 = X := by simp
  rw [hF', h0] at h
  simp only [Finset.sum_apply, Pi.sub_apply] at h
  linarith [h]

/-- **`extD` of the tower is the next level of the tower.** -/
theorem extD_ckt (g : SMet I M) (j : ℕ) (y : M) (Y : Tf) (F : Fin (j + 4) → Tf) :
    Work.Diff.GE.extD (Submission.Diff.lcOf g) (ckt g j) y Y F
      = ckt g (j + 1) (consF Y F) y := by
  rw [Work.Diff.GE.extD_eq, mvfderiv_ckt_gen']
  have hsum : (∑ s : Fin (j + 4), ckt g j (Function.update F s (dirF g (F s) Y)) y)
      = (∑ i : Fin (j + 4),
          ckt g j (Work.Diff.GE.upd (Submission.Diff.lcOf g) Y F i) y) :=
    Finset.sum_congr rfl fun s _ => rfl
  rw [hsum]
  ring

/-- **`extDD` of the tower is the tower two levels up.** -/
theorem extDD_ckt (g : SMet I M) (j : ℕ) (x : M) (X Y : Tf) (F : Fin (j + 4) → Tf) :
    Work.Diff.GE.extDD (Submission.Diff.lcOf g) (ckt g j) x X Y F
      = ckt g (j + 2) (consF X (consF Y F)) x := by
  have h1 : ∀ y : M, Work.Diff.GE.extD (Submission.Diff.lcOf g) (ckt g j) y Y F
      = ckt g (j + 1) (consF Y F) y := fun y => extD_ckt g j y Y F
  rw [Work.Diff.GE.extDD_eq]
  rw [show (fun y : M => Work.Diff.GE.extD (Submission.Diff.lcOf g) (ckt g j) y Y F)
      = (fun y : M => ckt g (j + 1) (consF Y F) y) from funext h1]
  rw [mvfderiv_ckt_gen']
  have hc1 : Work.Diff.GE.extD (Submission.Diff.lcOf g) (ckt g j) x
        (Work.Diff.GE.covAlong (Submission.Diff.lcOf g) X Y) F
      = ckt g (j + 1) (consF (Work.Diff.GE.covAlong (Submission.Diff.lcOf g) X Y) F) x :=
    extD_ckt g j x _ F
  have hc2 : (∑ i : Fin (j + 4), Work.Diff.GE.extD (Submission.Diff.lcOf g) (ckt g j) x Y
        (Work.Diff.GE.upd (Submission.Diff.lcOf g) X F i))
      = ∑ i : Fin (j + 4), ckt g (j + 1)
          (consF Y (Work.Diff.GE.upd (Submission.Diff.lcOf g) X F i)) x :=
    Finset.sum_congr rfl fun i _ => extD_ckt g j x Y _
  rw [hc1, hc2]
  have hsplit : (∑ s : Fin (j + 5),
        ckt g (j + 1) (Function.update (consF Y F) s (dirF g ((consF Y F) s) X)) x)
      = ckt g (j + 1) (consF (Work.Diff.GE.covAlong (Submission.Diff.lcOf g) X Y) F) x
        + ∑ i : Fin (j + 4),
            ckt g (j + 1) (consF Y (Work.Diff.GE.upd (Submission.Diff.lcOf g) X F i)) x := by
    rw [Fin.sum_univ_succ]
    have h0 : ckt g (j + 1) (Function.update (consF Y F) 0 (dirF g ((consF Y F) 0) X)) x
        = ckt g (j + 1) (consF (Work.Diff.GE.covAlong (Submission.Diff.lcOf g) X Y) F) x := by
      rw [Fin.cons_zero, Fin.update_cons_zero]
      rfl
    have hsucc : (∑ i : Fin (j + 4),
          ckt g (j + 1) (Function.update (consF Y F) i.succ (dirF g ((consF Y F) i.succ) X)) x)
        = ∑ i : Fin (j + 4),
            ckt g (j + 1) (consF Y (Work.Diff.GE.upd (Submission.Diff.lcOf g) X F i)) x := by
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      rw [upd_cons_succ, Fin.cons_succ]
      rfl
    rw [h0, hsucc]
  rw [hsplit]
  ring

/-- **The first term of the commutator, evaluated on the tuple.** -/
theorem lapComm_A (g : SMet I M) (k : ℕ) (x : M)
    (Ef : Fin (Module.finrank ℝ E) → Tf) (G : Fin (k + 5) → Tf) :
    (∑ m : Fin (Module.finrank ℝ E),
        Work.Diff.GE.extDD (Submission.Diff.lcOf g) (ckt g (k + 1)) x (Ef m) (Ef m) G)
      = ∑ m : Fin (Module.finrank ℝ E),
          ckt g (k + 3) (consF (Ef m) (consF (Ef m) G)) x :=
  Finset.sum_congr rfl fun m _ => extDD_ckt g (k + 1) x (Ef m) (Ef m) G

/-- **The tower written as the `Ext` derivative of the previous level.** -/
theorem ckt_succ_extD (g : SMet I M) (j : ℕ) (x : M) (X : Tf) (F : Fin (j + 4) → Tf) :
    ckt g (j + 1) (consF X F) x
      = Work.Diff.GE.extD (Submission.Diff.lcOf g) (ckt g j) x X F :=
  (extD_ckt g j x X F).symm

/-! ## The `∇(Δτ)` term, expanded

Expanding the `extDD`'s of the trace `Δτ` and using the product rule for the tower produces the
tower values of the statement, plus the *frame-motion* terms
`∑ m, ckt g (k+2) ((∇_{G 0}Ef m) :: Ef m :: tail G)` (and its mirror image), which cancel by the
antisymmetry of the frame velocities (lemma `Work.Diff.EXT.lapComm_frameMotion`). -/

/-- **The `∇(Δτ)` term, expanded.** -/
theorem lapComm_B_expand (hLC : Submission.Diff.LCSmooth I M) (g : SMet I M) (k : ℕ) (x : M)
    (Ef : Fin (Module.finrank ℝ E) → Tf) (hEf : ∀ i, SmoothF (Ef i))
    (G : Fin (k + 5) → Tf) (hG : ∀ i, SmoothF (G i)) :
    Work.Diff.GE.extD (Submission.Diff.lcOf g)
        (fun (F : Fin (k + 4) → Tf) => fun (y : M) =>
          ∑ m : Fin (Module.finrank ℝ E),
            Work.Diff.GE.extDD (Submission.Diff.lcOf g) (ckt g k) y (Ef m) (Ef m) F)
        x (G 0) (fun i : Fin (k + 4) => G i.succ)
      = (∑ m : Fin (Module.finrank ℝ E),
            ckt g (k + 3)
              (consF (G 0) (consF (Ef m) (consF (Ef m) (fun i : Fin (k + 4) => G i.succ)))) x)
        + ((∑ m : Fin (Module.finrank ℝ E),
              ckt g (k + 2)
                (consF (dirF g (Ef m) (G 0))
                  (consF (Ef m) (fun i : Fin (k + 4) => G i.succ))) x)
          + (∑ m : Fin (Module.finrank ℝ E),
              ckt g (k + 2)
                (consF (Ef m) (consF (dirF g (Ef m) (G 0))
                  (fun i : Fin (k + 4) => G i.succ))) x)) := by
  classical
  set T : Fin (k + 4) → Tf := fun i => G i.succ with hT
  have hTsm : ∀ i, SmoothF (T i) := fun i => hG i.succ
  -- the coefficients of `Δτ` in the tower
  have hΔC : ∀ (F : Fin (k + 4) → Tf) (y : M),
      (∑ m : Fin (Module.finrank ℝ E),
          Work.Diff.GE.extDD (Submission.Diff.lcOf g) (ckt g k) y (Ef m) (Ef m) F)
        = ∑ m : Fin (Module.finrank ℝ E),
            ckt g (k + 2) (consF (Ef m) (consF (Ef m) F)) y := by
    intro F y
    exact Finset.sum_congr rfl fun m _ => extDD_ckt g k y (Ef m) (Ef m) F
  -- smoothness of the coefficients
  have hCsm : ∀ m : Fin (Module.finrank ℝ E),
      CMDiff ∞ (fun y : M => ckt g (k + 2) (consF (Ef m) (consF (Ef m) T)) y) := by
    intro m
    exact (tensProp_all hLC g (k + 2) _ (smoothF_cons (hEf m) (smoothF_cons (hEf m) hTsm))).1
  -- the derivative of `Δτ` along `G 0`
  have hder : mvfderiv I (fun y : M => (∑ m : Fin (Module.finrank ℝ E),
          Work.Diff.GE.extDD (Submission.Diff.lcOf g) (ckt g k) y (Ef m) (Ef m) T)) x
        ((G 0) x)
      = ∑ m : Fin (Module.finrank ℝ E),
          (ckt g (k + 3) (consF (G 0) (consF (Ef m) (consF (Ef m) T))) x
            + ∑ s : Fin (k + 6),
                ckt g (k + 2)
                  (Function.update (consF (Ef m) (consF (Ef m) T)) s
                    (dirF g ((consF (Ef m) (consF (Ef m) T)) s) (G 0))) x) := by
    have hfun : (fun y : M => (∑ m : Fin (Module.finrank ℝ E),
          Work.Diff.GE.extDD (Submission.Diff.lcOf g) (ckt g k) y (Ef m) (Ef m) T))
        = (fun y : M => ∑ m : Fin (Module.finrank ℝ E),
            ckt g (k + 2) (consF (Ef m) (consF (Ef m) T)) y) :=
      funext fun y => hΔC T y
    rw [hfun]
    rw [Work.Diff.GE.Kato3.mvfderiv_sum Finset.univ
      (fun m : Fin (Module.finrank ℝ E) =>
        fun y : M => ckt g (k + 2) (consF (Ef m) (consF (Ef m) T)) y) hCsm x ((G 0) x)]
    exact Finset.sum_congr rfl fun m _ =>
      mvfderiv_ckt_gen' g (k + 2) (consF (Ef m) (consF (Ef m) T)) (G 0) x
  -- the split of the inner sums
  have hsplit : ∀ m : Fin (Module.finrank ℝ E),
      (∑ s : Fin (k + 6),
          ckt g (k + 2) (Function.update (consF (Ef m) (consF (Ef m) T)) s
            (dirF g ((consF (Ef m) (consF (Ef m) T)) s) (G 0))) x)
        = ckt g (k + 2) (consF (dirF g (Ef m) (G 0)) (consF (Ef m) T)) x
          + ckt g (k + 2) (consF (Ef m) (consF (dirF g (Ef m) (G 0)) T)) x
          + ∑ j : Fin (k + 4),
              ckt g (k + 2) (consF (Ef m) (consF (Ef m)
                (Work.Diff.GE.upd (Submission.Diff.lcOf g) (G 0) T j))) x := by
    intro m
    have e1 : (∑ s : Fin (k + 6),
          ckt g (k + 2) (Function.update (consF (Ef m) (consF (Ef m) T)) s
            (dirF g ((consF (Ef m) (consF (Ef m) T)) s) (G 0))) x)
        = ckt g (k + 2) (Function.update (consF (Ef m) (consF (Ef m) T)) 0
              (dirF g ((consF (Ef m) (consF (Ef m) T)) 0) (G 0))) x
          + ckt g (k + 2) (Function.update (consF (Ef m) (consF (Ef m) T))
              ((0 : Fin (k + 5)).succ)
              (dirF g ((consF (Ef m) (consF (Ef m) T)) ((0 : Fin (k + 5)).succ)) (G 0))) x
          + ∑ j : Fin (k + 4),
              ckt g (k + 2) (Function.update (consF (Ef m) (consF (Ef m) T)) j.succ.succ
                (dirF g ((consF (Ef m) (consF (Ef m) T)) j.succ.succ) (G 0))) x := by
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      ring
    rw [e1]
    have h1 : Function.update (consF (Ef m) (consF (Ef m) T)) 0
        (dirF g ((consF (Ef m) (consF (Ef m) T)) 0) (G 0))
        = consF (dirF g (Ef m) (G 0)) (consF (Ef m) T) := by
      rw [Fin.cons_zero, Fin.update_cons_zero]
    have h2 : Function.update (consF (Ef m) (consF (Ef m) T))
        ((0 : Fin (k + 5)).succ)
        (dirF g ((consF (Ef m) (consF (Ef m) T)) ((0 : Fin (k + 5)).succ)) (G 0))
        = consF (Ef m) (consF (dirF g (Ef m) (G 0)) T) := by
      simp only [upd_cons_succ, Fin.update_cons_zero, Fin.cons_succ, Fin.cons_zero]
    have h3 : ∀ j : Fin (k + 4),
        Function.update (consF (Ef m) (consF (Ef m) T)) j.succ.succ
          (dirF g ((consF (Ef m) (consF (Ef m) T)) j.succ.succ) (G 0))
        = consF (Ef m) (consF (Ef m)
            (Work.Diff.GE.upd (Submission.Diff.lcOf g) (G 0) T j)) := by
      intro j
      simp only [upd_cons_succ, Fin.cons_succ, Work.Diff.GE.upd, Work.Diff.GE.covAlong, dirF]
      rfl
    have h3s : (∑ j : Fin (k + 4),
          ckt g (k + 2) (Function.update (consF (Ef m) (consF (Ef m) T)) j.succ.succ
            (dirF g ((consF (Ef m) (consF (Ef m) T)) j.succ.succ) (G 0))) x)
        = ∑ j : Fin (k + 4),
            ckt g (k + 2) (consF (Ef m) (consF (Ef m)
              (Work.Diff.GE.upd (Submission.Diff.lcOf g) (G 0) T j))) x :=
      Finset.sum_congr rfl fun j _ => congrArg (fun W => ckt g (k + 2) W x) (h3 j)
    rw [h1, h2, h3s]
  -- the correction sum of `extD`
  have hcorr : (∑ i : Fin (k + 4),
        (∑ m : Fin (Module.finrank ℝ E),
          Work.Diff.GE.extDD (Submission.Diff.lcOf g) (ckt g k) x (Ef m) (Ef m)
            (Work.Diff.GE.upd (Submission.Diff.lcOf g) (G 0) T i)))
      = ∑ i : Fin (k + 4), ∑ m : Fin (Module.finrank ℝ E),
          ckt g (k + 2) (consF (Ef m) (consF (Ef m)
            (Work.Diff.GE.upd (Submission.Diff.lcOf g) (G 0) T i))) x := by
    refine Finset.sum_congr rfl fun i _ => ?_
    exact hΔC _ x
  rw [Work.Diff.GE.extD_eq]
  rw [hder]
  rw [hcorr]
  -- now combine
  have hcm : (∑ i : Fin (k + 4), ∑ m : Fin (Module.finrank ℝ E),
        ckt g (k + 2) (consF (Ef m) (consF (Ef m)
          (Work.Diff.GE.upd (Submission.Diff.lcOf g) (G 0) T i))) x)
      = ∑ m : Fin (Module.finrank ℝ E), ∑ j : Fin (k + 4),
          ckt g (k + 2) (consF (Ef m) (consF (Ef m)
            (Work.Diff.GE.upd (Submission.Diff.lcOf g) (G 0) T j))) x :=
    Finset.sum_comm
  rw [hcm]
  have hPS : (∑ m : Fin (Module.finrank ℝ E),
        ∑ s : Fin (k + 6),
          ckt g (k + 2) (Function.update (consF (Ef m) (consF (Ef m) T)) s
            (dirF g ((consF (Ef m) (consF (Ef m) T)) s) (G 0))) x)
      = (∑ m : Fin (Module.finrank ℝ E),
            ckt g (k + 2) (consF (dirF g (Ef m) (G 0)) (consF (Ef m) T)) x)
        + (∑ m : Fin (Module.finrank ℝ E),
            ckt g (k + 2) (consF (Ef m) (consF (dirF g (Ef m) (G 0)) T)) x)
        + ∑ m : Fin (Module.finrank ℝ E), ∑ j : Fin (k + 4),
            ckt g (k + 2) (consF (Ef m) (consF (Ef m)
              (Work.Diff.GE.upd (Submission.Diff.lcOf g) (G 0) T j))) x := by
    rw [show (∑ m : Fin (Module.finrank ℝ E), ∑ s : Fin (k + 6),
          ckt g (k + 2) (Function.update (consF (Ef m) (consF (Ef m) T)) s
            (dirF g ((consF (Ef m) (consF (Ef m) T)) s) (G 0))) x)
        = ∑ m : Fin (Module.finrank ℝ E),
            (ckt g (k + 2) (consF (dirF g (Ef m) (G 0)) (consF (Ef m) T)) x
              + ckt g (k + 2) (consF (Ef m) (consF (dirF g (Ef m) (G 0)) T)) x
              + ∑ j : Fin (k + 4),
                  ckt g (k + 2) (consF (Ef m) (consF (Ef m)
                    (Work.Diff.GE.upd (Submission.Diff.lcOf g) (G 0) T j))) x) from
      Finset.sum_congr rfl fun m _ => hsplit m]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_add_distrib, hPS]
  ring


/-- `ckt` at a point is `Kpt` on the values of the tuple. -/
theorem ckt_eq_Kpt' (hLC : Submission.Diff.LCSmooth I M) (g : SMet I M) (j : ℕ) (x : M)
    {T : Fin (j + 4) → Tf} (hT : ∀ s, SmoothF (T s)) :
    ckt g j T x = Kpt g x j (fun s => T s x) := by
  have h := ckt_val_dep_all (I := I) (M := M) hLC g j x hT
    (fun s => Work.Diff.GE.smoothExt_cmdiff x (T s x))
    (fun s => by rw [Work.Diff.GE.smoothExt_apply])
  show ckt g j T x = ckt g j (fun s => smoothExt x (T s x)) x
  exact h

/-! ## The frame-motion terms cancel

The two families of tower values with `∇_X Ef m` inserted in the first or second slot cancel: the
matrix `ω m k = ⟪∇_X Ef m, Ef k⟫` is skew (`Work.Diff.GE.covRic_frame_skew`, from metric
compatibility and the orthonormality near `x`), while the contracted array is symmetric in `(m,k)`. -/

/-- The value tuple `(Ef m x, Ef m x, F·x)`. -/
noncomputable def frameVal {k : ℕ} (Ef : Fin (Module.finrank ℝ E) → Tf) (F : Fin (k + 4) → Tf)
    (x : M) (m : Fin (Module.finrank ℝ E)) : Fin (k + 6) → TangentSpace I x :=
  fun s => (consF (Ef m) (consF (Ef m) F)) s x

/-- Prepending `W` to `(A, F)` is the value-level update of `(A, A, F)` in the first slot. -/
lemma cons_cons_val_zero {n : ℕ} (A : Tf) (F : Fin n → Tf) (x : M) (W : Tf) :
    (fun s : Fin (n + 2) => (consF W (consF A F)) s x)
      = Function.update (fun s : Fin (n + 2) => (consF A (consF A F)) s x) 0 (W x) := by
  have h2 : consF W (consF A F) = Function.update (consF A (consF A F)) 0 W := by
    rw [Fin.update_cons_zero]
  have h3 : (fun s : Fin (n + 2) => (consF W (consF A F)) s x)
      = (fun s : Fin (n + 2) => (Function.update (consF A (consF A F)) 0 W) s x) := by
    rw [h2]
  rw [h3]
  funext s
  rw [Function.update_apply, Function.update_apply]
  by_cases hs : s = 0
  · rw [if_pos hs, if_pos hs]
  · rw [if_neg hs, if_neg hs]

/-- Prepending `W` to `F` after `A` is the value-level update of `(A, A, F)` in the second slot. -/
lemma cons_cons_val_one {n : ℕ} (A : Tf) (F : Fin n → Tf) (x : M) (W : Tf) :
    (fun s : Fin (n + 2) => (consF A (consF W F)) s x)
      = Function.update (fun s : Fin (n + 2) => (consF A (consF A F)) s x)
          ((0 : Fin (n + 1)).succ) (W x) := by
  have h1 : consF W F = Function.update (consF A F) 0 W := by
    rw [Fin.update_cons_zero]
  have h2 : consF A (consF W F)
      = Function.update (consF A (consF A F)) ((0 : Fin (n + 1)).succ) W := by
    rw [h1, upd_cons_succ]
  have h3 : (fun s : Fin (n + 2) => (consF A (consF W F)) s x)
      = (fun s : Fin (n + 2) =>
          (Function.update (consF A (consF A F)) ((0 : Fin (n + 1)).succ) W) s x) := by
    rw [h2]
  rw [h3]
  funext s
  rw [Function.update_apply, Function.update_apply]
  by_cases hs : s = ((0 : Fin (n + 1)).succ)
  · rw [if_pos hs, if_pos hs]
  · rw [if_neg hs, if_neg hs]

/-- **The frame-motion terms cancel** (`∇_{Ef m} X` inserted in the first or second slot). -/
theorem Kpt_frameMotion (hLC : Submission.Diff.LCSmooth I M) (g : SMet I M) (x : M) (k : ℕ)
    (Ef : Fin (Module.finrank ℝ E) → Tf) (hEf : ∀ i, SmoothF (Ef i))
    (hON : ∀ᶠ y in 𝓝 x, IsONFrame g y (fun i => Ef i y))
    (X : Tf) (hX : SmoothF X) (F : Fin (k + 4) → Tf) (hF : ∀ i, SmoothF (F i)) :
    (∑ m : Fin (Module.finrank ℝ E),
        Kpt g x (k + 2)
          (Function.update (frameVal (I := I) (M := M) Ef F x m) 0 (lcOf g (Ef m) x (X x))))
      + (∑ m : Fin (Module.finrank ℝ E),
          Kpt g x (k + 2)
            (Function.update (frameVal (I := I) (M := M) Ef F x m) ((0 : Fin (k + 5)).succ)
              (lcOf g (Ef m) x (X x)))) = 0 := by
  classical
  by_cases hfr : 0 < Module.finrank ℝ E
  · have hONx : IsONFrame g x (fun m => Ef m x) := hON.self_of_nhds
    have hskew : ∀ m p : Fin (Module.finrank ℝ E),
        g.inner x (lcOf g (Ef m) x (X x)) (Ef p x)
          = - g.inner x (lcOf g (Ef p) x (X x)) (Ef m x) := by
      intro m p
      have h := Work.Diff.GE.covRic_frame_skew (I := I) (M := M) hLC g x (X x) Ef hEf hON m p
      rw [← g.symm x (lcOf g (Ef p) x (X x)) (Ef m x)] at h
      linarith [h]
    have hexp : ∀ m : Fin (Module.finrank ℝ E), lcOf g (Ef m) x (X x)
        = ∑ p, g.inner x (lcOf g (Ef m) x (X x)) (Ef p x) • Ef p x :=
      fun m => (Work.Diff.GE.sum_smul_inner_eq_self g x hfr (fun i => Ef i x) hONx
        (lcOf g (Ef m) x (X x))).symm
    have hP : (∑ m : Fin (Module.finrank ℝ E),
          Kpt g x (k + 2) (Function.update (frameVal (I := I) (M := M) Ef F x m) 0
            (lcOf g (Ef m) x (X x))))
        = ∑ m : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
            g.inner x (lcOf g (Ef m) x (X x)) (Ef p x)
              * Kpt g x (k + 2) (Function.update (frameVal (I := I) (M := M) Ef F x m) 0
                  (Ef p x)) := by
      refine Finset.sum_congr rfl fun m _ => ?_
      conv_lhs => rw [hexp m]
      rw [show Kpt g x (k + 2) (Function.update (frameVal (I := I) (M := M) Ef F x m) 0
              (∑ p, g.inner x (lcOf g (Ef m) x (X x)) (Ef p x) • Ef p x))
          = KptLin hLC g x (k + 2)
              (Function.update (frameVal (I := I) (M := M) Ef F x m) 0
                (∑ p, g.inner x (lcOf g (Ef m) x (X x)) (Ef p x) • Ef p x)) from rfl]
      rw [MultilinearMap.map_update_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [MultilinearMap.map_update_smul, smul_eq_mul]
      rfl
    have hQ : (∑ m : Fin (Module.finrank ℝ E),
          Kpt g x (k + 2) (Function.update (frameVal (I := I) (M := M) Ef F x m)
            ((0 : Fin (k + 5)).succ) (lcOf g (Ef m) x (X x))))
        = ∑ m : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
            g.inner x (lcOf g (Ef m) x (X x)) (Ef p x)
              * Kpt g x (k + 2) (Function.update (frameVal (I := I) (M := M) Ef F x m)
                  ((0 : Fin (k + 5)).succ) (Ef p x)) := by
      refine Finset.sum_congr rfl fun m _ => ?_
      conv_lhs => rw [hexp m]
      rw [show Kpt g x (k + 2) (Function.update (frameVal (I := I) (M := M) Ef F x m)
              ((0 : Fin (k + 5)).succ)
              (∑ p, g.inner x (lcOf g (Ef m) x (X x)) (Ef p x) • Ef p x))
          = KptLin hLC g x (k + 2)
              (Function.update (frameVal (I := I) (M := M) Ef F x m)
                ((0 : Fin (k + 5)).succ)
                (∑ p, g.inner x (lcOf g (Ef m) x (X x)) (Ef p x) • Ef p x)) from rfl]
      rw [MultilinearMap.map_update_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [MultilinearMap.map_update_smul, smul_eq_mul]
      rfl
    have hkey : (∑ m : Fin (Module.finrank ℝ E),
          Kpt g x (k + 2) (Function.update (frameVal (I := I) (M := M) Ef F x m) 0
            (lcOf g (Ef m) x (X x))))
        + (∑ m : Fin (Module.finrank ℝ E),
          Kpt g x (k + 2) (Function.update (frameVal (I := I) (M := M) Ef F x m)
            ((0 : Fin (k + 5)).succ) (lcOf g (Ef m) x (X x))))
        = (∑ m : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
              g.inner x (lcOf g (Ef m) x (X x)) (Ef p x)
                * Kpt g x (k + 2) (Function.update (frameVal (I := I) (M := M) Ef F x m) 0
                    (Ef p x)))
          + (∑ m : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
              g.inner x (lcOf g (Ef m) x (X x)) (Ef p x)
                * Kpt g x (k + 2) (Function.update (frameVal (I := I) (M := M) Ef F x m)
                    ((0 : Fin (k + 5)).succ) (Ef p x))) := by
      rw [hP, hQ]
    rw [hkey]
    have e1 : (∑ m : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
          g.inner x (lcOf g (Ef m) x (X x)) (Ef p x)
            * Kpt g x (k + 2) (Function.update (frameVal (I := I) (M := M) Ef F x m) 0
                (Ef p x)))
        = ∑ m : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
            g.inner x (lcOf g (Ef m) x (X x)) (Ef p x)
              * Kpt g x (k + 2)
                  (fun s : Fin (k + 6) => (consF (Ef p) (consF (Ef m) F)) s x) := by
      refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun p _ => ?_
      rw [show Function.update (frameVal (I := I) (M := M) Ef F x m) 0 (Ef p x)
          = (fun s : Fin (k + 6) => (consF (Ef p) (consF (Ef m) F)) s x) from
        (cons_cons_val_zero (A := Ef m) (F := F) (x := x) (W := Ef p)).symm]
    have e2 : (∑ m : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
          g.inner x (lcOf g (Ef m) x (X x)) (Ef p x)
            * Kpt g x (k + 2) (Function.update (frameVal (I := I) (M := M) Ef F x m)
                ((0 : Fin (k + 5)).succ) (Ef p x)))
        = ∑ m : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
            g.inner x (lcOf g (Ef m) x (X x)) (Ef p x)
              * Kpt g x (k + 2)
                  (fun s : Fin (k + 6) => (consF (Ef m) (consF (Ef p) F)) s x) := by
      refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun p _ => ?_
      rw [show Function.update (frameVal (I := I) (M := M) Ef F x m)
            ((0 : Fin (k + 5)).succ) (Ef p x)
          = (fun s : Fin (k + 6) => (consF (Ef m) (consF (Ef p) F)) s x) from
        (cons_cons_val_one (A := Ef m) (F := F) (x := x) (W := Ef p)).symm]
    rw [e1, e2]
    exact Work.Diff.GE.covRic_skew_sum_zero
      (fun m p => g.inner x (lcOf g (Ef m) x (X x)) (Ef p x))
      (fun u v => Kpt g x (k + 2)
        (fun s : Fin (k + 6) => (consF (Ef u) (consF (Ef v) F)) s x)) hskew
  · have h0 : Module.finrank ℝ E = 0 := Nat.eq_zero_of_not_pos hfr
    haveI : IsEmpty (Fin (Module.finrank ℝ E)) := by rw [h0]; infer_instance
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]

/-! ## Reduction of the commutator to two tower values -/

/-- **The commutator reduces to `Δ(∇τ) − ∇(Δτ)` in tower form.** -/
theorem lapComm_reduce (hLC : Submission.Diff.LCSmooth I M) (g : SMet I M) (k : ℕ) (x : M)
    (Ef : Fin (Module.finrank ℝ E) → Tf) (hEf : ∀ i, SmoothF (Ef i))
    (hON : ∀ᶠ y in 𝓝 x, IsONFrame g y (fun i => Ef i y))
    (G : Fin (k + 5) → Tf) (hG : ∀ i, SmoothF (G i)) :
    (∑ m : Fin (Module.finrank ℝ E),
        Work.Diff.GE.extDD (Submission.Diff.lcOf g) (ckt g (k + 1)) x (Ef m) (Ef m) G)
      - Work.Diff.GE.extD (Submission.Diff.lcOf g)
          (fun (F : Fin (k + 4) → Tf) => fun (y : M) =>
            ∑ m : Fin (Module.finrank ℝ E),
              Work.Diff.GE.extDD (Submission.Diff.lcOf g) (ckt g k) y (Ef m) (Ef m) F)
          x (G 0) (fun i : Fin (k + 4) => G i.succ)
      = (∑ m : Fin (Module.finrank ℝ E),
            ckt g (k + 3) (consF (Ef m) (consF (Ef m) G)) x)
        - (∑ m : Fin (Module.finrank ℝ E),
            ckt g (k + 3)
              (consF (G 0) (consF (Ef m) (consF (Ef m) (fun i : Fin (k + 4) => G i.succ)))) x) := by
  set T : Fin (k + 4) → Tf := fun i => G i.succ with hT
  have hTsm : ∀ i, SmoothF (T i) := fun i => hG i.succ
  have hTval : (fun i : Fin (k + 4) => G i.succ) = T := rfl
  rw [lapComm_A g k x Ef G, lapComm_B_expand hLC g k x Ef hEf G hG]
  -- the frame-motion sums, in `Kpt` form
  have e1 : (∑ m : Fin (Module.finrank ℝ E),
        ckt g (k + 2) (consF (dirF g (Ef m) (G 0)) (consF (Ef m) T)) x)
      = ∑ m : Fin (Module.finrank ℝ E),
          Kpt g x (k + 2) (Function.update (frameVal (I := I) (M := M) Ef T x m) 0
            (lcOf g (Ef m) x ((G 0) x))) := by
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [ckt_eq_Kpt' hLC g (k + 2) x
      (smoothF_cons (dirF_smooth hLC g (hEf m) (hG 0)) (smoothF_cons (hEf m) hTsm))]
    rw [show (fun s : Fin (k + 6) => (consF (dirF g (Ef m) (G 0)) (consF (Ef m) T)) s x)
        = Function.update (frameVal (I := I) (M := M) Ef T x m) 0
            (lcOf g (Ef m) x ((G 0) x)) from by
      rw [show frameVal (I := I) (M := M) Ef T x m
          = (fun s : Fin (k + 6) => (consF (Ef m) (consF (Ef m) T)) s x) from rfl]
      exact cons_cons_val_zero (A := Ef m) (F := T) (x := x) (W := dirF g (Ef m) (G 0))]
  have e2 : (∑ m : Fin (Module.finrank ℝ E),
        ckt g (k + 2) (consF (Ef m) (consF (dirF g (Ef m) (G 0)) T)) x)
      = ∑ m : Fin (Module.finrank ℝ E),
          Kpt g x (k + 2) (Function.update (frameVal (I := I) (M := M) Ef T x m)
            ((0 : Fin (k + 5)).succ) (lcOf g (Ef m) x ((G 0) x))) := by
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [ckt_eq_Kpt' hLC g (k + 2) x
      (smoothF_cons (hEf m) (smoothF_cons (dirF_smooth hLC g (hEf m) (hG 0)) hTsm))]
    rw [show (fun s : Fin (k + 6) => (consF (Ef m) (consF (dirF g (Ef m) (G 0)) T)) s x)
        = Function.update (frameVal (I := I) (M := M) Ef T x m)
            ((0 : Fin (k + 5)).succ) (lcOf g (Ef m) x ((G 0) x)) from by
      rw [show frameVal (I := I) (M := M) Ef T x m
          = (fun s : Fin (k + 6) => (consF (Ef m) (consF (Ef m) T)) s x) from rfl]
      exact cons_cons_val_one (A := Ef m) (F := T) (x := x) (W := dirF g (Ef m) (G 0))]
  have hfm : (∑ m : Fin (Module.finrank ℝ E),
          Kpt g x (k + 2) (Function.update (frameVal (I := I) (M := M) Ef T x m) 0
            (lcOf g (Ef m) x ((G 0) x))))
      + (∑ m : Fin (Module.finrank ℝ E),
          Kpt g x (k + 2) (Function.update (frameVal (I := I) (M := M) Ef T x m)
            ((0 : Fin (k + 5)).succ) (lcOf g (Ef m) x ((G 0) x)))) = 0 :=
    Kpt_frameMotion hLC g x k Ef hEf hON (G 0) (hG 0) T hTsm
  have hB2B3 : (∑ m : Fin (Module.finrank ℝ E),
        ckt g (k + 2) (consF (dirF g (Ef m) (G 0)) (consF (Ef m) T)) x)
      + (∑ m : Fin (Module.finrank ℝ E),
        ckt g (k + 2) (consF (Ef m) (consF (dirF g (Ef m) (G 0)) T)) x) = 0 := by
    rw [e1, e2]
    exact hfm
  rw [hB2B3]
  ring

/-! ## The Ricci identity for the tower (first two slots)

`ckt g (j+2) (a :: b :: R) - ckt g (j+2) (b :: a :: R)` is minus the curvature acting on each slot of
the level-`j` tower.  This is the general Ricci identity for the `Ext` pattern
(`Work.Diff.Evol.ricci_id_aux_extDD_antisymm`), whose proof we redo for `τ = ckt g j` with the
`C^∞(M)`-linearity of the tower only invoked on *smooth* fields (`TensProp_add`/`TensProp_smul`). -/

/-- `SmoothF` of a difference of fields. -/
lemma smoothF_sub' {A B : Tf} (hA : SmoothF A) (hB : SmoothF B) : SmoothF (A - B) := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ B]
  exact smoothF_add hA (smoothF_smul (contMDiff_const (c := (-1 : ℝ))) hB)

/-- Combining four fields in one slot of the tower (smooth fields), function form. -/
lemma ckt_update_comb_fun (hLC : Submission.Diff.LCSmooth I M) (g : SMet I M) (j : ℕ)
    {F : Fin (j + 4) → Tf} (hF : ∀ s, SmoothF (F s)) (i : Fin (j + 4))
    (Z1 Z2 Z3 Z4 : Tf) (h1 : SmoothF Z1) (h2 : SmoothF Z2) (h3 : SmoothF Z3)
    (h4 : SmoothF Z4) :
    ckt g j (Function.update F i Z1) - ckt g j (Function.update F i Z2)
      + (ckt g j (Function.update F i Z3) - ckt g j (Function.update F i Z4))
    = ckt g j (Function.update F i (Z1 - Z2 + Z3 - Z4)) := by
  classical
  have hT := tensProp_all hLC g j
  have hsub : ∀ (A B : Tf), SmoothF A → SmoothF B →
      ckt g j (Function.update F i (A - B))
        = ckt g j (Function.update F i A) - ckt g j (Function.update F i B) := by
    intro A B hA hB
    rw [show A - B = A + (-1 : ℝ) • B from by rw [neg_one_smul, sub_eq_add_neg]]
    rw [TensProp_add (hLC) (g) (k := j) hT (F := F) hF (s := i) (X := A)
        (Y := (-1 : ℝ) • B) hA (smoothF_smul (contMDiff_const (c := (-1 : ℝ))) hB)]
    rw [show ckt g j (Function.update F i ((-1 : ℝ) • B))
        = ((-1 : ℝ) • ckt g j (Function.update F i B)) from
      TensProp_smul (hLC) (g) (k := j) hT (F := F) hF (s := i) (-1) (X := B) hB]
    funext z
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, neg_one_mul]
    ring
  have hsplit : Z1 - Z2 + Z3 - Z4 = (Z1 - Z2) + (Z3 - Z4) := by abel
  rw [hsplit]
  rw [TensProp_add (hLC) (g) (k := j) hT (F := F) hF (s := i) (X := Z1 - Z2)
    (Y := Z3 - Z4) (smoothF_sub' h1 h2) (smoothF_sub' h3 h4)]
  rw [hsub Z1 Z2 h1 h2, hsub Z3 Z4 h3 h4]

/-- The same identity, evaluated at a point. -/
lemma ckt_update_comb (hLC : Submission.Diff.LCSmooth I M) (g : SMet I M) (j : ℕ)
    {F : Fin (j + 4) → Tf} (hF : ∀ s, SmoothF (F s)) (i : Fin (j + 4))
    (Z1 Z2 Z3 Z4 : Tf) (h1 : SmoothF Z1) (h2 : SmoothF Z2) (h3 : SmoothF Z3)
    (h4 : SmoothF Z4) (x : M) :
    ckt g j (Function.update F i Z1) x - ckt g j (Function.update F i Z2) x
      + (ckt g j (Function.update F i Z3) x - ckt g j (Function.update F i Z4) x)
    = ckt g j (Function.update F i (Z1 - Z2 + Z3 - Z4)) x :=
  congrFun (ckt_update_comb_fun hLC g j hF i Z1 Z2 Z3 Z4 h1 h2 h3 h4) x


/-- **The Ricci identity for the tower** (first two slots). -/
theorem ckt_ricci (hLC : Submission.Diff.LCSmooth I M) (g : SMet I M) (j : ℕ) (x : M)
    (a b : Tf) (ha : SmoothF a) (hb : SmoothF b)
    (R : Fin (j + 4) → Tf) (hR : ∀ s, SmoothF (R s)) :
    ckt g (j + 2) (consF a (consF b R)) x - ckt g (j + 2) (consF b (consF a R)) x
      = - ∑ s : Fin (j + 4),
          ckt g j (Function.update R s (fun y => curv (Submission.Diff.lcOf g) a b (R s) y)) x := by
  obtain ⟨hcov0, htor, -⟩ := hLC g
  obtain ⟨hcov⟩ := hcov0
  have hτ : ∀ F : Fin (j + 4) → Tf, (∀ s, SmoothF (F s)) → CMDiff ∞ (ckt g j F) :=
    fun F hF => (tensProp_all hLC g j F hF).1
  have hgen : ∀ (X Y : Tf) (hX : SmoothF X) (hY : SmoothF Y) (F : Fin (j + 4) → Tf),
      (∀ s, SmoothF (F s)) →
      Work.Diff.GE.extDD (Submission.Diff.lcOf g) (ckt g j) x X Y F
        - Work.Diff.GE.extDD (Submission.Diff.lcOf g) (ckt g j) x Y X F
      = -∑ i, ckt g j (Function.update F i
          (fun y => curv (Submission.Diff.lcOf g) X Y (F i) y)) x := by
    intro X Y hX hY F hF
    classical
    rw [Work.Diff.GE.extDD_expand (Submission.Diff.lcOf g) hcov (ckt g j) hτ x X Y hY F hF,
        Work.Diff.GE.extDD_expand (Submission.Diff.lcOf g) hcov (ckt g j) hτ x Y X hX F hF]
    have hT1 : (∑ i, (mvfderiv I (fun y : M =>
            ckt g j (Work.Diff.GE.upd (Submission.Diff.lcOf g) Y F i) y) x) (X x))
        = (∑ i, (mvfderiv I (ckt g j (Work.Diff.GE.upd (Submission.Diff.lcOf g) Y F i)) x)
            (X x)) :=
      Finset.sum_congr rfl fun i _ => rfl
    have hT2 : (∑ i, (mvfderiv I (fun y : M =>
            ckt g j (Work.Diff.GE.upd (Submission.Diff.lcOf g) X F i) y) x) (Y x))
        = (∑ i, (mvfderiv I (ckt g j (Work.Diff.GE.upd (Submission.Diff.lcOf g) X F i)) x)
            (Y x)) :=
      Finset.sum_congr rfl fun i _ => rfl
    rw [hT1, hT2]
    set A := (mvfderiv I (fun y => (mvfderiv I (ckt g j F) y) (Y y)) x) (X x) with hA
    set A' := (mvfderiv I (fun y => (mvfderiv I (ckt g j F) y) (X y)) x) (Y x) with hA'
    set B := (mvfderiv I (ckt g j F) x)
      (Work.Diff.GE.covAlong (Submission.Diff.lcOf g) X Y x) with hB
    set B' := (mvfderiv I (ckt g j F) x)
      (Work.Diff.GE.covAlong (Submission.Diff.lcOf g) Y X x) with hB'
    set TY := ∑ i, (mvfderiv I (ckt g j (Work.Diff.GE.upd (Submission.Diff.lcOf g) Y F i)) x)
      (X x) with hTY
    set TX := ∑ i, (mvfderiv I (ckt g j (Work.Diff.GE.upd (Submission.Diff.lcOf g) X F i)) x)
      (Y x) with hTX
    set C := ∑ i, ckt g j (Work.Diff.GE.upd (Submission.Diff.lcOf g)
      (Work.Diff.GE.covAlong (Submission.Diff.lcOf g) X Y) F i) x with hC
    set C' := ∑ i, ckt g j (Work.Diff.GE.upd (Submission.Diff.lcOf g)
      (Work.Diff.GE.covAlong (Submission.Diff.lcOf g) Y X) F i) x with hC'
    set D := ∑ i, ∑ k, ckt g j (Work.Diff.GE.upd (Submission.Diff.lcOf g) Y
      (Work.Diff.GE.upd (Submission.Diff.lcOf g) X F i) k) x with hD
    set D' := ∑ i, ∑ k, ckt g j (Work.Diff.GE.upd (Submission.Diff.lcOf g) X
      (Work.Diff.GE.upd (Submission.Diff.lcOf g) Y F i) k) x with hD'
    set S := ∑ i, ckt g j (Function.update F i
      (fun y => curv (Submission.Diff.lcOf g) X Y (F i) y)) x with hS
    have hred : A - TY - B + C - TX + D - (A' - TX - B' + C' - TY + D')
        = (A - A') - (B - B') + (C - C') + (D - D') := by ring
    rw [hred]
    have hAB : A - A' = B - B' := by
      rw [hA, hA', hB, hB']
      have hcl := Commons.Geometry.Manifold.VectorField.mvfderiv_second_along_fields
        (f := ckt g j F) (x := x) (hτ F hF) hX hY
      rw [hcl]
      have hsub1 : (mvfderiv I (fun y => (mvfderiv I (ckt g j F) y) (X y)) x) (Y x)
            + (mvfderiv I (ckt g j F) x) (mlieBracket I X Y x)
          - (mvfderiv I (fun y => (mvfderiv I (ckt g j F) y) (X y)) x) (Y x)
          = (mvfderiv I (ckt g j F) x) (mlieBracket I X Y x) := by ring
      rw [hsub1]
      rw [← ContinuousLinearMap.map_sub,
        (CovariantDerivative.torsion_eq_zero_iff (cov := Submission.Diff.lcOf g)).mp htor
          ((hX x).mdifferentiableAt (by simp)) ((hY x).mdifferentiableAt (by simp))]
    have hoff : ∀ i k : Fin (j + 4), k ≠ i →
        ckt g j (Work.Diff.GE.upd (Submission.Diff.lcOf g) Y
          (Work.Diff.GE.upd (Submission.Diff.lcOf g) X F k) i) x
          = ckt g j (Work.Diff.GE.upd (Submission.Diff.lcOf g) X
              (Work.Diff.GE.upd (Submission.Diff.lcOf g) Y F i) k) x := by
      intro i k hki
      have h1 : (Function.update F k (Work.Diff.GE.covAlong (Submission.Diff.lcOf g) X (F k))) i
          = F i := Function.update_of_ne (Ne.symm hki) _ _
      have h2 : (Function.update F i (Work.Diff.GE.covAlong (Submission.Diff.lcOf g) Y (F i))) k
          = F k := Function.update_of_ne hki _ _
      have hupd : Work.Diff.GE.upd (Submission.Diff.lcOf g) Y
            (Work.Diff.GE.upd (Submission.Diff.lcOf g) X F k) i
          = Work.Diff.GE.upd (Submission.Diff.lcOf g) X
              (Work.Diff.GE.upd (Submission.Diff.lcOf g) Y F i) k := by
        simp only [Work.Diff.GE.upd, h1, h2]
        exact Function.update_comm hki _ _ _
      rw [hupd]
    have hdiag := Work.Diff.GE.sum_univ_univ_sub_eq_diag
      (fun i k : Fin (j + 4) => ckt g j (Work.Diff.GE.upd (Submission.Diff.lcOf g) Y
        (Work.Diff.GE.upd (Submission.Diff.lcOf g) X F i) k) x)
      (fun i k : Fin (j + 4) => ckt g j (Work.Diff.GE.upd (Submission.Diff.lcOf g) X
        (Work.Diff.GE.upd (Submission.Diff.lcOf g) Y F i) k) x)
      (fun i k (hki : k ≠ i) => hoff i k hki)
    have hDsub : D - D'
        = (∑ i, ckt g j (Work.Diff.GE.upd (Submission.Diff.lcOf g) Y
              (Work.Diff.GE.upd (Submission.Diff.lcOf g) X F i) i) x)
          - (∑ i, ckt g j (Work.Diff.GE.upd (Submission.Diff.lcOf g) X
              (Work.Diff.GE.upd (Submission.Diff.lcOf g) Y F i) i) x) := by
      rw [hD, hD']
      simp only [← Finset.sum_sub_distrib]
      simp only [hdiag]
    have hper : ∀ i : Fin (j + 4),
        ckt g j (Work.Diff.GE.upd (Submission.Diff.lcOf g)
            (Work.Diff.GE.covAlong (Submission.Diff.lcOf g) X Y) F i) x
          - ckt g j (Work.Diff.GE.upd (Submission.Diff.lcOf g)
              (Work.Diff.GE.covAlong (Submission.Diff.lcOf g) Y X) F i) x
          + (ckt g j (Work.Diff.GE.upd (Submission.Diff.lcOf g) Y
                (Work.Diff.GE.upd (Submission.Diff.lcOf g) X F i) i) x
              - ckt g j (Work.Diff.GE.upd (Submission.Diff.lcOf g) X
                (Work.Diff.GE.upd (Submission.Diff.lcOf g) Y F i) i) x)
        = -ckt g j (Function.update F i
            (fun y => curv (Submission.Diff.lcOf g) X Y (F i) y)) x := by
      intro i
      have e1 : Work.Diff.GE.upd (Submission.Diff.lcOf g)
            (Work.Diff.GE.covAlong (Submission.Diff.lcOf g) X Y) F i
          = Function.update F i (Work.Diff.GE.covAlong (Submission.Diff.lcOf g)
              (Work.Diff.GE.covAlong (Submission.Diff.lcOf g) X Y) (F i)) := rfl
      have e2 : Work.Diff.GE.upd (Submission.Diff.lcOf g)
            (Work.Diff.GE.covAlong (Submission.Diff.lcOf g) Y X) F i
          = Function.update F i (Work.Diff.GE.covAlong (Submission.Diff.lcOf g)
              (Work.Diff.GE.covAlong (Submission.Diff.lcOf g) Y X) (F i)) := rfl
      have e3 : Work.Diff.GE.upd (Submission.Diff.lcOf g) Y
            (Work.Diff.GE.upd (Submission.Diff.lcOf g) X F i) i
          = Function.update F i (Work.Diff.GE.covAlong (Submission.Diff.lcOf g) Y
              (Work.Diff.GE.covAlong (Submission.Diff.lcOf g) X (F i))) := by
        simp only [Work.Diff.GE.upd, Function.update_self, Function.update_idem]
      have e4 : Work.Diff.GE.upd (Submission.Diff.lcOf g) X
            (Work.Diff.GE.upd (Submission.Diff.lcOf g) Y F i) i
          = Function.update F i (Work.Diff.GE.covAlong (Submission.Diff.lcOf g) X
              (Work.Diff.GE.covAlong (Submission.Diff.lcOf g) Y (F i))) := by
        simp only [Work.Diff.GE.upd, Function.update_self, Function.update_idem]
      rw [e1, e2, e3, e4]
      rw [ckt_update_comb (hLC) (g) (j) hF i
        (Work.Diff.GE.covAlong (Submission.Diff.lcOf g)
          (Work.Diff.GE.covAlong (Submission.Diff.lcOf g) X Y) (F i))
        (Work.Diff.GE.covAlong (Submission.Diff.lcOf g)
          (Work.Diff.GE.covAlong (Submission.Diff.lcOf g) Y X) (F i))
        (Work.Diff.GE.covAlong (Submission.Diff.lcOf g) Y
          (Work.Diff.GE.covAlong (Submission.Diff.lcOf g) X (F i)))
        (Work.Diff.GE.covAlong (Submission.Diff.lcOf g) X
          (Work.Diff.GE.covAlong (Submission.Diff.lcOf g) Y (F i)))
        (Work.Diff.GE.cmdiff_covAlong (Submission.Diff.lcOf g) hcov
          (Work.Diff.GE.cmdiff_covAlong (Submission.Diff.lcOf g) hcov hX hY) (hF i))
        (Work.Diff.GE.cmdiff_covAlong (Submission.Diff.lcOf g) hcov
          (Work.Diff.GE.cmdiff_covAlong (Submission.Diff.lcOf g) hcov hY hX) (hF i))
        (Work.Diff.GE.cmdiff_covAlong (Submission.Diff.lcOf g) hcov hY
          (Work.Diff.GE.cmdiff_covAlong (Submission.Diff.lcOf g) hcov hX (hF i)))
        (Work.Diff.GE.cmdiff_covAlong (Submission.Diff.lcOf g) hcov hX
          (Work.Diff.GE.cmdiff_covAlong (Submission.Diff.lcOf g) hcov hY (hF i))) x]
      rw [show Work.Diff.GE.covAlong (Submission.Diff.lcOf g)
              (Work.Diff.GE.covAlong (Submission.Diff.lcOf g) X Y) (F i)
            - Work.Diff.GE.covAlong (Submission.Diff.lcOf g)
              (Work.Diff.GE.covAlong (Submission.Diff.lcOf g) Y X) (F i)
            + Work.Diff.GE.covAlong (Submission.Diff.lcOf g) Y
              (Work.Diff.GE.covAlong (Submission.Diff.lcOf g) X (F i))
            - Work.Diff.GE.covAlong (Submission.Diff.lcOf g) X
              (Work.Diff.GE.covAlong (Submission.Diff.lcOf g) Y (F i))
          = -curv (Submission.Diff.lcOf g) X Y (F i) from
        Work.Diff.Evol.ricci_id_aux_covAlong_curv (Submission.Diff.lcOf g) htor hX hY]
      rw [show -curv (Submission.Diff.lcOf g) X Y (F i)
          = (-1 : ℝ) • curv (Submission.Diff.lcOf g) X Y (F i) from
        (neg_one_smul ℝ (curv (Submission.Diff.lcOf g) X Y (F i))).symm]
      rw [show ckt g j (Function.update F i
            ((-1 : ℝ) • curv (Submission.Diff.lcOf g) X Y (F i)))
          = ((-1 : ℝ) • ckt g j (Function.update F i
              (curv (Submission.Diff.lcOf g) X Y (F i)))) from
        TensProp_smul (hLC) (g) (k := j) (tensProp_all hLC g j) (F := F) hF (s := i) (-1)
          (X := curv (Submission.Diff.lcOf g) X Y (F i))
          (Work.Diff.GE.contMDiff_curv_fields (Submission.Diff.lcOf g) hcov hX hY (hF i))]
      simp only [Pi.smul_apply, smul_eq_mul, neg_one_mul]
    have hCD : (C - C') + (D - D') = -S := by
      rw [hC, hC', hDsub, hS]
      have hsplit : (∑ i, ckt g j (Work.Diff.GE.upd (Submission.Diff.lcOf g)
                (Work.Diff.GE.covAlong (Submission.Diff.lcOf g) X Y) F i) x)
            - (∑ i, ckt g j (Work.Diff.GE.upd (Submission.Diff.lcOf g)
                (Work.Diff.GE.covAlong (Submission.Diff.lcOf g) Y X) F i) x)
            + ((∑ i, ckt g j (Work.Diff.GE.upd (Submission.Diff.lcOf g) Y
                  (Work.Diff.GE.upd (Submission.Diff.lcOf g) X F i) i) x)
                - (∑ i, ckt g j (Work.Diff.GE.upd (Submission.Diff.lcOf g) X
                  (Work.Diff.GE.upd (Submission.Diff.lcOf g) Y F i) i) x))
          = ∑ i, (ckt g j (Work.Diff.GE.upd (Submission.Diff.lcOf g)
                (Work.Diff.GE.covAlong (Submission.Diff.lcOf g) X Y) F i) x
              - ckt g j (Work.Diff.GE.upd (Submission.Diff.lcOf g)
                (Work.Diff.GE.covAlong (Submission.Diff.lcOf g) Y X) F i) x
              + (ckt g j (Work.Diff.GE.upd (Submission.Diff.lcOf g) Y
                    (Work.Diff.GE.upd (Submission.Diff.lcOf g) X F i) i) x
                - ckt g j (Work.Diff.GE.upd (Submission.Diff.lcOf g) X
                    (Work.Diff.GE.upd (Submission.Diff.lcOf g) Y F i) i) x)) := by
        rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      rw [hsplit, Finset.sum_congr rfl (fun i _ => hper i), Finset.sum_neg_distrib]
    linarith [hAB, hCD]
  -- instantiate at `a`, `b`, `R`
  have h1 := hgen a b ha hb R hR
  rw [extDD_ckt g j x a b R, extDD_ckt g j x b a R] at h1
  exact h1


/-- The permutation of `Fin (m+2)` exchanging the first two indices (defined by cases). -/
noncomputable def swapFirstTwo (m : ℕ) : Equiv.Perm (Fin (m + 2)) where
  toFun := Fin.cases 1 (Fin.cases 0 (fun i : Fin m => i.succ.succ))
  invFun := Fin.cases 1 (Fin.cases 0 (fun i : Fin m => i.succ.succ))
  left_inv := by
    intro i
    induction i using Fin.cases with
    | zero => rfl
    | succ u =>
      induction u using Fin.cases with
      | zero => rfl
      | succ v => rfl
  right_inv := by
    intro i
    induction i using Fin.cases with
    | zero => rfl
    | succ u =>
      induction u using Fin.cases with
      | zero => rfl
      | succ v => rfl

/-- `swapFirstTwo` is an involution. -/
lemma swapFirstTwo_invol (m : ℕ) (i : Fin (m + 2)) :
    swapFirstTwo m (swapFirstTwo m i) = i :=
  (swapFirstTwo m).left_inv i

/-- Exchanging the first two slots, as a `cons` tuple. -/
lemma tupSw_swapFirstTwo {j : ℕ} (G : Fin (j + 6) → Tf) :
    Work.Diff.GE.tupSw (swapFirstTwo (j + 4)) G
      = consF (G 1) (consF (G 0) (fun i : Fin (j + 4) => G i.succ.succ)) := by
  funext q
  induction q using Fin.cases with
  | zero => rfl
  | succ u =>
    induction u using Fin.cases with
    | zero => rfl
    | succ v => rfl

/-- A `Fin (j+6)`-tuple is its first two entries followed by the tail. -/
lemma cons_cons_eta {j : ℕ} (G : Fin (j + 6) → Tf) :
    consF (G 0) (consF (G 1) (fun i : Fin (j + 4) => G i.succ.succ)) = G := by
  funext q
  induction q using Fin.cases with
  | zero => simp
  | succ u =>
    induction u using Fin.cases with
    | zero => simp
    | succ v => simp

/-- The curvature action on the level-`j` tower, as a field-level tensor of arity `j+6`. -/
noncomputable def curvActT (g : SMet I M) (j : ℕ) :
    (Fin (j + 6) → Tf) → M → ℝ :=
  fun G => fun y =>
    ∑ s : Fin (j + 4),
      ckt g j (Function.update (fun i : Fin (j + 4) => G i.succ.succ) s
        (fun z => curv (Submission.Diff.lcOf g) (G 0) (G 1) (G s.succ.succ) z)) y

/-- **The Ricci identity for the tower, in swap form.** -/
theorem ckt_sub_swap (hLC : Submission.Diff.LCSmooth I M) (g : SMet I M) (j : ℕ)
    {G : Fin (j + 6) → Tf} (hG : ∀ i, SmoothF (G i)) :
    ckt g (j + 2) G - ckt g (j + 2) (Work.Diff.GE.tupSw (swapFirstTwo (j + 4)) G)
      = -curvActT (I := I) (M := M) g j G := by
  funext y
  rw [Pi.sub_apply, Pi.neg_apply]
  rw [show ckt g (j + 2) G = ckt g (j + 2) (consF (G 0) (consF (G 1)
      (fun i : Fin (j + 4) => G i.succ.succ))) from by rw [cons_cons_eta],
    show Work.Diff.GE.tupSw (swapFirstTwo (j + 4)) G = consF (G 1) (consF (G 0)
      (fun i : Fin (j + 4) => G i.succ.succ)) from tupSw_swapFirstTwo G]
  have h1 := ckt_ricci hLC g j y (G 0) (G 1) (hG 0) (hG 1)
      (fun i : Fin (j + 4) => G i.succ.succ) (fun i => hG i.succ.succ)
  rw [h1]
  rfl

/-- **(S2)**: the `∇³`-difference with the 2nd and 3rd slots exchanged is the derivative of the
curvature action. -/
theorem ckt_swap23 (hLC : Submission.Diff.LCSmooth I M) (g : SMet I M) (j : ℕ) (x : M)
    (e X : Tf) (he : SmoothF e) (hX : SmoothF X)
    (F : Fin (j + 4) → Tf) (hF : ∀ i, SmoothF (F i)) :
    ckt g (j + 3) (consF e (consF e (consF X F))) x
      - ckt g (j + 3) (consF e (consF X (consF e F))) x
      = - Work.Diff.GE.extD (Submission.Diff.lcOf g) (curvActT (I := I) (M := M) g j) x e
          (consF e (consF X F)) := by
  obtain ⟨hcov⟩ := (hLC g).1
  have hpt : ∀ G : Fin (j + 6) → Tf, Work.Diff.GE.SmoothTuple (I := I) (M := M) G →
      ckt g (j + 2) G - ckt g (j + 2) (Work.Diff.GE.tupSw (swapFirstTwo (j + 4)) G)
        = -curvActT (I := I) (M := M) g j G :=
    fun G hG => ckt_sub_swap hLC g j hG
  have hFsm : Work.Diff.GE.SmoothTuple (I := I) (M := M) (consF e (consF X F)) :=
    smoothF_cons he (smoothF_cons hX hF)
  have hgen := Work.Diff.GE.extD_sub_swap (I := I) (M := M) (swapFirstTwo (j + 4))
    (swapFirstTwo_invol (j + 4))
    (Submission.Diff.lcOf g) hcov (ckt g (j + 2)) (curvActT (I := I) (M := M) g j)
    (fun G hG => (tensProp_all hLC g (j + 2) G hG).1) hpt x e he (consF e (consF X F)) hFsm
  rw [extD_ckt, extD_ckt] at hgen
  rw [show Work.Diff.GE.tupSw (swapFirstTwo (j + 4)) (consF e (consF X F))
      = consF X (consF e F) from tupSw_swapFirstTwo _] at hgen
  exact hgen


/-- **The product rule for the curvature-inserted tower.** -/
theorem curvActT_deriv (hLC : Submission.Diff.LCSmooth I M) (g : SMet I M) (j : ℕ) (x : M)
    (e : Tf) (he : SmoothF e) (G : Fin (j + 6) → Tf) (hG : ∀ i, SmoothF (G i)) :
    Work.Diff.GE.extD (Submission.Diff.lcOf g) (curvActT (I := I) (M := M) g j) x e G
      = (∑ s : Fin (j + 4), ckt g (j + 1) (consF e (Function.update (fun i : Fin (j + 4) =>
            G i.succ.succ) s (fun z => curv (Submission.Diff.lcOf g) (G 0) (G 1)
              (G s.succ.succ) z))) x)
        + (∑ s : Fin (j + 4), ckt g j (Function.update (Function.update (fun i : Fin (j + 4) =>
            G i.succ.succ) s (fun z => curv (Submission.Diff.lcOf g) (G 0) (G 1)
              (G s.succ.succ) z)) s
            (Work.Diff.EXT.dCurvV (Submission.Diff.lcOf g) e (G 0) (G 1) (G s.succ.succ))) x) := by
  obtain ⟨hcov⟩ := (hLC g).1
  -- abbreviations
  set TL : Fin (j + 4) → Tf := fun i => G i.succ.succ with hTL
  set Cs : Fin (j + 4) → Tf := fun s => (fun y => curv (Submission.Diff.lcOf g) (G 0) (G 1)
    (TL s) y) with hCs
  set Tp : Fin (j + 4) → (Fin (j + 4) → Tf) := fun s => Function.update TL s (Cs s) with hTp
  have hTLsm : ∀ i, SmoothF (TL i) := fun i => hG i.succ.succ
  have hCssm : ∀ s, SmoothF (Cs s) := fun s => Work.Diff.GE.contMDiff_curv_fields
    (Submission.Diff.lcOf g) hcov (hG 0) (hG 1) (hTLsm s)
  have hTpsm : ∀ s, ∀ i, SmoothF (Tp s i) := fun s i => smoothF_update hTLsm (hCssm s) i
  -- `curvActT` in terms of `Tp`
  have hcurvAct : curvActT (I := I) (M := M) g j G = (fun y => ∑ s, ckt g j (Tp s) y) := by
    funext y
    rw [hTp, hCs, hTL]
    rfl
  rw [Work.Diff.GE.extD_eq, hcurvAct]
  -- the derivative
  have hder : mvfderiv I (fun y : M => ∑ s, ckt g j (Tp s) y) x (e x)
      = ∑ s, (ckt g (j + 1) (consF e (Tp s)) x
          + ∑ i : Fin (j + 4), ckt g j (Function.update (Tp s) i
              (dirF g ((Tp s) i) e)) x) := by
    rw [Work.Diff.GE.Kato3.mvfderiv_sum Finset.univ
      (fun s : Fin (j + 4) => fun y : M => ckt g j (Tp s) y)
      (fun s => (tensProp_all hLC g j (Tp s) (hTpsm s)).1) x (e x)]
    exact Finset.sum_congr rfl fun s _ => mvfderiv_ckt_gen' g j (Tp s) e x
  rw [hder]
  -- the corrections
  have hcorr : (∑ q : Fin (j + 6), curvActT (I := I) (M := M) g j
        (Work.Diff.GE.upd (Submission.Diff.lcOf g) e G q) x)
      = ∑ q : Fin (j + 6), ∑ s : Fin (j + 4), ckt g j
          (Function.update (fun i : Fin (j + 4) =>
              (Work.Diff.GE.upd (Submission.Diff.lcOf g) e G q) i.succ.succ) s
            (fun z => curv (Submission.Diff.lcOf g)
              ((Work.Diff.GE.upd (Submission.Diff.lcOf g) e G q) 0)
              ((Work.Diff.GE.upd (Submission.Diff.lcOf g) e G q) 1)
              ((Work.Diff.GE.upd (Submission.Diff.lcOf g) e G q) s.succ.succ) z)) x := by
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [show curvActT (I := I) (M := M) g j (Work.Diff.GE.upd (Submission.Diff.lcOf g) e G q)
        = (fun y : M => ∑ s, ckt g j (Function.update (fun i : Fin (j + 4) =>
            (Work.Diff.GE.upd (Submission.Diff.lcOf g) e G q) i.succ.succ) s
              (fun z => curv (Submission.Diff.lcOf g)
                ((Work.Diff.GE.upd (Submission.Diff.lcOf g) e G q) 0)
                ((Work.Diff.GE.upd (Submission.Diff.lcOf g) e G q) 1)
                ((Work.Diff.GE.upd (Submission.Diff.lcOf g) e G q) s.succ.succ) z)) y) from rfl]
  rw [hcorr, Finset.sum_comm]
  rw [Finset.sum_add_distrib]
  -- `upd` is the slotwise Leibniz update
  have hupd : ∀ q : Fin (j + 6), Work.Diff.GE.upd (Submission.Diff.lcOf g) e G q
      = Function.update G q (dirF g (G q) e) := fun q => rfl
  simp only [hupd]
  -- termwise, the single-slot insertion identity
  have hsum : (∑ s : Fin (j + 4), ∑ i : Fin (j + 4), ckt g j (Function.update (Tp s) i
        (dirF g ((Tp s) i) e)) x)
      - (∑ s : Fin (j + 4), ∑ q : Fin (j + 6), ckt g j
          (Function.update (fun i : Fin (j + 4) =>
              (Function.update G q (dirF g (G q) e)) i.succ.succ) s
            (fun z => curv (Submission.Diff.lcOf g)
              ((Function.update G q (dirF g (G q) e)) 0)
              ((Function.update G q (dirF g (G q) e)) 1)
              ((Function.update G q (dirF g (G q) e)) s.succ.succ) z)) x)
      = ∑ s : Fin (j + 4), ckt g j
          (Function.update (Function.update (fun i : Fin (j + 4) => G i.succ.succ) s
              (fun z => curv (Submission.Diff.lcOf g) (G 0) (G 1) (G s.succ.succ) z)) s
            (Work.Diff.EXT.dCurvV (Submission.Diff.lcOf g) e (G 0) (G 1) (G s.succ.succ))) x := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    have h := lapCommInsT (I := I) (M := M) hLC g j x e he G hG s
    rw [hTp, hCs, hTL]
    simpa only [hupd] using h
  have hAsum : (∑ s : Fin (j + 4), ckt g (j + 1) (consF e (Tp s)) x)
      = ∑ s : Fin (j + 4), ckt g (j + 1)
          (consF e (Function.update (fun i : Fin (j + 4) => G i.succ.succ) s
            (fun z => curv (Submission.Diff.lcOf g) (G 0) (G 1) (G s.succ.succ) z))) x := by
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hTp, hCs, hTL]
  linarith [hsum, hAsum]

/-! ## Norm bounds: the tower, the curvature vector, and the corrected insertions -/

/-- The metric norm `|v| = √(g.inner x v v)`. -/
noncomputable abbrev gNrm (g : SMet I M) (x : M) (v : TangentSpace I x) : ℝ := Real.sqrt (g.inner x v v)

theorem gNrm_nonneg (g : SMet I M) (x : M) (v : TangentSpace I x) : 0 ≤ gNrm g x v :=
  Real.sqrt_nonneg _

theorem gNrm_eq_nrm (g : SMet I M) (x : M) (v : TangentSpace I x) :
    gNrm g x v = Work.Diff.GE.EvolB.nrm g x v := rfl

theorem inner_self_nonneg_lap (g : SMet I M) (x : M) (v : TangentSpace I x) :
    0 ≤ g.inner x v v := Work.Diff.GE.EvolB.inner_self_nonneg_B g x v

theorem sqrt_mul4_lap {p q r s : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    Real.sqrt (p * q * r * s) = Real.sqrt p * Real.sqrt q * Real.sqrt r * Real.sqrt s := by
  rw [Real.sqrt_mul (mul_nonneg (mul_nonneg hp hq) hr), Real.sqrt_mul (mul_nonneg hp hq),
    Real.sqrt_mul hp]

theorem curvNormK_nonneg_lap (g : SMet I M) (x : M) (j : ℕ) : 0 ≤ curvNormK g x j := by
  simp only [curvNormK]
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **Product estimate for a one-slot update.** If `ψ` differs from `φ` only at `i`, where
`ψ i ≤ B * φ i`, then `∏ ψ ≤ B * ∏ φ`. -/
theorem prod_update_le {N : ℕ} (φ ψ : Fin N → ℝ) (i : Fin N) (B : ℝ)
    (hφ : ∀ r, 0 ≤ φ r) (hψφ : ∀ r, r ≠ i → ψ r = φ r) (hi : ψ i ≤ B * φ i) :
    ∏ r, ψ r ≤ B * ∏ r, φ r := by
  have h1 : ∏ r, ψ r = ψ i * ∏ r ∈ Finset.univ.erase i, ψ r :=
    (Finset.mul_prod_erase Finset.univ ψ (Finset.mem_univ i)).symm
  have h2 : ∏ r ∈ Finset.univ.erase i, ψ r = ∏ r ∈ Finset.univ.erase i, φ r :=
    Finset.prod_congr rfl fun r hr => hψφ r (Finset.mem_erase.mp hr).1
  have h3 : ∏ r, φ r = φ i * ∏ r ∈ Finset.univ.erase i, φ r :=
    (Finset.mul_prod_erase Finset.univ φ (Finset.mem_univ i)).symm
  rw [h1, h2, h3]
  calc ψ i * ∏ r ∈ Finset.univ.erase i, φ r ≤ (B * φ i) * ∏ r ∈ Finset.univ.erase i, φ r :=
        mul_le_mul_of_nonneg_right hi (Finset.prod_nonneg fun r _ => hφ r)
    _ = B * (φ i * ∏ r ∈ Finset.univ.erase i, φ r) := by ring

/-- **Tower bound.**  The value of `∇^j Rm` at `x` on a smooth tuple is bounded by the Frobenius
norm `√(curvNormK g x j)` times the product of the metric norms of the values. -/
theorem ckt_norm_le (hLC : Submission.Diff.LCSmooth I M) (g : SMet I M) (x : M) (j : ℕ)
    (F : Fin (j + 4) → Tf) (hF : ∀ i, SmoothF (F i)) :
    |ckt g j F x| ≤ Real.sqrt (curvNormK g x j) * ∏ r : Fin (j + 4), gNrm g x (F r x) := by
  rw [ckt_eq_Kpt' hLC g j x hF]
  exact Kpt_norm_bound hLC g x j (fun r => F r x)

/-- **Curvature vector bound (sharp).** -/
theorem gNrm_rmVec_le (hLC : Submission.Diff.LCSmooth I M) (g : SMet I M) (x : M)
    (u w z : TangentSpace I x) :
    gNrm g x (rmVec (lcOf g) x u w z)
      ≤ Real.sqrt (curvNormK g x 0) * gNrm g x u * gNrm g x w * gNrm g x z := by
  have hsq := Work.Diff.GE.rmVec_sq_le_sharp' (I := I) (M := M) hLC g x u w z
  rw [← Work.Diff.EXT.curvNormK_zero_eq_rmNormSq (I := I) (M := M) g x] at hsq
  refine le_trans (Real.sqrt_le_sqrt hsq) ?_
  rw [show Real.sqrt (curvNormK g x 0 * (g.inner x u u) * (g.inner x w w) * (g.inner x z z))
      = Real.sqrt (curvNormK g x 0) * gNrm g x u * gNrm g x w * gNrm g x z from
    sqrt_mul4_lap (curvNormK_nonneg_lap g x 0) (inner_self_nonneg_lap g x u)
      (inner_self_nonneg_lap g x w) (inner_self_nonneg_lap g x z)]

/-- **Curvature vector bound for smooth fields.** -/
theorem gNrm_curv_le (hLC : Submission.Diff.LCSmooth I M) (g : SMet I M) (x : M)
    {A B U : Tf} (hA : SmoothF A) (hB : SmoothF B) (hU : SmoothF U) :
    gNrm g x (curv (lcOf g) A B U x)
      ≤ Real.sqrt (curvNormK g x 0) * gNrm g x (A x) * gNrm g x (B x) * gNrm g x (U x) := by
  rw [Work.Diff.GE.curv_section_apply_eq_rmVec (I := I) (M := M) hLC g hA hB hU x]
  exact gNrm_rmVec_le hLC g x (A x) (B x) (U x)

/-- **Insertion bound for the curvature field.**  Replacing the `i`-th field of a smooth tuple by
the curvature field `z ↦ R(A,B)(F i)(z)` costs a factor `√(curvNormK g x 0) |A| |B|`. -/
theorem ckt_update_curv_le (hLC : Submission.Diff.LCSmooth I M) (g : SMet I M) (x : M) (j : ℕ)
    (F : Fin (j + 4) → Tf) (hF : ∀ r, SmoothF (F r)) (i : Fin (j + 4))
    {A B : Tf} (hA : SmoothF A) (hB : SmoothF B) :
    |ckt g j (Function.update F i (fun z => curv (Submission.Diff.lcOf g) A B (F i) z)) x|
      ≤ Real.sqrt (curvNormK g x 0) * Real.sqrt (curvNormK g x j)
        * (gNrm g x (A x) * gNrm g x (B x) * ∏ r : Fin (j + 4), gNrm g x (F r x)) := by
  obtain ⟨hcov⟩ := (hLC g).1
  have hV : SmoothF (fun z => curv (Submission.Diff.lcOf g) A B (F i) z) :=
    Work.Diff.GE.contMDiff_curv_fields (Submission.Diff.lcOf g) hcov hA hB (hF i)
  have hsm : ∀ q, SmoothF ((Function.update F i (fun z => curv (Submission.Diff.lcOf g) A B
      (F i) z)) q) := smoothF_update (G := F) hF (j := i) hV
  have hb := ckt_norm_le hLC g x j
    (Function.update F i (fun z => curv (Submission.Diff.lcOf g) A B (F i) z)) hsm
  have hval : gNrm g x ((Function.update F i (fun z => curv (Submission.Diff.lcOf g) A B
      (F i) z)) i x)
      ≤ (Real.sqrt (curvNormK g x 0) * gNrm g x (A x) * gNrm g x (B x)) * gNrm g x (F i x) := by
    rw [Function.update_self]
    calc gNrm g x (curv (Submission.Diff.lcOf g) A B (F i) x)
        ≤ Real.sqrt (curvNormK g x 0) * gNrm g x (A x) * gNrm g x (B x) * gNrm g x (F i x) :=
          gNrm_curv_le hLC g x hA hB (hF i)
      _ = (Real.sqrt (curvNormK g x 0) * gNrm g x (A x) * gNrm g x (B x)) * gNrm g x (F i x) := by
          ring
  have hoff : ∀ r, r ≠ i → gNrm g x ((Function.update F i (fun z => curv (Submission.Diff.lcOf g)
      A B (F i) z)) r x) = gNrm g x (F r x) := by
    intro r hr
    rw [Function.update_of_ne hr]
  have hprodb := prod_update_le (φ := fun r => gNrm g x (F r x))
    (ψ := fun r => gNrm g x ((Function.update F i (fun z => curv (Submission.Diff.lcOf g) A B
      (F i) z)) r x)) i (Real.sqrt (curvNormK g x 0) * gNrm g x (A x) * gNrm g x (B x))
    (fun r => gNrm_nonneg g x (F r x)) hoff hval
  calc |ckt g j (Function.update F i (fun z => curv (Submission.Diff.lcOf g) A B (F i) z)) x|
      ≤ Real.sqrt (curvNormK g x j) * ∏ r : Fin (j + 4), gNrm g x
          ((Function.update F i (fun z => curv (Submission.Diff.lcOf g) A B (F i) z)) r x) := hb
    _ ≤ Real.sqrt (curvNormK g x j)
          * ((Real.sqrt (curvNormK g x 0) * gNrm g x (A x) * gNrm g x (B x))
              * ∏ r : Fin (j + 4), gNrm g x (F r x)) :=
        mul_le_mul_of_nonneg_left hprodb (Real.sqrt_nonneg _)
    _ = Real.sqrt (curvNormK g x 0) * Real.sqrt (curvNormK g x j)
          * (gNrm g x (A x) * gNrm g x (B x) * ∏ r : Fin (j + 4), gNrm g x (F r x)) := by ring

/-- **Insertion bound for the `∇Rm`-corrected field `dCurvV`** (with the pointwise norm bound of the
inserted vector as a hypothesis). -/
theorem ckt_update_dcurv_le (hLC : Submission.Diff.LCSmooth I M) (g : SMet I M) (x : M) (j : ℕ)
    (F : Fin (j + 4) → Tf) (hF : ∀ r, SmoothF (F r)) (i : Fin (j + 4))
    {Z A B : Tf} (hZ : SmoothF Z) (hA : SmoothF A) (hB : SmoothF B) (C : ℝ)
    (hd : SmoothF (Work.Diff.EXT.dCurvV (Submission.Diff.lcOf g) Z A B (F i)))
    (hbd : gNrm g x (Work.Diff.EXT.dCurvV (Submission.Diff.lcOf g) Z A B (F i) x)
      ≤ C * Real.sqrt (curvNormK g x 1) * (gNrm g x (Z x) * gNrm g x (A x) * gNrm g x (B x)
          * gNrm g x (F i x))) :
    |ckt g j (Function.update F i (Work.Diff.EXT.dCurvV (Submission.Diff.lcOf g) Z A B (F i))) x|
      ≤ C * Real.sqrt (curvNormK g x 1) * Real.sqrt (curvNormK g x j)
        * (gNrm g x (Z x) * gNrm g x (A x) * gNrm g x (B x)
            * ∏ r : Fin (j + 4), gNrm g x (F r x)) := by
  have hsm : ∀ q, SmoothF ((Function.update F i (Work.Diff.EXT.dCurvV
      (Submission.Diff.lcOf g) Z A B (F i))) q) := smoothF_update (G := F) hF (j := i) hd
  have hb := ckt_norm_le hLC g x j
    (Function.update F i (Work.Diff.EXT.dCurvV (Submission.Diff.lcOf g) Z A B (F i))) hsm
  have hval : gNrm g x ((Function.update F i (Work.Diff.EXT.dCurvV (Submission.Diff.lcOf g)
      Z A B (F i))) i x)
      ≤ (C * Real.sqrt (curvNormK g x 1) * (gNrm g x (Z x) * gNrm g x (A x) * gNrm g x (B x)))
        * gNrm g x (F i x) := by
    rw [Function.update_self]
    calc gNrm g x (Work.Diff.EXT.dCurvV (Submission.Diff.lcOf g) Z A B (F i) x)
        ≤ C * Real.sqrt (curvNormK g x 1) * (gNrm g x (Z x) * gNrm g x (A x) * gNrm g x (B x)
            * gNrm g x (F i x)) := hbd
      _ = (C * Real.sqrt (curvNormK g x 1) * (gNrm g x (Z x) * gNrm g x (A x) * gNrm g x (B x)))
        * gNrm g x (F i x) := by ring
  have hoff : ∀ r, r ≠ i → gNrm g x ((Function.update F i (Work.Diff.EXT.dCurvV
      (Submission.Diff.lcOf g) Z A B (F i))) r x) = gNrm g x (F r x) := by
    intro r hr
    rw [Function.update_of_ne hr]
  have hprodb := prod_update_le (φ := fun r => gNrm g x (F r x))
    (ψ := fun r => gNrm g x ((Function.update F i (Work.Diff.EXT.dCurvV
      (Submission.Diff.lcOf g) Z A B (F i))) r x)) i
    (C * Real.sqrt (curvNormK g x 1) * (gNrm g x (Z x) * gNrm g x (A x) * gNrm g x (B x)))
    (fun r => gNrm_nonneg g x (F r x)) hoff hval
  calc |ckt g j (Function.update F i (Work.Diff.EXT.dCurvV (Submission.Diff.lcOf g)
        Z A B (F i))) x|
      ≤ Real.sqrt (curvNormK g x j) * ∏ r : Fin (j + 4), gNrm g x
          ((Function.update F i (Work.Diff.EXT.dCurvV (Submission.Diff.lcOf g)
            Z A B (F i))) r x) := hb
    _ ≤ Real.sqrt (curvNormK g x j)
          * ((C * Real.sqrt (curvNormK g x 1)
              * (gNrm g x (Z x) * gNrm g x (A x) * gNrm g x (B x)))
              * ∏ r : Fin (j + 4), gNrm g x (F r x)) :=
        mul_le_mul_of_nonneg_left hprodb (Real.sqrt_nonneg _)
    _ = C * Real.sqrt (curvNormK g x 1) * Real.sqrt (curvNormK g x j)
          * (gNrm g x (Z x) * gNrm g x (A x) * gNrm g x (B x)
              * ∏ r : Fin (j + 4), gNrm g x (F r x)) := by ring

/-- **The value of `gNrm` on the `Fin.cons` of a tuple.** -/
theorem gNrm_prod_cons {N : ℕ} (g : SMet I M) (x : M) (A : Tf) (F : Fin N → Tf) :
    ∏ r : Fin (N + 1), gNrm g x ((consF A F) r x)
      = gNrm g x (A x) * ∏ r : Fin N, gNrm g x (F r x) := by
  rw [Fin.prod_univ_succ]
  rfl

/-- A `g`-orthonormal family at `x` has unit norms. -/
theorem gNrm_eq_one_of_isONFrame (g : SMet I M) (x : M)
    {e : Fin (Module.finrank ℝ E) → TangentSpace I x} (he : Submission.Diff.IsONFrame g x e)
    (m : Fin (Module.finrank ℝ E)) : gNrm g x (e m) = 1 := by
  rw [gNrm, he m m, if_pos rfl, Real.sqrt_one]

/-- **The target's product factor**, in the split form used in the assembly. -/
theorem prod_split (g : SMet I M) (x : M) (k : ℕ) (G : Fin (k + 5) → Tf) :
    ∏ r : Fin (k + 5), gNrm g x (G r x)
      = gNrm g x (G 0 x) * ∏ r : Fin (k + 4), gNrm g x (G r.succ x) := by
  rw [Fin.prod_univ_succ]

/-- Arithmetic assembly of the three bounded families of sums. -/
theorem bound_of_sum_bounds {S1 S2 S3 Y0 Y1 Yk P C : ℝ} (hC : 1 ≤ C)
    (hS1 : S1 ≤ Y0 * Yk * P) (hS2 : S2 ≤ C * Y1 * Yk * P) (hS3 : S3 ≤ Y0 * Yk * P)
    (hP : 0 ≤ P) (hY0 : 0 ≤ Y0) (hY1 : 0 ≤ Y1) (hYk : 0 ≤ Yk) :
    S1 + S2 + S3 ≤ (2 * C) * (Y0 * Yk + Y1 * Yk) * P := by
  have h0 : 0 ≤ Y0 * Yk * P := mul_nonneg (mul_nonneg hY0 hYk) hP
  have h1 : 0 ≤ Y1 * Yk * P := mul_nonneg (mul_nonneg hY1 hYk) hP
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  have hsum : S1 + S2 + S3 ≤ Y0 * Yk * P + C * Y1 * Yk * P + Y0 * Yk * P := by linarith
  have ha : Y0 * Yk * P ≤ C * (Y0 * Yk) * P := by
    have h := mul_le_mul_of_nonneg_right hC h0
    rw [one_mul] at h
    rwa [(mul_assoc C (Y0 * Yk) P).symm] at h
  have hb : C * Y1 * Yk * P ≤ 2 * C * (Y1 * Yk) * P := by
    have h : 0 ≤ C * (Y1 * Yk * P) := mul_nonneg hC0 h1
    nlinarith [h]
  have htarget : Y0 * Yk * P + C * Y1 * Yk * P + Y0 * Yk * P
      ≤ (2 * C) * (Y0 * Yk + Y1 * Yk) * P := by
    have e : (2 * C) * (Y0 * Yk + Y1 * Yk) * P
        = 2 * C * (Y0 * Yk) * P + 2 * C * (Y1 * Yk) * P := by ring
    rw [e]
    linarith
  linarith

/-! ## Smoothness of the `∇Rm` insertion, and the decomposition of the commutator -/

/-- Smoothness of the `∇Rm`-corrected insertion field `dCurvV`. -/
theorem smoothF_dCurvV (hLC : Submission.Diff.LCSmooth I M) (g : SMet I M)
    {Z A B U : Tf} (hZ : SmoothF Z) (hA : SmoothF A) (hB : SmoothF B) (hU : SmoothF U) :
    SmoothF (Work.Diff.EXT.dCurvV (Submission.Diff.lcOf g) Z A B U) := by
  obtain ⟨hcov⟩ := (hLC g).1
  have hc : SmoothF (fun y => curv (Submission.Diff.lcOf g) A B U y) :=
    Work.Diff.GE.contMDiff_curv_fields (Submission.Diff.lcOf g) hcov hA hB hU
  have h1 : SmoothF (fun y => (Submission.Diff.lcOf g)
      (fun y => curv (Submission.Diff.lcOf g) A B U y) y (Z y)) :=
    Work.Diff.GE.cmdiff_covAlong (Submission.Diff.lcOf g) hcov hZ hc
  have h2 : SmoothF (fun y => curv (Submission.Diff.lcOf g)
      (fun z => (Submission.Diff.lcOf g) A z (Z z)) B U y) :=
    Work.Diff.GE.contMDiff_curv_fields (Submission.Diff.lcOf g) hcov
      (Work.Diff.GE.cmdiff_covAlong (Submission.Diff.lcOf g) hcov hZ hA) hB hU
  have h3 : SmoothF (fun y => curv (Submission.Diff.lcOf g) A
      (fun z => (Submission.Diff.lcOf g) B z (Z z)) U y) :=
    Work.Diff.GE.contMDiff_curv_fields (Submission.Diff.lcOf g) hcov hA
      (Work.Diff.GE.cmdiff_covAlong (Submission.Diff.lcOf g) hcov hZ hB) hU
  have h4 : SmoothF (fun y => curv (Submission.Diff.lcOf g) A B
      (fun z => (Submission.Diff.lcOf g) U z (Z z)) y) :=
    Work.Diff.GE.contMDiff_curv_fields (Submission.Diff.lcOf g) hcov hA hB
      (Work.Diff.GE.cmdiff_covAlong (Submission.Diff.lcOf g) hcov hZ hU)
  have hfun : Work.Diff.EXT.dCurvV (Submission.Diff.lcOf g) Z A B U
      = (fun y => (Submission.Diff.lcOf g) (fun y => curv (Submission.Diff.lcOf g) A B U y)
            y (Z y))
        - (fun y => curv (Submission.Diff.lcOf g)
            (fun z => (Submission.Diff.lcOf g) A z (Z z)) B U y)
        - (fun y => curv (Submission.Diff.lcOf g) A
            (fun z => (Submission.Diff.lcOf g) B z (Z z)) U y)
        - (fun y => curv (Submission.Diff.lcOf g) A B
            (fun z => (Submission.Diff.lcOf g) U z (Z z)) y) := rfl
  rw [hfun]
  exact smoothF_sub' (smoothF_sub' (smoothF_sub' h1 h2) h3) h4

/-- A tuple is its first entry followed by its tail. -/
lemma cons_eta_tail {N : ℕ} (G : Fin (N + 1) → Tf) :
    consF (G 0) (fun i : Fin N => G i.succ) = G := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rw [Fin.cons_zero]
  · intro j
    rw [Fin.cons_succ]

/-- **The Weitzenböck decomposition of the commutator**: split at the middle tuple `(A, X, A, T)`.
The first bracket is the `(S2)` identity (the derivative of the curvature action) and the second is
the Ricci identity `(S1)` for the two derivative slots. -/
theorem lapComm_decomp (hLC : Submission.Diff.LCSmooth I M) (g : SMet I M) (k : ℕ) (x : M)
    (Ef : Fin (Module.finrank ℝ E) → Tf) (hEf : ∀ i, SmoothF (Ef i))
    (G : Fin (k + 5) → Tf) (hG : ∀ i, SmoothF (G i)) :
    (∑ m : Fin (Module.finrank ℝ E), ckt g (k + 3) (consF (Ef m) (consF (Ef m) G)) x)
      - (∑ m : Fin (Module.finrank ℝ E), ckt g (k + 3) (consF (G 0) (consF (Ef m)
          (consF (Ef m) (fun i : Fin (k + 4) => G i.succ)))) x)
    = - (∑ m : Fin (Module.finrank ℝ E),
          Work.Diff.GE.extD (Submission.Diff.lcOf g) (curvActT g k) x (Ef m) (consF (Ef m) G))
      - (∑ m : Fin (Module.finrank ℝ E), ∑ s : Fin (k + 5), ckt g (k + 1)
          (Function.update (consF (Ef m) (fun i : Fin (k + 4) => G i.succ)) s
            (fun z => curv (Submission.Diff.lcOf g) (Ef m) (G 0)
              ((consF (Ef m) (fun i : Fin (k + 4) => G i.succ)) s) z)) x) := by
  have hper : ∀ m : Fin (Module.finrank ℝ E),
      ckt g (k + 3) (consF (Ef m) (consF (Ef m) G)) x
        - ckt g (k + 3) (consF (G 0) (consF (Ef m) (consF (Ef m)
            (fun i : Fin (k + 4) => G i.succ)))) x
      = - Work.Diff.GE.extD (Submission.Diff.lcOf g) (curvActT g k) x (Ef m) (consF (Ef m) G)
        - ∑ s : Fin (k + 5), ckt g (k + 1)
            (Function.update (consF (Ef m) (fun i : Fin (k + 4) => G i.succ)) s
              (fun z => curv (Submission.Diff.lcOf g) (Ef m) (G 0)
                ((consF (Ef m) (fun i : Fin (k + 4) => G i.succ)) s) z)) x := by
    intro m
    have hT : ∀ i : Fin (k + 4), SmoothF ((fun i : Fin (k + 4) => G i.succ) i) :=
      fun i => hG i.succ
    have hAT : ∀ i, SmoothF ((consF (Ef m) (fun i : Fin (k + 4) => G i.succ)) i) :=
      smoothF_cons (hEf m) hT
    have het : consF (Ef m) (consF (G 0) (fun i : Fin (k + 4) => G i.succ))
        = consF (Ef m) G := by
      rw [cons_eta_tail (G := G)]
    have hsplit : ckt g (k + 3) (consF (Ef m) (consF (Ef m) G)) x
        - ckt g (k + 3) (consF (G 0) (consF (Ef m) (consF (Ef m)
            (fun i : Fin (k + 4) => G i.succ)))) x
        = (ckt g (k + 3) (consF (Ef m) (consF (Ef m) (consF (G 0)
              (fun i : Fin (k + 4) => G i.succ)))) x
            - ckt g (k + 3) (consF (Ef m) (consF (G 0) (consF (Ef m)
              (fun i : Fin (k + 4) => G i.succ)))) x)
          + (ckt g (k + 3) (consF (Ef m) (consF (G 0) (consF (Ef m)
              (fun i : Fin (k + 4) => G i.succ)))) x
            - ckt g (k + 3) (consF (G 0) (consF (Ef m) (consF (Ef m)
              (fun i : Fin (k + 4) => G i.succ)))) x) := by
      rw [show consF (Ef m) (consF (Ef m) G)
          = consF (Ef m) (consF (Ef m) (consF (G 0) (fun i : Fin (k + 4) => G i.succ)))
          from by rw [cons_eta_tail (G := G)]]
      ring
    rw [hsplit]
    have hb1 := ckt_swap23 hLC g k x (Ef m) (G 0) (hEf m) (hG 0)
      (fun i : Fin (k + 4) => G i.succ) hT
    have hb2 := ckt_ricci hLC g (k + 1) x (Ef m) (G 0) (hEf m) (hG 0)
      (consF (Ef m) (fun i : Fin (k + 4) => G i.succ)) hAT
    rw [hb1, hb2, ← het]
    ring
  rw [← Finset.sum_sub_distrib]
  calc (∑ m, (ckt g (k + 3) (consF (Ef m) (consF (Ef m) G)) x
        - ckt g (k + 3) (consF (G 0) (consF (Ef m) (consF (Ef m)
            (fun i : Fin (k + 4) => G i.succ)))) x))
      = ∑ m, (- Work.Diff.GE.extD (Submission.Diff.lcOf g) (curvActT g k) x (Ef m)
          (consF (Ef m) G)
          - ∑ s : Fin (k + 5), ckt g (k + 1)
              (Function.update (consF (Ef m) (fun i : Fin (k + 4) => G i.succ)) s
                (fun z => curv (Submission.Diff.lcOf g) (Ef m) (G 0)
                  ((consF (Ef m) (fun i : Fin (k + 4) => G i.succ)) s) z)) x) :=
        Finset.sum_congr rfl fun m _ => hper m
    _ = - (∑ m, Work.Diff.GE.extD (Submission.Diff.lcOf g) (curvActT g k) x (Ef m)
            (consF (Ef m) G))
        - ∑ m, ∑ s : Fin (k + 5), ckt g (k + 1)
            (Function.update (consF (Ef m) (fun i : Fin (k + 4) => G i.succ)) s
              (fun z => curv (Submission.Diff.lcOf g) (Ef m) (G 0)
                ((consF (Ef m) (fun i : Fin (k + 4) => G i.succ)) s) z)) x := by
        rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]

end

/-! ## Assembly of the main theorem

The target is stated outside the `variable` scope of this file so that its statement carries the
explicit binders of the request verbatim. -/

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

abbrev TfPack {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    {N : ℕ} (X : Work.Diff.EXT.TField (I := I) (M := M))
    (F : Fin N → Work.Diff.EXT.TField (I := I) (M := M)) :
    Fin (N + 1) → Work.Diff.EXT.TField (I := I) (M := M) := Fin.cons X F

local notation "consF" X:max F:max => TfPack X F

/-- **The Weitzenböck commutator `[Δ, ∇]` for the curvature tower** (part (C) of the `k`-th order Shi estimate; the only missing input of the reaction-ladder step besides the proved `Work.Diff.EXT.ckt_step_tderiv` and `Work.Diff.EXT.connVar_bound`).

With `τ := ckt g k = ∇^k Rm` and `Ef` a family of fields which is `g`-orthonormal near `x` (so that the trace of the covariant Hessian `∑ m, extDD τ y (Ef m) (Ef m)` is the rough Laplacian `Δτ`), the two objects

* `∑ m, extDD (lcOf g) (ckt g (k+1)) x (Ef m) (Ef m) G` — the trace of the Hessian of the `(0,k+5)`-tensor `∇τ` evaluated on the tuple `G = (X, F)`; this is `Δ(∇τ)(G)`, since `extDD` corrects *all* the slots of the tuple (in particular the slot `X = G 0`);
* `extD (lcOf g) (fun F y ↦ ∑ m, extDD (lcOf g) (ckt g k) y (Ef m) (Ef m) F) x (G 0) (tail G)` — this is `∇(Δτ)` evaluated on `G`, again with `X = G 0` entering only through its *value* (both `extD` and `extDD` are `C^∞(M)`-linear in their direction arguments);

are the two terms of the tensor identity `Δ(∇τ) − ∇(Δτ) = 2 ∑ m R(Ef m, ·)·(∇_{Ef m} τ) + ∑ m (∇_{Ef m} R)(Ef m, ·)·τ`, i.e. `[Δ,∇]τ`, a *first-order* operator whose coefficients are algebraic contractions of `Rm` (`curvNormK g x 0`) and `∇Rm` (`curvNormK g x 1`) with `∇τ = ∇^{k+1}Rm` and `τ = ∇^k Rm`; hence the stated bound.  Proof route: the general Ricci identity for the `Ext` pattern, already **proved** as `Work.Diff.Evol.ricci_id_aux_extDD_antisymm` (antisymmetrised `extDD` = curvature acting on the slots) together with `Work.Diff.GE.extDD_expand`, applied to the two inner `∇`'s of the trace; the frame-motion terms (the `∇_{Ef m}Ef m` and `∇_{Ef m}X` contributions) cancel by the antisymmetry of the structure coefficients of an orthonormal frame; the remaining curvature contractions are bounded componentwise by Cauchy–Schwarz (`Work.Diff.EXT.multilinear_frame_bound`).  `hLC` supplies `CovSmooth (lcOf g)` and torsion-freeness, the two hypotheses of the cited Ricci identity (and is available from `[T2Space M]` by `Work.EXT.lcSmooth_noBoundary`).

**Status (proved).**  The proof actually implemented here goes through
`Work.Diff.EXT.lapComm_reduce` + `Work.Diff.EXT.lapComm_decomp` (which reduce the difference to the
two tower sums), then the product rule `Work.Diff.EXT.curvActT_deriv` (whose pointwise crux is the
single-slot identity `Work.Diff.EXT.lapCommInsT` / `Work.Diff.EXT.lapComm_insT`), and finally the
componentwise bounds `ckt_update_curv_le`, `ckt_update_dcurv_le`, `dCurvV_norm_le` and the product
bookkeeping `gNrm_prod_cons`, `prod_split`, `gNrm_eq_one_of_isONFrame`.  Equivalent proved copies of
the two identities also live in `Submission/Work/Diff/EXT/lapComm_curvActT_deriv.lean`
(`Work.Diff.EXT.lapComm_curvActT_deriv`) and `Submission/Work/Diff/EXT/lapCommTowerFinal.lean`
(`Work.Diff.EXT.lapCommTowerProved`).

**For the reaction-ladder step.**  This lemma is exactly the *value-level* bound of the operator
`Work.Diff.EXT.srcLapComm Ef (G t) k = lapOpE Ef (G t) (k+1) − extStep (G t) (lapOpE Ef (G t) k)`
of `Submission/Work/Diff/EXT/ladderSrcDefs.lean` (via `extDD_ckt`).  The *jet-level* version — which
`Work.Diff.EXT.ladderEfD_step` needs — is the content of that step's Weitzenböck half.  A caveat for
the *other* half (`srcConnvar`): at `t = 0` the identification of `srcConnvar` with the contraction
of `∂ₜ∇` with the tower cannot use `Work.Diff.EXT.ckt_step_tderiv` (it is stated for `t ∈ Ioo 0 T`)
together with `dtMet G 0` (the two-sided `deriv` is junk there, since `IsRicciFlow` controls `G`
only on `[0,T)`); either use a one-sided `dtMet` (a one-sided `LCVariation`) or obtain the `t = 0`
case by continuity in `t` from the bounds for `t > 0` (the relevant expressions are continuous in
`t` at `0⁺` by joint smoothness on `Ico 0 T`). -/
theorem lapComm_tower
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g : Submission.Diff.SMet I M) (x : M)
        (Ef : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
        (G : Fin (k + 5) → Work.Diff.EXT.TField (I := I) (M := M)),
        (∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (Ef i)) →
        (∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (G i)) →
        Filter.Eventually (fun y : M => Submission.Diff.IsONFrame g y (fun i => Ef i y)) (nhds x) →
        |(∑ m : Fin (Module.finrank ℝ E),
              Work.Diff.GE.extDD (Submission.Diff.lcOf g) (Work.Diff.EXT.ckt g (k + 1))
                x (Ef m) (Ef m) G)
            - Work.Diff.GE.extD (Submission.Diff.lcOf g)
                (fun (F : Fin (k + 4) → Work.Diff.EXT.TField (I := I) (M := M)) => fun (y : M) =>
                  ∑ m : Fin (Module.finrank ℝ E),
                    Work.Diff.GE.extDD (Submission.Diff.lcOf g) (Work.Diff.EXT.ckt g k)
                      y (Ef m) (Ef m) F)
                x (G 0) (fun i : Fin (k + 4) => G i.succ)|
          ≤ C * (Real.sqrt (Work.Diff.EXT.curvNormK g x 0) * Real.sqrt (Work.Diff.EXT.curvNormK g x (k + 1))
                  + Real.sqrt (Work.Diff.EXT.curvNormK g x 1) * Real.sqrt (Work.Diff.EXT.curvNormK g x k))
              * ∏ r : Fin (k + 5), Real.sqrt (g.inner x (G r x) (G r x)) := by
  classical
  refine ⟨(Module.finrank ℝ E : ℝ) * (2 * k + 9)
      + (Module.finrank ℝ E : ℝ) * (k + 4) * (Real.sqrt (Module.finrank ℝ E : ℝ) + 1),
    by positivity, ?_⟩
  intro g x Ef G hEf hG hON
  obtain ⟨hcov⟩ := (hLC g).1
  -- data
  have hONx : Submission.Diff.IsONFrame g x (fun i => Ef i x) := hON.self_of_nhds
  have hEf1 : ∀ m : Fin (Module.finrank ℝ E), gNrm g x (Ef m x) = 1 :=
    fun m => gNrm_eq_one_of_isONFrame g x hONx m
  -- smoothness of the tuples occurring below
  have hGcons : ∀ (m : Fin (Module.finrank ℝ E)) (r : Fin (k + 6)),
      SmoothF ((consF (Ef m) G) r) := by
    intro m r
    exact smoothF_cons (hEf m) hG r
  have hGtailsm : ∀ (m : Fin (Module.finrank ℝ E)) (r : Fin (k + 5)),
      SmoothF ((consF (Ef m) (fun i : Fin (k + 4) => G i.succ)) r) := by
    intro m r
    exact smoothF_cons (hEf m) (fun (i : Fin (k + 4)) => hG i.succ) r
  have hGtsm : ∀ (r : Fin (k + 4)), SmoothF ((fun i : Fin (k + 4) => G i.succ) r) :=
    fun r => hG r.succ
  -- the four scalars and the product of the norms of the tuple
  have hP : (∏ r : Fin (k + 5), gNrm g x (G r x))
      = gNrm g x (G 0 x) * ∏ r : Fin (k + 4), gNrm g x (G r.succ x) :=
    prod_split g x k G
  have hPnn : 0 ≤ ∏ r : Fin (k + 5), gNrm g x (G r x) :=
    Finset.prod_nonneg fun r _ => gNrm_nonneg g x _
  have hY0 : 0 ≤ Real.sqrt (curvNormK g x 0) := Real.sqrt_nonneg _
  have hY1 : 0 ≤ Real.sqrt (curvNormK g x 1) := Real.sqrt_nonneg _
  have hYk : 0 ≤ Real.sqrt (curvNormK g x (k + 1)) := Real.sqrt_nonneg _
  have hYj : 0 ≤ Real.sqrt (curvNormK g x k) := Real.sqrt_nonneg _
  -- the two pieces of the decomposition
  have hmain : |(∑ m : Fin (Module.finrank ℝ E),
          Work.Diff.GE.extDD (Submission.Diff.lcOf g) (ckt g (k + 1))
            x (Ef m) (Ef m) G)
        - Work.Diff.GE.extD (Submission.Diff.lcOf g)
            (fun (F : Fin (k + 4) → Work.Diff.EXT.TField (I := I) (M := M)) => fun (y : M) =>
              ∑ m : Fin (Module.finrank ℝ E),
                Work.Diff.GE.extDD (Submission.Diff.lcOf g) (ckt g k) y (Ef m) (Ef m) F)
            x (G 0) (fun i : Fin (k + 4) => G i.succ)|
      = |(∑ m : Fin (Module.finrank ℝ E),
            Work.Diff.GE.extD (Submission.Diff.lcOf g) (curvActT (I := I) (M := M) g k)
              x (Ef m) (consF (Ef m) G))
          + (∑ m : Fin (Module.finrank ℝ E), ∑ s : Fin (k + 5), ckt g (k + 1)
              (Function.update (consF (Ef m) (fun i : Fin (k + 4) => G i.succ)) s
                (fun z => curv (Submission.Diff.lcOf g) (Ef m) (G 0)
                  ((consF (Ef m) (fun i : Fin (k + 4) => G i.succ)) s) z)) x)| := by
    rw [lapComm_reduce hLC g k x Ef hEf hON G hG, lapComm_decomp hLC g k x Ef hEf G hG]
    rw [show -(∑ m : Fin (Module.finrank ℝ E),
          Work.Diff.GE.extD (Submission.Diff.lcOf g) (curvActT (I := I) (M := M) g k)
            x (Ef m) (consF (Ef m) G))
        - (∑ m : Fin (Module.finrank ℝ E), ∑ s : Fin (k + 5), ckt g (k + 1)
            (Function.update (consF (Ef m) (fun i : Fin (k + 4) => G i.succ)) s
              (fun z => curv (Submission.Diff.lcOf g) (Ef m) (G 0)
                ((consF (Ef m) (fun i : Fin (k + 4) => G i.succ)) s) z)) x)
        = - ((∑ m, Work.Diff.GE.extD (Submission.Diff.lcOf g)
              (curvActT (I := I) (M := M) g k) x (Ef m) (consF (Ef m) G))
            + (∑ m, ∑ s : Fin (k + 5), ckt g (k + 1)
              (Function.update (consF (Ef m) (fun i : Fin (k + 4) => G i.succ)) s
                (fun z => curv (Submission.Diff.lcOf g) (Ef m) (G 0)
                  ((consF (Ef m) (fun i : Fin (k + 4) => G i.succ)) s) z)) x)) from by ring]
    rw [abs_neg]
  rw [hmain]
  refine le_trans (abs_add_le _ _) ?_
  -- ### first family: `|∑_m extD (curvActT g k) x (Ef m) (Ef m :: G)|`
  have hfam1 : |∑ m : Fin (Module.finrank ℝ E),
        Work.Diff.GE.extD (Submission.Diff.lcOf g) (curvActT (I := I) (M := M) g k)
          x (Ef m) (consF (Ef m) G)|
      ≤ (Module.finrank ℝ E : ℝ) * ((k + 4 : ℝ) * (Real.sqrt (curvNormK g x 0)
            * Real.sqrt (curvNormK g x (k + 1)) * ∏ r : Fin (k + 5), gNrm g x (G r x))
          + (k + 4 : ℝ) * ((Real.sqrt (Module.finrank ℝ E : ℝ) + 1)
            * (Real.sqrt (curvNormK g x 1) * Real.sqrt (curvNormK g x k)
              * ∏ r : Fin (k + 5), gNrm g x (G r x)))) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ m : Fin (Module.finrank ℝ E),
        |Work.Diff.GE.extD (Submission.Diff.lcOf g) (curvActT (I := I) (M := M) g k)
          x (Ef m) (consF (Ef m) G)|
        ≤ (k + 4 : ℝ) * (Real.sqrt (curvNormK g x 0)
            * Real.sqrt (curvNormK g x (k + 1)) * ∏ r : Fin (k + 5), gNrm g x (G r x))
          + (k + 4 : ℝ) * ((Real.sqrt (Module.finrank ℝ E : ℝ) + 1)
            * (Real.sqrt (curvNormK g x 1) * Real.sqrt (curvNormK g x k)
              * ∏ r : Fin (k + 5), gNrm g x (G r x))) := by
      intro m
      have hGsm : ∀ i : Fin (k + 6), SmoothF ((consF (Ef m) G) i) := hGcons m
      have hGtail : ∀ i : Fin (k + 4), SmoothF ((fun i : Fin (k + 4) => G i.succ) i) := hGtsm
      -- the product rule
      rw [curvActT_deriv (I := I) (M := M) hLC g k x (Ef m) (hEf m)
        (consF (Ef m) G) hGsm]
      simp only [Fin.cons_zero, Fin.cons_succ]
      refine le_trans (abs_add_le _ _) ?_
      -- the two sums of the product rule
      have hs1 : |∑ s : Fin (k + 4), ckt g (k + 1)
            (consF (Ef m) (Function.update (fun i : Fin (k + 4) => G i.succ) s
              (fun z => curv (Submission.Diff.lcOf g) (Ef m) (G 0) (G s.succ) z))) x|
          ≤ (k + 4 : ℝ) * (Real.sqrt (curvNormK g x 0)
              * Real.sqrt (curvNormK g x (k + 1)) * ∏ r : Fin (k + 5), gNrm g x (G r x)) := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        have hb : ∀ s : Fin (k + 4),
            |ckt g (k + 1) (consF (Ef m) (Function.update
                (fun i : Fin (k + 4) => G i.succ) s
                (fun z => curv (Submission.Diff.lcOf g) (Ef m) (G 0) (G s.succ) z))) x|
              ≤ Real.sqrt (curvNormK g x 0) * Real.sqrt (curvNormK g x (k + 1))
                * ∏ r : Fin (k + 5), gNrm g x (G r x) := by
          intro s
          have h1 := ckt_update_curv_le hLC g x (k + 1)
            (consF (Ef m) (fun i : Fin (k + 4) => G i.succ)) (hGtailsm m) s.succ (hEf m) (hG 0)
          -- rewrite the insertion and the tuple into the goal's shape
          rw [show (fun z => curv (Submission.Diff.lcOf g) (Ef m) (G 0)
                ((consF (Ef m) (fun i : Fin (k + 4) => G i.succ)) s.succ) z)
              = (fun z => curv (Submission.Diff.lcOf g) (Ef m) (G 0) (G s.succ) z) from by
            rw [show (consF (Ef m) (fun i : Fin (k + 4) => G i.succ)) s.succ = G s.succ
              from Fin.cons_succ _ _ _]] at h1
          rw [upd_cons_succ] at h1
          refine le_trans h1 ?_
          -- the product: `|Ef m| = 1` and `prod_split`
          have hprod : gNrm g x (Ef m x) * gNrm g x (G 0 x)
              * ∏ r : Fin (k + 5), gNrm g x
                  ((consF (Ef m) (fun i : Fin (k + 4) => G i.succ)) r x)
              = ∏ r : Fin (k + 5), gNrm g x (G r x) := by
            rw [gNrm_prod_cons, hEf1 m, hP]
            ring
          rw [hprod]
        calc (∑ s : Fin (k + 4), |ckt g (k + 1) (consF (Ef m) (Function.update
              (fun i : Fin (k + 4) => G i.succ) s
              (fun z => curv (Submission.Diff.lcOf g) (Ef m) (G 0) (G s.succ) z))) x|)
            ≤ ∑ _s : Fin (k + 4), Real.sqrt (curvNormK g x 0) * Real.sqrt (curvNormK g x (k + 1))
                * ∏ r : Fin (k + 5), gNrm g x (G r x) := Finset.sum_le_sum fun s _ => hb s
          _ = (k + 4 : ℝ) * (Real.sqrt (curvNormK g x 0) * Real.sqrt (curvNormK g x (k + 1))
                * ∏ r : Fin (k + 5), gNrm g x (G r x)) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              push_cast
              ring
      have hs2 : |∑ s : Fin (k + 4), ckt g k
            (Function.update (Function.update (fun i : Fin (k + 4) => G i.succ) s
                (fun z => curv (Submission.Diff.lcOf g) (Ef m) (G 0) (G s.succ) z)) s
              (dCurvV (Submission.Diff.lcOf g) (Ef m) (Ef m) (G 0) (G s.succ))) x|
          ≤ (k + 4 : ℝ) * ((Real.sqrt (Module.finrank ℝ E : ℝ) + 1)
              * (Real.sqrt (curvNormK g x 1) * Real.sqrt (curvNormK g x k)
                * ∏ r : Fin (k + 5), gNrm g x (G r x))) := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        have hb : ∀ s : Fin (k + 4),
            |ckt g k (Function.update (Function.update (fun i : Fin (k + 4) => G i.succ) s
                (fun z => curv (Submission.Diff.lcOf g) (Ef m) (G 0) (G s.succ) z)) s
              (dCurvV (Submission.Diff.lcOf g) (Ef m) (Ef m) (G 0) (G s.succ))) x|
              ≤ (Real.sqrt (Module.finrank ℝ E : ℝ) + 1)
                * (Real.sqrt (curvNormK g x 1) * Real.sqrt (curvNormK g x k)
                  * ∏ r : Fin (k + 5), gNrm g x (G r x)) := by
          intro s
          rw [Function.update_idem]
          have h1 := ckt_update_dcurv_le hLC g x k (fun i : Fin (k + 4) => G i.succ) hGtail s
            (hEf m) (hEf m) (hG 0) (Real.sqrt (Module.finrank ℝ E : ℝ) + 1)
            (smoothF_dCurvV hLC g (hEf m) (hEf m) (hG 0) (hG s.succ))
            (dCurvV_norm_le hLC g x (Ef m) (Ef m) (G 0) (G s.succ)
              (hEf m) (hEf m) (hG 0) (hG s.succ))
          refine le_trans h1 ?_
          have hprod : gNrm g x (Ef m x) * gNrm g x (Ef m x) * gNrm g x (G 0 x)
              * ∏ r : Fin (k + 4), gNrm g x (G r.succ x)
              = ∏ r : Fin (k + 5), gNrm g x (G r x) := by
            rw [hEf1 m, hP]
            ring
          rw [hprod]
          refine le_of_eq ?_
          ring
        calc (∑ s : Fin (k + 4), |ckt g k (Function.update
              (Function.update (fun i : Fin (k + 4) => G i.succ) s
                (fun z => curv (Submission.Diff.lcOf g) (Ef m) (G 0) (G s.succ) z)) s
              (dCurvV (Submission.Diff.lcOf g) (Ef m) (Ef m) (G 0) (G s.succ))) x|)
            ≤ ∑ _s : Fin (k + 4), (Real.sqrt (Module.finrank ℝ E : ℝ) + 1)
                * (Real.sqrt (curvNormK g x 1) * Real.sqrt (curvNormK g x k)
                  * ∏ r : Fin (k + 5), gNrm g x (G r x)) := Finset.sum_le_sum fun s _ => hb s
          _ = (k + 4 : ℝ) * ((Real.sqrt (Module.finrank ℝ E : ℝ) + 1)
                * (Real.sqrt (curvNormK g x 1) * Real.sqrt (curvNormK g x k)
                  * ∏ r : Fin (k + 5), gNrm g x (G r x))) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              push_cast
              ring
      exact add_le_add hs1 hs2
    calc (∑ m : Fin (Module.finrank ℝ E),
          |Work.Diff.GE.extD (Submission.Diff.lcOf g) (curvActT (I := I) (M := M) g k)
            x (Ef m) (consF (Ef m) G)|)
        ≤ ∑ _m : Fin (Module.finrank ℝ E),
            ((k + 4 : ℝ) * (Real.sqrt (curvNormK g x 0)
              * Real.sqrt (curvNormK g x (k + 1)) * ∏ r : Fin (k + 5), gNrm g x (G r x))
            + (k + 4 : ℝ) * ((Real.sqrt (Module.finrank ℝ E : ℝ) + 1)
              * (Real.sqrt (curvNormK g x 1) * Real.sqrt (curvNormK g x k)
                * ∏ r : Fin (k + 5), gNrm g x (G r x)))) :=
          Finset.sum_le_sum fun m _ => hterm m
      _ = (Module.finrank ℝ E : ℝ) * ((k + 4 : ℝ) * (Real.sqrt (curvNormK g x 0)
              * Real.sqrt (curvNormK g x (k + 1)) * ∏ r : Fin (k + 5), gNrm g x (G r x))
            + (k + 4 : ℝ) * ((Real.sqrt (Module.finrank ℝ E : ℝ) + 1)
              * (Real.sqrt (curvNormK g x 1) * Real.sqrt (curvNormK g x k)
                * ∏ r : Fin (k + 5), gNrm g x (G r x)))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- ### second family: the `∇Rm`-insertion sum
  have hfam2 : |∑ m : Fin (Module.finrank ℝ E), ∑ s : Fin (k + 5), ckt g (k + 1)
        (Function.update (consF (Ef m) (fun i : Fin (k + 4) => G i.succ)) s
          (fun z => curv (Submission.Diff.lcOf g) (Ef m) (G 0)
            ((consF (Ef m) (fun i : Fin (k + 4) => G i.succ)) s) z)) x|
      ≤ (Module.finrank ℝ E : ℝ) * ((k + 5 : ℝ) * (Real.sqrt (curvNormK g x 0)
          * Real.sqrt (curvNormK g x (k + 1)) * ∏ r : Fin (k + 5), gNrm g x (G r x))) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ m : Fin (Module.finrank ℝ E),
        |∑ s : Fin (k + 5), ckt g (k + 1)
          (Function.update (consF (Ef m) (fun i : Fin (k + 4) => G i.succ)) s
            (fun z => curv (Submission.Diff.lcOf g) (Ef m) (G 0)
              ((consF (Ef m) (fun i : Fin (k + 4) => G i.succ)) s) z)) x|
        ≤ (k + 5 : ℝ) * (Real.sqrt (curvNormK g x 0)
          * Real.sqrt (curvNormK g x (k + 1)) * ∏ r : Fin (k + 5), gNrm g x (G r x)) := by
      intro m
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have hb : ∀ s : Fin (k + 5),
          |ckt g (k + 1) (Function.update (consF (Ef m) (fun i : Fin (k + 4) => G i.succ)) s
            (fun z => curv (Submission.Diff.lcOf g) (Ef m) (G 0)
              ((consF (Ef m) (fun i : Fin (k + 4) => G i.succ)) s) z)) x|
            ≤ Real.sqrt (curvNormK g x 0) * Real.sqrt (curvNormK g x (k + 1))
              * ∏ r : Fin (k + 5), gNrm g x (G r x) := by
        intro s
        have h1 := ckt_update_curv_le hLC g x (k + 1)
          (consF (Ef m) (fun i : Fin (k + 4) => G i.succ)) (hGtailsm m) s (hEf m) (hG 0)
        refine le_trans h1 ?_
        have hprod : gNrm g x (Ef m x) * gNrm g x (G 0 x)
            * ∏ r : Fin (k + 5), gNrm g x
                ((consF (Ef m) (fun i : Fin (k + 4) => G i.succ)) r x)
            = ∏ r : Fin (k + 5), gNrm g x (G r x) := by
          rw [gNrm_prod_cons, hEf1 m, hP]
          ring
        rw [hprod]
      calc (∑ s : Fin (k + 5), |ckt g (k + 1) (Function.update
            (consF (Ef m) (fun i : Fin (k + 4) => G i.succ)) s
            (fun z => curv (Submission.Diff.lcOf g) (Ef m) (G 0)
              ((consF (Ef m) (fun i : Fin (k + 4) => G i.succ)) s) z)) x|)
          ≤ ∑ _s : Fin (k + 5), Real.sqrt (curvNormK g x 0) * Real.sqrt (curvNormK g x (k + 1))
              * ∏ r : Fin (k + 5), gNrm g x (G r x) := Finset.sum_le_sum fun s _ => hb s
        _ = (k + 5 : ℝ) * (Real.sqrt (curvNormK g x 0) * Real.sqrt (curvNormK g x (k + 1))
              * ∏ r : Fin (k + 5), gNrm g x (G r x)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            push_cast
            ring
    calc (∑ m : Fin (Module.finrank ℝ E), |∑ s : Fin (k + 5), ckt g (k + 1)
          (Function.update (consF (Ef m) (fun i : Fin (k + 4) => G i.succ)) s
            (fun z => curv (Submission.Diff.lcOf g) (Ef m) (G 0)
              ((consF (Ef m) (fun i : Fin (k + 4) => G i.succ)) s) z)) x|)
        ≤ ∑ _m : Fin (Module.finrank ℝ E), (k + 5 : ℝ) * (Real.sqrt (curvNormK g x 0)
          * Real.sqrt (curvNormK g x (k + 1)) * ∏ r : Fin (k + 5), gNrm g x (G r x)) :=
          Finset.sum_le_sum fun m _ => hterm m
      _ = (Module.finrank ℝ E : ℝ) * ((k + 5 : ℝ) * (Real.sqrt (curvNormK g x 0)
          * Real.sqrt (curvNormK g x (k + 1)) * ∏ r : Fin (k + 5), gNrm g x (G r x))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- ### arithmetic
  refine le_trans (add_le_add hfam1 hfam2) ?_
  have hA : (0 : ℝ) ≤ Real.sqrt (curvNormK g x 0) * Real.sqrt (curvNormK g x (k + 1))
      * ∏ r : Fin (k + 5), gNrm g x (G r x) := by positivity
  have hB : (0 : ℝ) ≤ Real.sqrt (curvNormK g x 1) * Real.sqrt (curvNormK g x k)
      * ∏ r : Fin (k + 5), gNrm g x (G r x) := by positivity
  have hc1 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) * (k + 4)
      * (Real.sqrt (Module.finrank ℝ E : ℝ) + 1) := by positivity
  have hc2 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) * (2 * k + 9) := by positivity
  calc (Module.finrank ℝ E : ℝ)
        * ((k + 4 : ℝ) * (Real.sqrt (curvNormK g x 0) * Real.sqrt (curvNormK g x (k + 1))
            * ∏ r : Fin (k + 5), gNrm g x (G r x))
          + (k + 4 : ℝ) * ((Real.sqrt (Module.finrank ℝ E : ℝ) + 1)
            * (Real.sqrt (curvNormK g x 1) * Real.sqrt (curvNormK g x k)
              * ∏ r : Fin (k + 5), gNrm g x (G r x))))
        + (Module.finrank ℝ E : ℝ) * ((k + 5 : ℝ)
            * (Real.sqrt (curvNormK g x 0) * Real.sqrt (curvNormK g x (k + 1))
              * ∏ r : Fin (k + 5), gNrm g x (G r x)))
      = ((Module.finrank ℝ E : ℝ) * (2 * k + 9))
          * (Real.sqrt (curvNormK g x 0) * Real.sqrt (curvNormK g x (k + 1))
            * ∏ r : Fin (k + 5), gNrm g x (G r x))
        + ((Module.finrank ℝ E : ℝ) * (k + 4) * (Real.sqrt (Module.finrank ℝ E : ℝ) + 1))
          * (Real.sqrt (curvNormK g x 1) * Real.sqrt (curvNormK g x k)
            * ∏ r : Fin (k + 5), gNrm g x (G r x)) := by ring
    _ ≤ (((Module.finrank ℝ E : ℝ) * (2 * k + 9))
          + ((Module.finrank ℝ E : ℝ) * (k + 4) * (Real.sqrt (Module.finrank ℝ E : ℝ) + 1)))
          * ((Real.sqrt (curvNormK g x 0) * Real.sqrt (curvNormK g x (k + 1))
              * ∏ r : Fin (k + 5), gNrm g x (G r x))
            + (Real.sqrt (curvNormK g x 1) * Real.sqrt (curvNormK g x k)
              * ∏ r : Fin (k + 5), gNrm g x (G r x))) := by
        nlinarith [hA, hB, hc1, hc2]
    _ = ((Module.finrank ℝ E : ℝ) * (2 * k + 9)
          + (Module.finrank ℝ E : ℝ) * (k + 4) * (Real.sqrt (Module.finrank ℝ E : ℝ) + 1))
          * (Real.sqrt (curvNormK g x 0) * Real.sqrt (curvNormK g x (k + 1))
            + Real.sqrt (curvNormK g x 1) * Real.sqrt (curvNormK g x k))
          * ∏ r : Fin (k + 5), gNrm g x (G r x) := by ring


end Work.Diff.EXT
