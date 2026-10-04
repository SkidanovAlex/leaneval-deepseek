import Mathlib
import Submission.Work.Diff.EXT.ladderSrcDefs
import Submission.Work.Diff.EXT.jetSmoothDefs
import Submission.Work.Diff.EXT.ckt_step_tderiv
import Submission.Work.Diff.GE.curv_var_prelim
import Submission.Work.Diff.T.lc_variation
import Submission.Work.Diff.Evol.cv_dLC
import Submission.Work.Diff.EXT.evolX.connVarDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The one-step time derivative of the curvature tower

This module proves the operator identity of the connection-variation source of the reaction-ladder
step:

`dtOpD G t (k+1) F = extStep (G t) (dtOpD G t k) F + connVarOp G t k F`  (near the base point),

i.e. the difference `dtOpD G t (k+1) F − extStep (G t) (dtOpD G t k) F` is exactly the negative of
the level-`k` curvature tower with one slot replaced by the first variation `dLC G t` of the
Levi-Civita connection.

The proof combines

* `Work.Diff.EXT.ckt_step_tderiv` — the honest `s`-derivative at `t` of one recursion step of the
  tower `s ↦ ckt (G s) (k+1) F y`, with the connection-variation vector `Av s` characterised by the
  Koszul pairing;
* `Work.Diff.GE.dLC_pairing` + `Work.Diff.T.variation_algebra` — the identification of that vector
  with `dLC G t (F 0) (F ∘ succ s) y`;
* `derivWithin_of_mem_nhds` — the interior time `0 < t` turns the right derivative `dtOpD` into the
  two-sided derivative;
* `Work.Diff.EXT.ckt_val_dep` — single-slot value dependence of the tower, replacing the pointwise
  smooth extension `smoothExt y (dLC …)` by the globally smooth field `dLC …`;
* `Work.Diff.Evol.cv_dLC_smooth` — smoothness of the field `y ↦ dLC G t Y Z y`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.evolX

theorem dtOpD_step_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (hLV : Submission.Diff.LCVariation I M)
    {G : ℝ → Submission.Diff.SMet I M} {T : ℝ} (hflow : Submission.Diff.IsRicciFlow G T)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T) (k : ℕ) (x : M)
    (F : Fin (k + 5) → Work.Diff.EXT.TField (I := I) (M := M))
    (hF : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (F i)) :
    Filter.EventuallyEq (nhds x)
      (fun y : M => Work.Diff.EXT.dtOpD (I := I) (M := M) G t (k + 1) F y)
      (fun y : M => Work.Diff.EXT.extStep (I := I) (M := M) (G t)
        (Work.Diff.EXT.dtOpD (I := I) (M := M) G t k) F y
      + Work.Diff.EXT.evolX.connVarOp (I := I) (M := M) G t k F y) := by
  classical
  have ht0 : 0 < t := ht.1
  have hIoi : Set.Ioi (0 : ℝ) ∈ 𝓝 t := isOpen_Ioi.mem_nhds ht0
  have hJopen : IsOpen (Set.Ioo (0 : ℝ) T) := isOpen_Ioo
  have hJs : Submission.Diff.JointSmooth G (Set.Ioo (0 : ℝ) T) :=
    hflow.1.mono (Set.prod_mono Set.Ioo_subset_Ico_self (subset_refl _))
  have hF' : ∀ i : Fin (k + 4), Work.Diff.EXT.SmoothF ((fun i : Fin (k + 4) => F i.succ) i) :=
    fun i => hF i.succ
  -- the inserted field `dLC G t (F 0) (F' s)` is globally smooth
  have hWs : ∀ s : Fin (k + 4),
      Work.Diff.EXT.SmoothF (Submission.Diff.dLC G t (F 0) ((fun i : Fin (k + 4) => F i.succ) s)) :=
    fun s => fun y => Work.Diff.Evol.cv_dLC_smooth (I := I) (M := M) hLC hLV hJopen hJs ht
      (F 0) ((fun i : Fin (k + 4) => F i.succ) s) (hF 0) (hF' s) y
  filter_upwards with y
  -- the pairing identity characterising the connection-variation vector
  have hAv : ∀ (s : Fin (k + 4)) (Z : Work.Diff.EXT.TField (I := I) (M := M)),
      Work.Diff.EXT.SmoothF Z →
      (G t).inner y (Submission.Diff.dLC G t (F 0)
          ((fun i : Fin (k + 4) => F i.succ) s) y) (Z y)
        = (1 / 2 : ℝ) *
            (Submission.Diff.covDerivSym2 (Submission.Diff.lcOf (G t)) (Submission.Diff.dtMet G t)
                (F 0) ((fun i : Fin (k + 4) => F i.succ) s) Z y
              + Submission.Diff.covDerivSym2 (Submission.Diff.lcOf (G t))
                (Submission.Diff.dtMet G t) ((fun i : Fin (k + 4) => F i.succ) s) (F 0) Z y
              - Submission.Diff.covDerivSym2 (Submission.Diff.lcOf (G t))
                (Submission.Diff.dtMet G t) Z (F 0) ((fun i : Fin (k + 4) => F i.succ) s) y) := by
    intro s Z hZ
    have hp := Work.Diff.GE.dLC_pairing (I := I) (M := M) hLV hJopen hJs ht
      (Y := F 0) (Z := (fun i : Fin (k + 4) => F i.succ) s) (W := Z) (hF 0) (hF' s) hZ y
    have hv := Work.Diff.T.variation_algebra (I := I) (M := M) (G := G) hJopen hJs ht
      (x := y) (F 0) ((fun i : Fin (k + 4) => F i.succ) s) Z (hF 0) (hF' s) hZ
    linarith [hp, hv]
  -- the one-step time derivative of the tower at `y`
  have hder := Work.Diff.EXT.ckt_step_tderiv (I := I) (M := M) hLC hLV hflow ht F hF y
    (Av := fun s => Submission.Diff.dLC G t (F 0) ((fun i : Fin (k + 4) => F i.succ) s) y) hAv
  -- rewrite `dtOpD` as a two-sided derivative (interior time) and use `hder`
  have hdw : derivWithin (fun s : ℝ => Work.Diff.EXT.ckt (G s) (k + 1) F y) (Set.Ioi 0) t
      = deriv (fun s : ℝ => Work.Diff.EXT.ckt (G s) (k + 1) F y) t := derivWithin_of_mem_nhds hIoi
  rw [Work.Diff.EXT.dtOpD, hdw, hder.deriv]
  simp only [Work.Diff.EXT.extStep, Work.Diff.EXT.dirF, Work.Diff.EXT.evolX.connVarOp,
    Pi.sub_apply]
  -- identify the two-sided derivatives with `dtOpD`
  have hid1 : mvfderiv I (fun y' : M => deriv
        (fun s : ℝ => Work.Diff.EXT.ckt (G s) k (fun i : Fin (k + 4) => F i.succ) y') t) y (F 0 y)
      = mvfderiv I (fun y' : M => Work.Diff.EXT.dtOpD (I := I) (M := M) G t k
          (fun i : Fin (k + 4) => F i.succ) y') y (F 0 y) := by
    have hfun : (fun y' : M => deriv
          (fun s : ℝ => Work.Diff.EXT.ckt (G s) k (fun i : Fin (k + 4) => F i.succ) y') t)
        = fun y' : M => Work.Diff.EXT.dtOpD (I := I) (M := M) G t k
            (fun i : Fin (k + 4) => F i.succ) y' := by
      funext y'
      rw [Work.Diff.EXT.dtOpD, derivWithin_of_mem_nhds hIoi]
    rw [hfun]
  have hid2 : ∀ s : Fin (k + 4),
      deriv (fun s' : ℝ => Work.Diff.EXT.ckt (G s') k
          (Function.update (fun i : Fin (k + 4) => F i.succ) s
            (fun z : M => Submission.Diff.lcOf (G t)
              ((fun i : Fin (k + 4) => F i.succ) s) z (F 0 z))) y) t
        = Work.Diff.EXT.dtOpD (I := I) (M := M) G t k
            (Function.update (fun i : Fin (k + 4) => F i.succ) s
              (fun z : M => Submission.Diff.lcOf (G t)
                ((fun i : Fin (k + 4) => F i.succ) s) z (F 0 z))) y := by
    intro s
    rw [Work.Diff.EXT.dtOpD, derivWithin_of_mem_nhds hIoi]
  have hid3 : ∀ s : Fin (k + 4),
      Work.Diff.EXT.ckt (G t) k (Function.update (fun i : Fin (k + 4) => F i.succ) s
          (fun z : M => Submission.Diff.smoothExt y
            (Submission.Diff.dLC G t (F 0) ((fun i : Fin (k + 4) => F i.succ) s) y) z)) y
        = Work.Diff.EXT.ckt (G t) k (Function.update (fun i : Fin (k + 4) => F i.succ) s
            (Submission.Diff.dLC G t (F 0) ((fun i : Fin (k + 4) => F i.succ) s))) y := by
    intro s
    refine Work.Diff.EXT.ckt_val_dep (I := I) (M := M) hLC (G t) k y hF' s
      (Work.Diff.GE.smoothExt_cmdiff y _) (hWs s) ?_
    simp only [Work.Diff.GE.smoothExt_apply]
  rw [hid1, Finset.sum_congr rfl (fun s _ => hid2 s), Finset.sum_congr rfl (fun s _ => hid3 s)]
  have hdir : ∀ s : Fin (k + 4), Work.Diff.EXT.dirF (G t)
      ((fun i : Fin (k + 4) => F i.succ) s) (F 0)
      = (fun z : M => Submission.Diff.lcOf (G t)
          ((fun i : Fin (k + 4) => F i.succ) s) z (F 0 z)) := fun s => rfl
  simp only [hdir]
  ring

end Work.Diff.EXT.evolX
