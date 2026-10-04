import Mathlib
import Submission.Work.Diff.EXT.ckt_step_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The time-derivative of one step of the curvature tower `∇^k Rm`

The proof of the requested statement, using the auxiliary module
`Submission.Work.Diff.EXT.ckt_step_aux`:

* `ckt_familySmoothAt` — joint smoothness of `(s,y) ↦ ckt (G s) k U y` at `(t,y)`;
* `hasDerivAt_ckt_family` — its scalar (differentiability) form;
* `hasDerivAt_linMap_apply_family` — the basis product rule;
* `kptSlotLin` — `∇^k Rm` as a linear functional of one slot;
* `kpt_eq_ckt_update`, `ckt_update_eq_constant` — the value-dependence identities.

Every statement about the tangent space `TangentSpace I y` is phrased with the *model space* `E`
as codomain (as in `Submission.Diff.LCVariation`), because `TangentSpace I y` is a non-reducible
type synonym and carries no `NormedAddCommGroup` instance unless a `RiemannianBundle` instance is
in scope; introducing one locally would change the instance arguments of the types and break the
comparison with the statement's goal.

NOTE ON IMPORTS.  The statement below is the requested one, verbatim.  It mentions
`Work.Diff.EXT.ckt`, which is declared both by `Submission.Work.Diff.EXT.curvNormK_frame_indep`
and by its clash-free copy `...curvNormK_frame_indepL`.  The proof needs, besides `ckt`, the
joint smoothness of the tower along a metric family (`Work.Diff.EXT.covK_familySmooth`, pulled in
by `ckt_step_aux`), whose import closure contains `Submission.Work.Diff.GE.norms_defs`; the latter
declares `Work.Diff.GE.rot5`, a name that is *also* declared (as a lemma) in
`Submission.Work.Diff.GE.frobSq5_frameIndep`, which the non-`L` copy of `curvNormK_frame_indep`
pulls in.  No module may therefore import `covK_familySmooth` together with the non-`L` copy of
`curvNormK_frame_indep`.  The `L` copy declares exactly the same constants (`ckt`, `Kpt`,
`ckt_succ`, `ckt_eq_covKRmExt`, ...) and is used here for that reason; this is the same device
that `Submission/Work/Diff/EXT/curvNormK_jointSmooth.lean` uses.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Commons.Geometry.Manifold.VectorField

namespace Work.Diff.EXT

theorem ckt_step_tderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (hLV : Submission.Diff.LCVariation I M)
    {G : ℝ → Submission.Diff.SMet I M} {T : ℝ} (hflow : Submission.Diff.IsRicciFlow G T)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T)
    {k : ℕ} (F : Fin (k + 5) → (y : M) → TangentSpace I y)
    (hF : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (F i)) (y : M)
    (Av : Fin (k + 4) → TangentSpace I y)
    (hAv : ∀ (s : Fin (k + 4)) (Z : (y : M) → TangentSpace I y),
        Work.Diff.GE.SmoothFieldT (I := I) (M := M) Z →
        (G t).inner y (Av s) (Z y)
          = (1 / 2 : ℝ) *
              (Submission.Diff.covDerivSym2 (Submission.Diff.lcOf (G t)) (Submission.Diff.dtMet G t)
                  (F 0) ((fun i : Fin (k + 4) => F i.succ) s) Z y
                + Submission.Diff.covDerivSym2 (Submission.Diff.lcOf (G t)) (Submission.Diff.dtMet G t)
                  ((fun i : Fin (k + 4) => F i.succ) s) (F 0) Z y
                - Submission.Diff.covDerivSym2 (Submission.Diff.lcOf (G t)) (Submission.Diff.dtMet G t)
                  Z (F 0) ((fun i : Fin (k + 4) => F i.succ) s) y)) :
    HasDerivAt (fun s => Work.Diff.EXT.ckt (G s) (k + 1) F y)
      ( ((mvfderiv I (fun y' : M =>
            deriv (fun s => Work.Diff.EXT.ckt (G s) k (fun i : Fin (k + 4) => F i.succ) y') t)
            y) (F 0 y)
          - ∑ s : Fin (k + 4), deriv (fun s' =>
              Work.Diff.EXT.ckt (G s') k
                (Function.update (fun i : Fin (k + 4) => F i.succ) s
                  (fun z => Submission.Diff.lcOf (G t) ((fun i : Fin (k + 4) => F i.succ) s) z
                    (F 0 z))) y) t)
        - ∑ s : Fin (k + 4), Work.Diff.EXT.ckt (G t) k
            (Function.update (fun i : Fin (k + 4) => F i.succ) s
              (fun z => Submission.Diff.smoothExt y (Av s) z)) y) t := by
  classical
  set F' : Fin (k + 4) → (y : M) → TangentSpace I y := fun i => F i.succ with hF'def
  have hF's : ∀ i, Work.Diff.EXT.SmoothTField (I := I) (M := M) (F' i) := fun i => hF i.succ
  -- ## the spatial derivative of the time derivative of the level-`k` tower
  have hΦ : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => Work.Diff.EXT.ckt (G p.1) k F' p.2) (t, y) :=
    Work.Diff.EXT.ckt_familySmoothAt (I := I) (M := M) hLC hflow ht hF's
  have hP : HasDerivAt
      (fun s : ℝ => (mvfderiv I (Work.Diff.EXT.ckt (G s) k F') y) (F 0 y))
      ((mvfderiv I (fun y' : M => deriv (fun s : ℝ => Work.Diff.EXT.ckt (G s) k F' y') t) y)
        (F 0 y)) t :=
    Work.Diff.GE.hasDerivAt_mvfderiv (I := I) (M := M) hΦ
  -- ## the correction terms, one slot at a time
  have hQ : ∀ j : Fin (k + 4),
      HasDerivAt (fun s : ℝ => Work.Diff.EXT.ckt (G s) k
          (Function.update F' j (Work.Diff.EXT.dirF (G s) (F' j) (F 0))) y)
        (deriv (fun s' : ℝ => Work.Diff.EXT.ckt (G s') k
            (Function.update F' j (Work.Diff.EXT.dirF (G t) (F' j) (F 0))) y) t
          + Work.Diff.EXT.ckt (G t) k
              (Function.update F' j (fun z : M => Submission.Diff.smoothExt y (Av j) z)) y) t := by
    intro j
    have hVj : HasDerivAt (fun s : ℝ => (Work.Diff.EXT.dirF (G s) (F' j) (F 0) y : E))
        (Av j : E) t := by
      have hJM : Work.Diff.EXT.JointMet G (Set.Ioo 0 T ×ˢ (Set.univ : Set M)) :=
        (Work.Diff.EXT.jointMet_prod G (Set.Ico 0 T)).mp hflow.1 |>.mono
          (Set.prod_mono Set.Ioo_subset_Ico_self (subset_refl _))
      have hJS : Submission.Diff.JointSmooth G (Set.Ioo 0 T) :=
        (Work.Diff.EXT.jointMet_prod G (Set.Ioo 0 T)).mpr hJM
      obtain ⟨A, hAder, hApair⟩ :=
        hLV G (Set.Ioo 0 T) isOpen_Ioo hJS t ht (F 0) (F' j) (hF 0) (hF's j) y
      have hAeq : A = Av j := by
        have hZ : Work.Diff.EXT.SmoothTField (I := I) (M := M)
            (Submission.Diff.smoothExt y (A - Av j)) :=
          Work.Diff.GE.smoothExt_cmdiff y (A - Av j)
        have e2 := hApair (Submission.Diff.smoothExt y (A - Av j)) hZ
        have e3 := hAv j (Submission.Diff.smoothExt y (A - Av j)) hZ
        simp only [Work.Diff.GE.smoothExt_apply] at e2 e3
        have hEq : (G t).inner y A (A - Av j) = (G t).inner y (Av j) (A - Av j) :=
          e2.trans e3.symm
        have hsplit : (G t).inner y (A - Av j)
            = (G t).inner y A - (G t).inner y (Av j) :=
          ContinuousLinearMap.map_sub _ _ _
        have hzero : (G t).inner y (A - Av j) (A - Av j) = 0 := by
          rw [hsplit, ContinuousLinearMap.sub_apply, hEq, sub_self]
        by_contra hne
        have hpos := (G t).pos y (A - Av j) (sub_ne_zero.mpr hne)
        rw [hzero] at hpos
        exact absurd hpos (lt_irrefl 0)
      rw [hAeq] at hAder
      simpa only [Work.Diff.EXT.dirF] using hAder
    let H : ℝ → (E →ₗ[ℝ] ℝ) := fun s =>
      { toFun := fun w : E =>
          Work.Diff.EXT.Kpt (G s) y k (Function.update (fun i => F' i y) j w)
        map_add' := fun a b =>
          Work.Diff.EXT.Kpt_add (I := I) (M := M) hLC (G s) y k (fun i => F' i y) j a b
        map_smul' := fun c a =>
          Work.Diff.EXT.Kpt_smul (I := I) (M := M) hLC (G s) y k (fun i => F' i y) j c a }
    have hHapply : ∀ (s : ℝ) (w : E),
        H s w = Work.Diff.EXT.ckt (G s) k
          (Function.update F' j (Submission.Diff.smoothExt y w)) y := by
      intro s w
      exact Work.Diff.EXT.kpt_eq_ckt_update (I := I) (M := M) hLC (G s) y hF's j w
    have hbasis : ∀ i : Fin (Module.finrank ℝ E),
        HasDerivAt (fun s : ℝ => H s (Module.finBasis ℝ E i))
          (deriv (fun s : ℝ => H s (Module.finBasis ℝ E i)) t) t := by
      intro i
      have hU : ∀ i', Work.Diff.EXT.SmoothTField (I := I) (M := M)
          ((Function.update F' j (Submission.Diff.smoothExt y (Module.finBasis ℝ E i))) i') :=
        Work.Diff.EXT.smoothF_update hF's
          (Work.Diff.GE.smoothExt_cmdiff y (Module.finBasis ℝ E i))
      have hdd := Work.Diff.EXT.hasDerivAt_ckt_family (I := I) (M := M) hLC hflow ht hU y
      have hfun : (fun s : ℝ => H s (Module.finBasis ℝ E i))
          = fun s => Work.Diff.EXT.ckt (G s) k
              (Function.update F' j (Submission.Diff.smoothExt y (Module.finBasis ℝ E i))) y :=
        funext (fun s => hHapply s (Module.finBasis ℝ E i))
      rw [hfun]
      exact hdd
    have hmain : HasDerivAt (fun s : ℝ => H s (Work.Diff.EXT.dirF (G s) (F' j) (F 0) y))
        (H t (Av j) + deriv (fun s : ℝ => H s (Work.Diff.EXT.dirF (G t) (F' j) (F 0) y)) t) t :=
      Work.Diff.EXT.hasDerivAt_linMap_apply_family (E := E) (L := H)
        (V := fun s => (Work.Diff.EXT.dirF (G s) (F' j) (F 0) y : E))
        (v := (Av j : E)) hVj hbasis
    have hfunQ : (fun s : ℝ => Work.Diff.EXT.ckt (G s) k
          (Function.update F' j (Work.Diff.EXT.dirF (G s) (F' j) (F 0))) y)
        = fun s => H s (Work.Diff.EXT.dirF (G s) (F' j) (F 0) y) := by
      funext s
      rw [hHapply s (Work.Diff.EXT.dirF (G s) (F' j) (F 0) y)]
      exact Work.Diff.EXT.ckt_update_eq_constant (I := I) (M := M) hLC (G s) y hF's j
        (Work.Diff.EXT.dirF_smooth (I := I) (M := M) hLC (G s) (hF's j) (hF 0))
    rw [hfunQ]
    have heta : (fun z : M => Submission.Diff.smoothExt y (Av j) z)
        = Submission.Diff.smoothExt y (Av j) := by
      funext z; rfl
    have hval1 : H t (Av j) = Work.Diff.EXT.ckt (G t) k
        (Function.update F' j (fun z : M => Submission.Diff.smoothExt y (Av j) z)) y :=
      (hHapply t (Av j)).trans (congrArg (fun g => Work.Diff.EXT.ckt (G t) k
        (Function.update F' j g) y) heta).symm
    have hval2 : deriv (fun s : ℝ => H s (Work.Diff.EXT.dirF (G t) (F' j) (F 0) y)) t
        = deriv (fun s' : ℝ => Work.Diff.EXT.ckt (G s') k
            (Function.update F' j (Work.Diff.EXT.dirF (G t) (F' j) (F 0))) y) t := by
      congr 1
      funext s
      rw [hHapply s (Work.Diff.EXT.dirF (G t) (F' j) (F 0) y)]
      exact (Work.Diff.EXT.ckt_update_eq_constant (I := I) (M := M) hLC (G s) y hF's j
        (Work.Diff.EXT.dirF_smooth (I := I) (M := M) hLC (G t) (hF's j) (hF 0))).symm
    have hval : H t (Av j) + deriv (fun s : ℝ => H s (Work.Diff.EXT.dirF (G t) (F' j) (F 0) y)) t
        = deriv (fun s' : ℝ => Work.Diff.EXT.ckt (G s') k
            (Function.update F' j (Work.Diff.EXT.dirF (G t) (F' j) (F 0))) y) t
          + Work.Diff.EXT.ckt (G t) k
              (Function.update F' j (fun z : M => Submission.Diff.smoothExt y (Av j) z)) y :=
      (congrArg₂ (fun a b : ℝ => a + b) hval1 hval2).trans (add_comm _ _)
    exact hmain.congr_deriv hval
  -- ## assembly
  have hQs : HasDerivAt (fun s : ℝ => ∑ j : Fin (k + 4), Work.Diff.EXT.ckt (G s) k
        (Function.update F' j (Work.Diff.EXT.dirF (G s) (F' j) (F 0))) y)
      (∑ j : Fin (k + 4), (deriv (fun s' : ℝ => Work.Diff.EXT.ckt (G s') k
            (Function.update F' j (Work.Diff.EXT.dirF (G t) (F' j) (F 0))) y) t
          + Work.Diff.EXT.ckt (G t) k
              (Function.update F' j (fun z : M => Submission.Diff.smoothExt y (Av j) z)) y)) t := by
    let A : Fin (k + 4) → ℝ → ℝ := fun j s => Work.Diff.EXT.ckt (G s) k
      (Function.update F' j (Work.Diff.EXT.dirF (G s) (F' j) (F 0))) y
    let A' : Fin (k + 4) → ℝ := fun j => deriv (fun s' : ℝ => Work.Diff.EXT.ckt (G s') k
          (Function.update F' j (Work.Diff.EXT.dirF (G t) (F' j) (F 0))) y) t
        + Work.Diff.EXT.ckt (G t) k
            (Function.update F' j (fun z : M => Submission.Diff.smoothExt y (Av j) z)) y
    have hsum := HasDerivAt.sum (u := Finset.univ) (A := A) (A' := A') (fun j _ => hQ j)
    refine hsum.congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall (fun s => (Finset.sum_apply s Finset.univ A).symm)
  have hDval : ((mvfderiv I (fun y' : M => deriv (fun s : ℝ => Work.Diff.EXT.ckt (G s) k F' y') t)
          y) (F 0 y))
        - ∑ j : Fin (k + 4), (deriv (fun s' : ℝ => Work.Diff.EXT.ckt (G s') k
              (Function.update F' j (Work.Diff.EXT.dirF (G t) (F' j) (F 0))) y) t
            + Work.Diff.EXT.ckt (G t) k
              (Function.update F' j (fun z : M => Submission.Diff.smoothExt y (Av j) z)) y)
      = (((mvfderiv I (fun y' : M => deriv (fun s : ℝ => Work.Diff.EXT.ckt (G s) k F' y') t)
            y) (F 0 y))
          - ∑ j : Fin (k + 4), deriv (fun s' : ℝ => Work.Diff.EXT.ckt (G s') k
              (Function.update F' j (Work.Diff.EXT.dirF (G t) (F' j) (F 0))) y) t)
        - ∑ j : Fin (k + 4), Work.Diff.EXT.ckt (G t) k
              (Function.update F' j (fun z : M => Submission.Diff.smoothExt y (Av j) z)) y := by
    rw [Finset.sum_add_distrib]
    ring
  have hall : HasDerivAt (fun s : ℝ => (mvfderiv I (Work.Diff.EXT.ckt (G s) k F') y) (F 0 y)
        - ∑ j : Fin (k + 4), Work.Diff.EXT.ckt (G s) k
            (Function.update F' j (Work.Diff.EXT.dirF (G s) (F' j) (F 0))) y)
      ( (((mvfderiv I (fun y' : M => deriv (fun s : ℝ => Work.Diff.EXT.ckt (G s) k F' y') t) y)
            (F 0 y))
          - ∑ j : Fin (k + 4), deriv (fun s' : ℝ => Work.Diff.EXT.ckt (G s') k
              (Function.update F' j (Work.Diff.EXT.dirF (G t) (F' j) (F 0))) y) t)
        - ∑ j : Fin (k + 4), Work.Diff.EXT.ckt (G t) k
              (Function.update F' j (fun z : M => Submission.Diff.smoothExt y (Av j) z)) y) t :=
    (hP.sub hQs).congr_deriv hDval
  have hkey : ∀ s : ℝ, Work.Diff.EXT.ckt (G s) (k + 1) F y
      = (mvfderiv I (Work.Diff.EXT.ckt (G s) k F') y) (F 0 y)
        - ∑ j : Fin (k + 4), Work.Diff.EXT.ckt (G s) k
            (Function.update F' j (Work.Diff.EXT.dirF (G s) (F' j) (F 0))) y := by
    intro s
    rw [Work.Diff.EXT.ckt_succ]
    simp only [Pi.sub_apply, Finset.sum_apply, hF'def]
  have hall2 := hall.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun s => hkey s))
  rw [hF'def] at hall2
  exact hall2

end Work.Diff.EXT
