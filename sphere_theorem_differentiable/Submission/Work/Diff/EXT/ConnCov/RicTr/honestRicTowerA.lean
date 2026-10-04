import Mathlib
import Submission.Work.Diff.EXT.ConnCov.FlipKit
import Submission.Work.Diff.EXT.ATower.connDiff_flip_input
import Submission.Work.Diff.EXT.covKRmExt_eval_bound
import Submission.Work.Diff.EXT.covKRmExt_tensorial
import Submission.Work.Diff.EXT.covK_familySmooth
import Submission.Work.Diff.GE.ricAt_eq_sum_frame
import Submission.Work.Diff.GE.covRic_eq_sum_covRm
import Submission.Work.Diff.GE.ExtTensor
import Submission.Work.Diff.EXT.covK_linear

/-!
# The `k`-th order Shi-type bound for the *honest* tower of the Ricci tensor (import land A)

This module proves `Work.Diff.EXT.ConnCov.RicTr.honestRicTowerA`: the uniform bound on the honest
towers `∇^{G t, j}Ric` (`j ≤ k+1`) along a Ricci flow on the collapsed slab `[T/2, T)`, with the
`∏ᵢ(1+√⟨vᵢ,vᵢ⟩)` shape in the direction slots.

The statement is the same as that of the sibling module
`Submission/Work/Diff/EXT/ConnCov/RicTr/honestRicTowerH.lean`; the point of *this* module is the
**import land**: it must not import the `RicTowerDefs`/`RicTowerKit` chain (`tower2`, `baseRic2`, …),
because `Work.Diff.EXT.ConnCov.ricTowerBound_fixed` (which needs the statement) lives in the
`deltaTower` chain and the two chains declare duplicate names (`Op2`, `vstep`, …), so no module may
import both.  Here the whole proof is carried out against the land-neutral vocabulary of

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
`Submission.Work.Diff.EXT.ConnCov.honestTower` (`htower`, `hstep`, `hstep_apply`, `cIndep_htower`,
`cIndep_baseRic`) and of `Submission.Work.Diff.EXT.ConnCov.FlipKit`.

## Route

1. **The trace identity** (`hrtA_htower_eq_trace_of_cancel`): for a smooth field family `W` which is
   `g`-orthonormal on an open set `U`, the honest Ricci tower is the metric trace of the curvature
   tower,

   `htower (lcOf g) (baseRic g) j v A B C y = Σ_m ∇^{g,j}Rm(v, W_m, A, W_m, B)(y)`  (`y ∈ U`).

   The induction step is exactly the `(0,2)`-tower induction of
   `tower2_eq_trace_of_cancel`: the honest recursion `hstep_apply` (for the third-slot independent
   object `htower (lcOf g) (baseRic g) j`) has the same shape as the `(0,2)`-recursion, so the only
   extra terms produced by the curvature recursion are the **two frame-derivative** corrections
   `Σ_m ∇^jRm(v, ∇_{v₀}W_m, A, W_m, B) + Σ_m ∇^jRm(v, W_m, A, ∇_{v₀}W_m, B)`, which vanish: in an
   orthonormal frame `∇_{v₀}W_m = Σ_p c_{mp}W_p` with `c` skew (`∇g = 0`), so the correction is
   `Σ_{m,p} c_{mp}(F_{p,m} + F_{m,p}) = 0` for *any* `F`.  This is the `(0,j+4)`-tensor lift of
   `Work.Diff.GE.covRic_frame_correction_zero`, taken here as the hypothesis `hcan` (the requester's
   input).

2. **The estimate**: evaluating the trace identity on the orthonormal frame field `katoFrame (G t) x`
   of `smoothExt x (onFrame (G t) x)`, and using the evaluation bound
   `Work.Diff.EXT.covKRmExt_eval_bound` for `∇^jRm` (Hilbert–Schmidt in an orthonormal frame)
   together with Shi's estimate `hShi`, bounds the right-hand side uniformly in `t`, at every level
   `j ≤ k+1`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Work.Diff.EXT.ATower

namespace Work.Diff.EXT.ConnCov.RicTr

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-! ## Local analytic tools -/

private theorem hrtA_mvfderiv_germ {f h : M → ℝ} {x : M} (hfh : f =ᶠ[𝓝 x] h) :
    mvfderiv I f x = mvfderiv I h x := by
  rw [mvfderiv, mvfderiv, hfh.eq_of_nhds, Filter.EventuallyEq.mfderiv_eq hfh]
  all_goals first | rfl | (ext v; rfl)

private theorem hrtA_mvfderiv_univ_sum {ι : Type*} [Fintype ι] (f : ι → M → ℝ) (x : M)
    (v : TangentSpace I x) (h : ∀ i, MDifferentiableAt I 𝓘(ℝ, ℝ) (f i) x) :
    mvfderiv I (fun y => ∑ i, f i y) x v = ∑ i, mvfderiv I (f i) x v := by
  classical
  have hdiff : ∀ t : Finset ι, MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => ∑ i ∈ t, f i y) x := by
    intro t
    refine (MDifferentiableAt.sum (t := t) (f := f) (fun i _ => h i)).congr_of_eventuallyEq ?_
    filter_upwards with y
    rw [Finset.sum_apply]
  have key : ∀ s : Finset ι,
      mvfderiv I (fun y => ∑ i ∈ s, f i y) x v = ∑ i ∈ s, mvfderiv I (f i) x v := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [show (fun y : M => ∑ i ∈ (∅ : Finset ι), f i y) = (fun _ : M => (0 : ℝ)) from by
        funext y; simp]
      rw [mvfderiv_const]
      simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      rw [show (fun y : M => ∑ i ∈ insert a s, f i y)
          = ((f a) + (fun y : M => ∑ i ∈ s, f i y)) from by
            funext y; rw [Finset.sum_insert ha]; rfl]
      rw [mvfderiv_add (h a) (hdiff s), add_apply, ih]
  simpa using key Finset.univ

private theorem hrtA_dirF_eq (g : SMet I M) (X v0 : Π y : M, TangentSpace I y) :
    dirF g X v0 = (fun y : M => lcOf g X y (v0 y)) := rfl

private theorem hrtA_curvNormK_nonneg' (g : SMet I M) (x : M) (k : ℕ) : 0 ≤ curvNormK g x k := by
  simp only [curvNormK]
  exact Finset.sum_nonneg fun ι _ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun m _ => sq_nonneg _

private theorem hrtA_sqrt_le_one_add' {x : ℝ} (hx : 0 ≤ x) : Real.sqrt x ≤ 1 + x := by
  have h1 : Real.sqrt x * Real.sqrt x = x := by
    rw [← pow_two]; exact Real.sq_sqrt hx
  nlinarith [Real.sqrt_nonneg x]

/-! ## The trace identity: the honest Ricci tower is the metric trace of the curvature tower -/

/-- **The honest `(0,2)`-tower of the Ricci tensor is the metric trace of the curvature tower.**
For a smooth field family `W` which is `g`-orthonormal on the open set `U`,

`htower (lcOf g) (baseRic g) j v A B C y = Σ_m ∇^{g,j}Rm(v, W_m, A, W_m, B)(y)`  for `y ∈ U`.

The hypothesis `hcan` is the frame-derivative cancellation (the requester's input); it is supplied,
in the application, by `Work.Diff.EXT.ConnCov.covKRmExt_frame_correction_zero`. -/
theorem hrtA_htower_eq_trace_of_cancel
    (hcan : ∀ (g : Submission.Diff.SMet I M) (x : M) (j : ℕ)
      (v : Fin j → (Π y : M, TangentSpace I y)) (v0 A B : Π y : M, TangentSpace I y)
      (W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y)),
      (∀ i, Work.Diff.EXT.ATower.SmE I M (v i)) → Work.Diff.EXT.ATower.SmE I M v0 →
      Work.Diff.EXT.ATower.SmE I M A → Work.Diff.EXT.ATower.SmE I M B →
      (∀ m, Work.Diff.EXT.ATower.SmE I M (W m)) →
      (∀ᶠ y in nhds x, Submission.Diff.IsONFrame g y (fun m => W m y)) →
      (Finset.univ.sum (fun m => Work.Diff.EXT.covKRmExt g j v (Work.Diff.EXT.dirF g (W m) v0) A (W m) B x))
        + (Finset.univ.sum (fun m => Work.Diff.EXT.covKRmExt g j v (W m) A (Work.Diff.EXT.dirF g (W m) v0) B x)) = 0)
    [I.Boundaryless]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y)) (hW : ∀ m, SmE I M (W m))
    (U : Set M) (hU : IsOpen U) (hON : ∀ y ∈ U, IsONFrame g y (fun m => W m y)) :
    ∀ (j : ℕ) (v : Fin j → (Π y : M, TangentSpace I y)) (A B C : Π y : M, TangentSpace I y),
      (∀ i, SmE I M (v i)) → SmE I M A → SmE I M B → SmE I M C → ∀ y ∈ U,
      htower (lcOf g) (baseRic g) j v A B C y
        = ∑ m, covKRmExt g j v (W m) A (W m) B y := by
  intro j
  induction j with
  | zero =>
    intro v A B C hv hA hB hC y hy
    simp only [htower_zero, baseRic, covKRmExt]
    exact Work.Diff.GE.ricAt_eq_sum_frame (I := I) (M := M) hLC g y (fun m => W m y)
      (hON y hy) (A y) (B y)
  | succ j ih =>
    intro v A B C hv hA hB hC y hy
    -- smoothness of the shifted tuple and of the correction fields
    have hv' : ∀ i : Fin j, SmE I M (v i.succ) := fun i => hv i.succ
    have hv0 : SmE I M (v 0) := hv 0
    have hdirA : SmE I M (fun z : M => lcOf g A z (v 0 z)) :=
      Work.Diff.EXT.ATower.lcOf_apply_smE hLC g A (v 0) hA hv0
    have hdirB : SmE I M (fun z : M => lcOf g B z (v 0 z)) :=
      Work.Diff.EXT.ATower.lcOf_apply_smE hLC g B (v 0) hB hv0
    have hdirv : ∀ i : Fin j, SmE I M (fun z : M => lcOf g (v i.succ) z (v 0 z)) :=
      fun i => Work.Diff.EXT.ATower.lcOf_apply_smE hLC g (v i.succ) (v 0) (hv i.succ) hv0
    have hdirW : ∀ m, SmE I M (fun z : M => lcOf g (W m) z (v 0 z)) :=
      fun m => Work.Diff.EXT.ATower.lcOf_apply_smE hLC g (W m) (v 0) (hW m) hv0
    -- the induction hypothesis, as a germ at `y`
    have hih : (htower (lcOf g) (baseRic g) j (fun i : Fin j => v i.succ) A B C)
        =ᶠ[𝓝 y] (fun z => ∑ m, covKRmExt g j (fun i : Fin j => v i.succ) (W m) A (W m) B z) := by
      filter_upwards [hU.mem_nhds hy] with z hz
      exact ih (fun i : Fin j => v i.succ) A B C hv' hA hB hC z hz
    have hderiv : mvfderiv I (htower (lcOf g) (baseRic g) j (fun i : Fin j => v i.succ) A B C)
          y (v 0 y)
        = mvfderiv I (fun z => ∑ m, covKRmExt g j (fun i : Fin j => v i.succ) (W m) A (W m) B z)
            y (v 0 y) :=
      congrArg (fun L : TangentSpace I y →L[ℝ] ℝ => L (v 0 y)) (hrtA_mvfderiv_germ hih)
    -- the sum over the differentiation slots of the honest recursion
    have hsum_i : (∑ i : Fin j, htower (lcOf g) (baseRic g) j
          (Function.update (fun j : Fin j => v j.succ) i (fun y => lcOf g (v i.succ) y (v 0 y)))
          A B C y)
        = ∑ i : Fin j, ∑ m, covKRmExt g j
            (Function.update (fun j : Fin j => v j.succ) i
              (fun y => lcOf g (v i.succ) y (v 0 y))) (W m) A (W m) B y := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      exact ih (Function.update (fun j : Fin j => v j.succ) i
          (fun y => lcOf g (v i.succ) y (v 0 y))) A B C
        (fun l => by
          by_cases hl : l = i
          · rw [hl, Function.update_self]; exact hdirv i
          · rw [Function.update_of_ne hl]; exact hv l.succ)
        hA hB hC y hy
    have hAcorr : htower (lcOf g) (baseRic g) j (fun i : Fin j => v i.succ)
        (fun y => lcOf g A y (v 0 y)) B C y
        = ∑ m, covKRmExt g j (fun i : Fin j => v i.succ) (W m) (fun y => lcOf g A y (v 0 y))
            (W m) B y :=
      ih (fun i : Fin j => v i.succ) (fun y => lcOf g A y (v 0 y)) B C hv' hdirA hB hC y hy
    have hBcorr : htower (lcOf g) (baseRic g) j (fun i : Fin j => v i.succ) A
        (fun y => lcOf g B y (v 0 y)) C y
        = ∑ m, covKRmExt g j (fun i : Fin j => v i.succ) (W m) A (W m)
            (fun y => lcOf g B y (v 0 y)) y :=
      ih (fun i : Fin j => v i.succ) A (fun y => lcOf g B y (v 0 y)) C hv' hA hdirB hC y hy
    -- the frame-derivative cancellation
    have hONev : ∀ᶠ z in 𝓝 y, IsONFrame g z (fun m => W m z) :=
      Filter.mem_of_superset (hU.mem_nhds hy) (fun z hz => hON z hz)
    have hF : (∑ m, covKRmExt g j (fun i : Fin j => v i.succ) (dirF g (W m) (v 0)) A (W m) B y)
        + (∑ m, covKRmExt g j (fun i : Fin j => v i.succ) (W m) A (dirF g (W m) (v 0)) B y) = 0 :=
      hcan g y j (fun i : Fin j => v i.succ) (v 0) A B W hv' hv0 hA hB hW hONev
    have hF' : (∑ m, covKRmExt g j (fun i : Fin j => v i.succ)
          (fun y => lcOf g (W m) y (v 0 y)) A (W m) B y)
        + (∑ m, covKRmExt g j (fun i : Fin j => v i.succ) (W m) A
          (fun y => lcOf g (W m) y (v 0 y)) B y) = 0 := by
      simpa only [hrtA_dirF_eq] using hF
    -- unfold the right-hand side
    have hR1 : (∑ m, covKRmExt g (j + 1) v (W m) A (W m) B y)
        = ∑ m, (mvfderiv I (covKRmExt g j (fun i : Fin j => v i.succ) (W m) A (W m) B) y (v 0 y)
            - (∑ i : Fin j, covKRmExt g j (Function.update (fun j : Fin j => v j.succ) i
                (fun y => lcOf g (v i.succ) y (v 0 y))) (W m) A (W m) B y)
            - covKRmExt g j (fun i : Fin j => v i.succ) (fun y => lcOf g (W m) y (v 0 y))
                A (W m) B y
            - covKRmExt g j (fun i : Fin j => v i.succ) (W m) (fun y => lcOf g A y (v 0 y))
                (W m) B y
            - covKRmExt g j (fun i : Fin j => v i.succ) (W m) A
                (fun y => lcOf g (W m) y (v 0 y)) B y
            - covKRmExt g j (fun i : Fin j => v i.succ) (W m) A (W m)
                (fun y => lcOf g B y (v 0 y)) y) := by
      refine Finset.sum_congr rfl (fun m _ => ?_)
      simp only [covKRmExt]
    have hR2 : (∑ m, (mvfderiv I (covKRmExt g j (fun i : Fin j => v i.succ) (W m) A (W m) B)
              y (v 0 y)
            - (∑ i : Fin j, covKRmExt g j (Function.update (fun j : Fin j => v j.succ) i
                (fun y => lcOf g (v i.succ) y (v 0 y))) (W m) A (W m) B y)
            - covKRmExt g j (fun i : Fin j => v i.succ) (fun y => lcOf g (W m) y (v 0 y))
                A (W m) B y
            - covKRmExt g j (fun i : Fin j => v i.succ) (W m) (fun y => lcOf g A y (v 0 y))
                (W m) B y
            - covKRmExt g j (fun i : Fin j => v i.succ) (W m) A
                (fun y => lcOf g (W m) y (v 0 y)) B y
            - covKRmExt g j (fun i : Fin j => v i.succ) (W m) A (W m)
                (fun y => lcOf g B y (v 0 y)) y))
        = (∑ m, mvfderiv I (covKRmExt g j (fun i : Fin j => v i.succ) (W m) A (W m) B) y (v 0 y))
          - (∑ m, ∑ i : Fin j, covKRmExt g j (Function.update (fun j : Fin j => v j.succ) i
              (fun y => lcOf g (v i.succ) y (v 0 y))) (W m) A (W m) B y)
          - (∑ m, covKRmExt g j (fun i : Fin j => v i.succ) (fun y => lcOf g (W m) y (v 0 y))
              A (W m) B y)
          - (∑ m, covKRmExt g j (fun i : Fin j => v i.succ) (W m) (fun y => lcOf g A y (v 0 y))
              (W m) B y)
          - (∑ m, covKRmExt g j (fun i : Fin j => v i.succ) (W m) A
              (fun y => lcOf g (W m) y (v 0 y)) B y)
          - (∑ m, covKRmExt g j (fun i : Fin j => v i.succ) (W m) A (W m)
              (fun y => lcOf g B y (v 0 y)) y) := by
      simp only [Finset.sum_sub_distrib]
    have hderivR : (∑ m, mvfderiv I (covKRmExt g j (fun i : Fin j => v i.succ) (W m) A (W m) B)
          y (v 0 y))
        = mvfderiv I (fun z => ∑ m, covKRmExt g j (fun i : Fin j => v i.succ) (W m) A (W m) B z)
            y (v 0 y) := by
      refine (hrtA_mvfderiv_univ_sum
        (fun m => fun z => covKRmExt g j (fun i : Fin j => v i.succ) (W m) A (W m) B z)
        y (v 0 y) ?_).symm
      intro m
      exact (Work.Diff.EXT.covK_fixedSmooth (I := I) (M := M) hLC g j
        (V := fun i : Fin j => v i.succ) hv' (A := W m) (B := A) (C := W m) (D := B)
        (hW m) hA (hW m) hB).mdifferentiableAt (by simp)
    -- the two sides of the recursion
    have hL : htower (lcOf g) (baseRic g) (j + 1) v A B C y
        = mvfderiv I (fun z => ∑ m, covKRmExt g j (fun i : Fin j => v i.succ) (W m) A (W m) B z)
            y (v 0 y)
          - (∑ i : Fin j, ∑ m, covKRmExt g j (Function.update (fun j : Fin j => v j.succ) i
              (fun y => lcOf g (v i.succ) y (v 0 y))) (W m) A (W m) B y)
          - (∑ m, covKRmExt g j (fun i : Fin j => v i.succ) (W m) (fun y => lcOf g A y (v 0 y))
              (W m) B y)
          - (∑ m, covKRmExt g j (fun i : Fin j => v i.succ) (W m) A (W m)
              (fun y => lcOf g B y (v 0 y)) y) := by
      rw [htower_succ, hstep_apply (lcOf g)
        (cIndep_htower (lcOf g) (cIndep_baseRic g) j)]
      rw [hderiv, hsum_i, hAcorr, hBcorr]
    have hR : (∑ m, covKRmExt g (j + 1) v (W m) A (W m) B y)
        = mvfderiv I (fun z => ∑ m, covKRmExt g j (fun i : Fin j => v i.succ) (W m) A (W m) B z)
            y (v 0 y)
          - (∑ i : Fin j, ∑ m, covKRmExt g j (Function.update (fun j : Fin j => v j.succ) i
              (fun y => lcOf g (v i.succ) y (v 0 y))) (W m) A (W m) B y)
          - (∑ m, covKRmExt g j (fun i : Fin j => v i.succ) (W m) (fun y => lcOf g A y (v 0 y))
              (W m) B y)
          - (∑ m, covKRmExt g j (fun i : Fin j => v i.succ) (W m) A (W m)
              (fun y => lcOf g B y (v 0 y)) y) := by
      rw [hR1, hR2, hderivR, Finset.sum_comm]
      linarith [hF']
    rw [hL, hR]

/-! ## The target -/

theorem honestRicTowerA
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hcan : ∀ (g : Submission.Diff.SMet I M) (x : M) (j : ℕ)
      (v : Fin j → (Π y : M, TangentSpace I y)) (v0 A B : Π y : M, TangentSpace I y)
      (W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y)),
      (∀ i, Work.Diff.EXT.ATower.SmE I M (v i)) → Work.Diff.EXT.ATower.SmE I M v0 →
      Work.Diff.EXT.ATower.SmE I M A → Work.Diff.EXT.ATower.SmE I M B →
      (∀ m, Work.Diff.EXT.ATower.SmE I M (W m)) →
      (∀ᶠ y in nhds x, Submission.Diff.IsONFrame g y (fun m => W m y)) →
      (Finset.univ.sum (fun m => Work.Diff.EXT.covKRmExt g j v (Work.Diff.EXT.dirF g (W m) v0) A (W m) B x))
        + (Finset.univ.sum (fun m => Work.Diff.EXT.covKRmExt g j v (W m) A (Work.Diff.EXT.dirF g (W m) v0) B x)) = 0)
    (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (T C : ℝ) (hT : 0 < T) (hC : 0 ≤ C)
    (hflow : Submission.Diff.IsRicciFlow G T)
    (hbound : ∀ t ∈ Set.Ico 0 T, Submission.Diff.CurvBound (G t) C)
    (hmet : ∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ u : TangentSpace I x,
      (G t).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G 0).inner x u u ∧
      (G 0).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G t).inner x u u)
    (hShi : Work.Diff.EXT.ShiBounds (I := I) (M := M)) (k : ℕ) :
    ∃ Ck : ℝ, 0 ≤ Ck ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ j : ℕ, j ≤ k + 1 → ∀ x : M,
      ∀ (v : Fin j → TangentSpace I x) (a b c : TangentSpace I x),
        |Work.Diff.EXT.ATower.valOp
            (Work.Diff.EXT.ConnCov.htower (Submission.Diff.lcOf (G t))
              (Work.Diff.EXT.ConnCov.baseRic (G t)) j) x v a b c|
          ≤ Ck * (Finset.univ.prod (fun i : Fin j => (1 + Real.sqrt ((G t).inner x (v i) (v i)))))
              * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b) := by
  -- Shi's estimate: a uniform bound for the geometric curvature norms on `[T/2, T)`
  have hshi : ∀ j : ℕ, ∃ S : ℝ, ∀ t ∈ Set.Ico (T / 2) T, ∀ x : M, curvNormK (G t) x j ≤ S :=
    fun j => hShi G T C (T / 2) hT hflow hbound (by linarith) (by linarith) j
  choose S hS using hshi
  -- the evaluation bound for `∇^j Rm`
  choose Ec hE using fun j : ℕ =>
    (Work.Diff.EXT.covKRmExt_eval_bound (I := I) (M := M) hLC j)
  -- the uniform constant
  set K : ℝ := (∑ i ∈ Finset.range (k + 2), (1 + |S i| + Ec i)) + 1 with hKdef
  have hKsum_nonneg : 0 ≤ ∑ i ∈ Finset.range (k + 2), (1 + |S i| + Ec i) :=
    Finset.sum_nonneg (fun i _ => by have h1 := abs_nonneg (S i); have h2 := (hE i).1; linarith)
  have hKpos : 1 ≤ K := by rw [hKdef]; linarith
  refine ⟨(Module.finrank ℝ E : ℝ) * (K * K), ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
    nlinarith [h1, hKpos]
  · intro t ht j hj x v a b c
    have hmem : j ∈ Finset.range (k + 2) := Finset.mem_range.mpr (by omega)
    -- the orthonormal frame field at `x`
    set V : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y) :=
      fun m => smoothExt x (onFrame (G t) x m) with hVdef
    set W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y) :=
      Work.Diff.GE.katoFrame (G t) x V with hWdef
    have hVs : ∀ i, SmE I M (V i) := fun i => Work.Diff.GE.smoothExt_cmdiff x _
    have hVON : IsONFrame (G t) x (fun i => V i x) := by
      rw [hVdef]
      simp only [Work.Diff.GE.smoothExt_apply]
      exact Work.Diff.GE.isONFrame_onFrame (G t) x
    obtain ⟨hWs, hWON, hWx⟩ :=
      Work.Diff.GE.covRic_onFrame_family (I := I) (M := M) (G t) x V hVs hVON
    have hWs' : ∀ m, SmE I M (W m) := fun m => hWs m
    obtain ⟨U, ⟨hxU, hUo⟩, hUsU⟩ :=
      (nhds_basis_opens x).mem_iff.mp (Filter.eventually_iff.mp hWON)
    have hONU : ∀ y ∈ U, IsONFrame (G t) y (fun m => W m y) := fun y hy => hUsU hy
    -- the trace identity at `x`
    have htr := hrtA_htower_eq_trace_of_cancel (I := I) (M := M) hcan hLC (G t) W hWs' U hUo hONU j
      (fun i => smoothExt x (v i)) (smoothExt x a) (smoothExt x b) (smoothExt x c)
      (fun i => Work.Diff.GE.smoothExt_cmdiff x (v i))
      (Work.Diff.GE.smoothExt_cmdiff x a) (Work.Diff.GE.smoothExt_cmdiff x b)
      (Work.Diff.GE.smoothExt_cmdiff x c) x hxU
    have hval : valOp (htower (lcOf (G t)) (baseRic (G t)) j) x v a b c
        = ∑ m, covKRmExt (G t) j (fun i => smoothExt x (v i)) (W m) (smoothExt x a) (W m)
            (smoothExt x b) x := by
      simp only [valOp]
      exact htr
    -- the frame is orthonormal at `x`
    have hgeom : ∀ m, (G t).inner x (W m x) (W m x) = 1 := by
      intro m
      have h1 := Work.Diff.GE.isONFrame_onFrame (G t) x m m
      have h2 : W m x = onFrame (G t) x m := by
        rw [hWdef, hWx m, hVdef]
        exact Work.Diff.GE.smoothExt_apply x (onFrame (G t) x m)
      rw [h2]
      simpa using h1
    -- value dependence: replace the frame fields by their values at `x`
    have hstep : ∀ m, |covKRmExt (G t) j (fun i => smoothExt x (v i)) (W m) (smoothExt x a)
          (W m) (smoothExt x b) x|
        = |covKRmExt (G t) j (fun i => smoothExt x (v i)) (smoothExt x (W m x)) (smoothExt x a)
            (smoothExt x (W m x)) (smoothExt x b) x| := by
      intro m
      rw [Work.Diff.EXT.covKRmExt_tensorial (I := I) (M := M) hLC j (G t) x
        (fun i => smoothExt x (v i)) (fun i => smoothExt x (v i))
        (W m) (smoothExt x (W m x)) (smoothExt x a) (smoothExt x a)
        (W m) (smoothExt x (W m x)) (smoothExt x b) (smoothExt x b)
        (fun i => Work.Diff.GE.smoothExt_cmdiff x (v i))
        (fun i => Work.Diff.GE.smoothExt_cmdiff x (v i))
        (hWs' m) (Work.Diff.GE.smoothExt_cmdiff x (W m x))
        (Work.Diff.GE.smoothExt_cmdiff x a) (Work.Diff.GE.smoothExt_cmdiff x a)
        (hWs' m) (Work.Diff.GE.smoothExt_cmdiff x (W m x))
        (Work.Diff.GE.smoothExt_cmdiff x b) (Work.Diff.GE.smoothExt_cmdiff x b)
        (fun i => rfl) (Work.Diff.GE.smoothExt_apply x (W m x)).symm rfl
        (Work.Diff.GE.smoothExt_apply x (W m x)).symm rfl]
    have hbound_each : ∀ m, |covKRmExt (G t) j (fun i => smoothExt x (v i))
          (smoothExt x (W m x)) (smoothExt x a) (smoothExt x (W m x)) (smoothExt x b) x|
        ≤ Ec j * (1 + Real.sqrt (curvNormK (G t) x j))
          * ((Finset.univ.prod (fun i : Fin j => Real.sqrt ((G t).inner x (v i) (v i))))
              * 1 * Real.sqrt ((G t).inner x a a) * 1 * Real.sqrt ((G t).inner x b b)) := by
      intro m
      have h := (hE j).2 (G t) x v (W m x) a (W m x) b
      simpa only [hgeom m, Real.sqrt_one, mul_one] using h
    -- the constants
    have hEj : Ec j ≤ K := by
      have hle : Ec j ≤ 1 + |S j| + Ec j := by
        have h1 := abs_nonneg (S j); have h2 := (hE j).1; linarith
      have hsum := Finset.single_le_sum (f := fun i => 1 + |S i| + Ec i)
        (s := Finset.range (k + 2)) (fun i _ => by
          have h1 := abs_nonneg (S i); have h2 := (hE i).1; linarith) hmem
      rw [hKdef]; linarith
    have hcurv_le_Sj : curvNormK (G t) x j ≤ S j := hS j t ht x
    have hSj : curvNormK (G t) x j ≤ K := by
      have hle : S j ≤ 1 + |S j| + Ec j := by
        have h2 := abs_nonneg (S j); have h3 := (hE j).1
        have h4 := le_abs_self (S j); linarith
      have hsum := Finset.single_le_sum (f := fun i => 1 + |S i| + Ec i)
        (s := Finset.range (k + 2)) (fun i _ => by
          have h2 := abs_nonneg (S i); have h3 := (hE i).1; linarith) hmem
      rw [hKdef]; linarith
    have hsqrt_c : 1 + Real.sqrt (curvNormK (G t) x j) ≤ K := by
      have h1 : Real.sqrt (curvNormK (G t) x j) ≤ 1 + |S j| :=
        (Real.sqrt_le_sqrt (le_trans hcurv_le_Sj (le_abs_self _))).trans
          (hrtA_sqrt_le_one_add' (abs_nonneg (S j)))
      have h2 : 1 + |S j| ≤ ∑ i ∈ Finset.range (k + 2), (1 + |S i| + Ec i) := by
        have hle : 1 + |S j| ≤ 1 + |S j| + Ec j := by have h3 := (hE j).1; linarith
        exact hle.trans (Finset.single_le_sum (f := fun i => 1 + |S i| + Ec i)
          (s := Finset.range (k + 2)) (fun i _ => by
            have h3 := abs_nonneg (S i); have h4 := (hE i).1; linarith) hmem)
      rw [hKdef]
      linarith
    -- the products
    have hprod_sqrt_le : (Finset.univ.prod (fun i : Fin j =>
          Real.sqrt ((G t).inner x (v i) (v i))))
        ≤ Finset.univ.prod (fun i : Fin j => (1 + Real.sqrt ((G t).inner x (v i) (v i)))) :=
      Finset.prod_le_prod₀ (fun i _ => Real.sqrt_nonneg _) (fun i _ => by
        have h := Real.sqrt_nonneg ((G t).inner x (v i) (v i)); linarith)
    have hprod_sqrt_nonneg : 0 ≤ (Finset.univ.prod (fun i : Fin j =>
          Real.sqrt ((G t).inner x (v i) (v i)))) :=
      Finset.prod_nonneg (fun i _ => Real.sqrt_nonneg _)
    have haa : 0 ≤ Real.sqrt ((G t).inner x a a) := Real.sqrt_nonneg _
    have hbb : 0 ≤ Real.sqrt ((G t).inner x b b) := Real.sqrt_nonneg _
    have hc0 : 0 ≤ 1 + Real.sqrt (curvNormK (G t) x j) := by
      have h := Real.sqrt_nonneg (curvNormK (G t) x j); linarith
    calc |valOp (htower (lcOf (G t)) (baseRic (G t)) j) x v a b c|
        = |∑ m, covKRmExt (G t) j (fun i => smoothExt x (v i)) (W m) (smoothExt x a)
              (W m) (smoothExt x b) x| := by rw [hval]
      _ ≤ ∑ m, |covKRmExt (G t) j (fun i => smoothExt x (v i)) (W m) (smoothExt x a)
              (W m) (smoothExt x b) x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ m, Ec j * (1 + Real.sqrt (curvNormK (G t) x j))
              * ((Finset.univ.prod (fun i : Fin j => Real.sqrt ((G t).inner x (v i) (v i))))
                * 1 * Real.sqrt ((G t).inner x a a) * 1
                * Real.sqrt ((G t).inner x b b)) := by
          refine Finset.sum_le_sum (fun m _ => ?_)
          rw [hstep m]
          exact hbound_each m
      _ = (Module.finrank ℝ E : ℝ) * (Ec j * (1 + Real.sqrt (curvNormK (G t) x j))
              * ((Finset.univ.prod (fun i : Fin j => Real.sqrt ((G t).inner x (v i) (v i))))
                * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
      _ ≤ (Module.finrank ℝ E : ℝ) * (K * K
              * ((Finset.univ.prod (fun i : Fin j =>
                    (1 + Real.sqrt ((G t).inner x (v i) (v i)))))
                * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b))) := by
          have hKnn : 0 ≤ K := le_trans zero_le_one hKpos
          have hEE : Ec j * (1 + Real.sqrt (curvNormK (G t) x j)) ≤ K * K :=
            mul_le_mul hEj hsqrt_c hc0 hKnn
          have hfac : (Finset.univ.prod (fun i : Fin j =>
                Real.sqrt ((G t).inner x (v i) (v i))))
                * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b)
              ≤ (Finset.univ.prod (fun i : Fin j =>
                  (1 + Real.sqrt ((G t).inner x (v i) (v i)))))
                * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hprod_sqrt_le haa) hbb
          have h1 : Ec j * (1 + Real.sqrt (curvNormK (G t) x j))
                * ((Finset.univ.prod (fun i : Fin j =>
                      Real.sqrt ((G t).inner x (v i) (v i))))
                  * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b))
              ≤ K * K * ((Finset.univ.prod (fun i : Fin j =>
                      Real.sqrt ((G t).inner x (v i) (v i))))
                  * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b)) :=
            mul_le_mul_of_nonneg_right hEE
              (mul_nonneg (mul_nonneg hprod_sqrt_nonneg haa) hbb)
          have h2 : K * K * ((Finset.univ.prod (fun i : Fin j =>
                      Real.sqrt ((G t).inner x (v i) (v i))))
                  * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b))
              ≤ K * K * ((Finset.univ.prod (fun i : Fin j =>
                      (1 + Real.sqrt ((G t).inner x (v i) (v i)))))
                  * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b)) :=
            mul_le_mul_of_nonneg_left hfac (mul_nonneg hKnn hKnn)
          refine mul_le_mul_of_nonneg_left (le_trans h1 h2) (Nat.cast_nonneg _)
      _ = (Module.finrank ℝ E : ℝ) * (K * K)
              * Finset.univ.prod (fun i : Fin j =>
                  (1 + Real.sqrt ((G t).inner x (v i) (v i))))
              * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b) := by
          ring

end Work.Diff.EXT.ConnCov.RicTr
