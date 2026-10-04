import Mathlib
import Submission.Work.Diff.EXT.evolK_bridges
import Submission.Work.Diff.EXT.lapCovKRm_one_eq_lapCovRmAt
import Submission.Work.Diff.GE.covRm_frame_evol_abs
import Submission.Work.Diff.T.lc_smooth
import Submission.Work.Diff.GE.cov3Rm_ricci
import Submission.Work.Diff.GE.swap_ricci
import Submission.Work.Diff.GE.kato_cov3RmExt_field
import Submission.Work.Diff.GE.kato_covRm_field
import Submission.Work.Diff.EXT.curvNormK_frame_indep
import Submission.Work.Diff.GE.Gest.Base

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

/-!
# The `k = 1` base case of the componentwise evolution estimate (`EvolCompK 1`)

`Work.Diff.EXT.EvolCompK k` (`Submission/Work/Diff/EXT/evolKDefs.lean`) is the componentwise
evolution estimate for `∇^k Rm` in a moving orthonormal frame, the single remaining ingredient of
the verified assembly `evolK_of_pieces` (`Submission/Work/Diff/EXT/evolK_of_flow.lean`) that proves
`EvolK` from `EvolCompK` for all `k`.  At `k = 1` the analytic content is the GE-area result

`Work.Diff.GE.covRm_frame_evol_abs` : `∃ C ≥ 0` such that along every Ricci flow, for every frame
family `e` orthonormal for `G s` near `t`, with `⟨ėᵢ,ėᵢ⟩ ≤ K |Rm|²`, every component of `∇Rm`
satisfies `|D − Δ∇Rm-component| ≤ C(1+K)√|Rm|² √|∇Rm|²`.

The statement below takes exactly that result as a *hypothesis* `h` (so that it is independent of
the proof state of that result) and deduces `EvolCompK 1`.  The conversion is bookkeeping plus
elementary estimates, using the bridges in `Submission/Work/Diff/EXT/evolK_bridges.lean`:
`covKRm_one` identifies the components, `curvNormK_zero_eq_rmNormSq` / `curvNormK_one_eq_dRmNormSq`
identify the norms `f_0`, `f_1` with `rmNormSq` / `dRmNormSq`, and the rough-Laplacian components
are identified by `lapCovKRm_one_eq` below.  Finally `√f_0·√f_1 ≤ (1+f_0)(1+√f_1)`, so the GE bound
`C(1+K)√f_0√f_1` implies `EvolCompK 1`'s bound `C'(1+K)(1+Σ_{j<1}f_j)(1+√f_1)`.

## The identification of the rough Laplacians

`lapCovKRm_one_eq` (`lapCovKRm g x 1 v a b c d = lapCovRmAt g x v a b c d`) is the `k = 1` case of
the dictionary between the `EXT` tower `covKRmExt` and the `k = 1` tensors `covRm`/`cov2Rm`/`cov3Rm`
of the GE area.  It is proved here by running the tower `covKRmExt` in its `Ext`-pattern form: the
`k`-th iterate `Work.Diff.EXT.ckt` of the tuple recursion satisfies
`ckt g k (mkT v (rmPQuad A B C D)) y = covKRmExt g k v A B C D y` (the proved `ckt_mkT_eq`), and
`ckt g k` is the iterated `Ext`-derivative of the curvature tensor; the three levels `k ≤ 3` that
are needed here are identified with `covRm`, `cov2Rm`, `cov3Rm` by
`Work.Diff.GE.extD_rmPTensor`, `Work.Diff.GE.extD_covRmT`, `extD_cov2RmT` and the value dependence
of `cov2RmExt`/`cov3RmExt`.  The smoothness of the Levi-Civita connection used on the way is the
proved contract `Work.Diff.T.lc_smooth` (`LCSmooth I M` holds for every smooth metric).
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-! ## `∇²Rm` as a field-level tensor of arity `6` -/

/-- The `(0,6)`-tensor `∇²Rm` as a field-level tensor: `cov2RmT g G = (y ↦ cov2Rm g y (G 0 y) …
(G 5 y))`.  Companion of `Work.Diff.GE.covRmT` for the second derivative. -/
noncomputable def cov2RmT (g : Submission.Diff.SMet I M) :
    Work.Diff.GE.ExtTensor (I := I) (M := M) (Fin 6) :=
  fun G => fun y => Work.Diff.GE.cov2Rm g y (G 0 y) (G 1 y) (G 2 y) (G 3 y) (G 4 y) (G 5 y)

/-- Unfolding lemma for `cov2RmT`. -/
theorem cov2RmT_apply (g : Submission.Diff.SMet I M)
    (G : Fin 6 → TField (I := I) (M := M)) (y : M) :
    cov2RmT g G y = Work.Diff.GE.cov2Rm g y (G 0 y) (G 1 y) (G 2 y) (G 3 y) (G 4 y) (G 5 y) :=
  rfl

/-- The first `Ext` derivative of `∇²Rm` is `∇³Rm`, evaluated on smooth fields. -/
theorem extD_cov2RmT (g : Submission.Diff.SMet I M) (x : M)
    (X : TField (I := I) (M := M)) (F : Fin 6 → TField (I := I) (M := M)) :
    Work.Diff.GE.extD (Submission.Diff.lcOf g) (cov2RmT g) x X F
      = Work.Diff.GE.cov3RmExt g x (X x) (F 0) (F 1) (F 2) (F 3) (F 4) (F 5) := by
  rw [Work.Diff.GE.extD_eq]
  rw [show cov2RmT g F = (fun y => Work.Diff.GE.cov2Rm g y (F 0 y) (F 1 y) (F 2 y) (F 3 y)
      (F 4 y) (F 5 y)) from rfl]
  simp only [Work.Diff.GE.cov3RmExt]
  rw [Fin.sum_univ_six]
  simp (config := { decide := true }) only [Work.Diff.GE.upd, cov2RmT_apply,
    Function.update_apply, Fin.isValue, reduceIte]
  ring

/-! ## The iterated `Ext` derivative in the `k ≤ 3` cases -/

/-- The first iterate: `∇Rm` on the values of the tuple. -/
theorem ckt_one_eq_covRm (hLC : Submission.Diff.LCSmooth I M)
    (g : Submission.Diff.SMet I M) (G : Fin 5 → TField (I := I) (M := M))
    (hG : ∀ i, CMDiff ∞ (T% (G i))) (y : M) :
    ckt g 1 G y
      = Submission.Diff.covRm g y (G 0 y) (G 1 y) (G 2 y) (G 3 y) (G 4 y) := by
  rw [show ckt g 1 G y
        = Work.Diff.GE.extD (Submission.Diff.lcOf g) (Work.Diff.GE.rmPTensor g) y (G 0)
            (fun i : Fin 4 => G i.succ) from rfl,
      Work.Diff.GE.extD_rmPTensor hLC g y (G 0) (hG 0) (fun i : Fin 4 => G i.succ)
        (fun i => hG i.succ)]
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    show (Fin.succ (2 : Fin 4)) = (3 : Fin 5) from by decide,
    show (Fin.succ (3 : Fin 4)) = (4 : Fin 5) from by decide]

/-- The second iterate: `∇²Rm` on the values of the tuple. -/
theorem ckt_two_eq_cov2Rm (hLC : Submission.Diff.LCSmooth I M)
    (g : Submission.Diff.SMet I M) (G : Fin 6 → TField (I := I) (M := M))
    (hG : ∀ i, CMDiff ∞ (T% (G i))) (y : M) :
    ckt g 2 G y
      = Work.Diff.GE.cov2Rm g y (G 0 y) (G 1 y) (G 2 y) (G 3 y) (G 4 y) (G 5 y) := by
  have hcov : Work.Diff.GE.CovSmooth (Submission.Diff.lcOf g) := (hLC g).1.some
  have htail : ∀ i : Fin 5, CMDiff ∞ (T% ((fun i : Fin 5 => G i.succ) i)) := fun i => hG i.succ
  have hupd : ∀ s : Fin 5,
      ∀ i, CMDiff ∞ (T% ((Work.Diff.GE.upd (Submission.Diff.lcOf g) (G 0)
        (fun i : Fin 5 => G i.succ) s) i)) := by
    intro s i
    simp only [Work.Diff.GE.upd, Function.update_apply]
    by_cases hi : i = s
    · rw [if_pos hi]
      exact Work.Diff.GE.cmdiff_covAlong (Submission.Diff.lcOf g) hcov (hG 0) (hG s.succ)
    · rw [if_neg hi]
      exact hG i.succ
  rw [show ckt g 2 G y
        = Work.Diff.GE.extD (Submission.Diff.lcOf g) (ckt g 1) y (G 0)
            (fun i : Fin 5 => G i.succ) from rfl]
  rw [show Work.Diff.GE.extD (Submission.Diff.lcOf g) (ckt g 1) y (G 0)
          (fun i : Fin 5 => G i.succ)
        = Work.Diff.GE.extD (Submission.Diff.lcOf g) (Work.Diff.GE.covRmT g) y (G 0)
            (fun i : Fin 5 => G i.succ) from by
      rw [Work.Diff.GE.extD_eq, Work.Diff.GE.extD_eq]
      rw [show (ckt g 1 (fun i : Fin 5 => G i.succ))
            = (Work.Diff.GE.covRmT g (fun i : Fin 5 => G i.succ)) from
          funext (fun y' => by
            rw [Work.Diff.GE.covRmT_apply]
            exact ckt_one_eq_covRm hLC g (fun i : Fin 5 => G i.succ) htail y')]
      rw [show (∑ s : Fin 5, ckt g 1 (Work.Diff.GE.upd (Submission.Diff.lcOf g)
              (G 0) (fun i : Fin 5 => G i.succ) s) y)
            = (∑ s : Fin 5, Work.Diff.GE.covRmT g (Work.Diff.GE.upd (Submission.Diff.lcOf g)
              (G 0) (fun i : Fin 5 => G i.succ) s) y) from
          Finset.sum_congr rfl (fun s _ => by
            rw [Work.Diff.GE.covRmT_apply]
            exact ckt_one_eq_covRm hLC g _ (hupd s) y)]]
  rw [Work.Diff.GE.extD_covRmT g y (G 0) (fun i : Fin 5 => G i.succ)]
  rw [Work.Diff.GE.cov2RmExt_eq_cov2Rm (V := (fun i : Fin 5 => G i.succ) 0) hLC g y (G 0 y)
        (hG (Fin.succ 0)) (hG (Fin.succ 1)) (hG (Fin.succ 2)) (hG (Fin.succ 3))
        (hG (Fin.succ 4))]
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    show (Fin.succ (2 : Fin 5)) = (3 : Fin 6) from by decide,
    show (Fin.succ (3 : Fin 5)) = (4 : Fin 6) from by decide,
    show (Fin.succ (4 : Fin 5)) = (5 : Fin 6) from by decide]

/-- The third iterate: `∇³Rm` on the values of the tuple. -/
theorem ckt_three_eq_cov3Rm (hLC : Submission.Diff.LCSmooth I M)
    (g : Submission.Diff.SMet I M) (G : Fin 7 → TField (I := I) (M := M))
    (hG : ∀ i, CMDiff ∞ (T% (G i))) (y : M) :
    ckt g 3 G y
      = Work.Diff.GE.cov3Rm g y (G 0 y) (G 1 y) (G 2 y) (G 3 y) (G 4 y) (G 5 y) (G 6 y) := by
  have hcov : Work.Diff.GE.CovSmooth (Submission.Diff.lcOf g) := (hLC g).1.some
  have htail : ∀ i : Fin 6, CMDiff ∞ (T% ((fun i : Fin 6 => G i.succ) i)) := fun i => hG i.succ
  have hupd : ∀ s : Fin 6,
      ∀ i, CMDiff ∞ (T% ((Work.Diff.GE.upd (Submission.Diff.lcOf g) (G 0)
        (fun i : Fin 6 => G i.succ) s) i)) := by
    intro s i
    simp only [Work.Diff.GE.upd, Function.update_apply]
    by_cases hi : i = s
    · rw [if_pos hi]
      exact Work.Diff.GE.cmdiff_covAlong (Submission.Diff.lcOf g) hcov (hG 0) (hG s.succ)
    · rw [if_neg hi]
      exact hG i.succ
  rw [show ckt g 3 G y
        = Work.Diff.GE.extD (Submission.Diff.lcOf g) (ckt g 2) y (G 0)
            (fun i : Fin 6 => G i.succ) from rfl]
  rw [show Work.Diff.GE.extD (Submission.Diff.lcOf g) (ckt g 2) y (G 0)
          (fun i : Fin 6 => G i.succ)
        = Work.Diff.GE.extD (Submission.Diff.lcOf g) (cov2RmT g) y (G 0)
            (fun i : Fin 6 => G i.succ) from by
      rw [Work.Diff.GE.extD_eq, Work.Diff.GE.extD_eq]
      rw [show (ckt g 2 (fun i : Fin 6 => G i.succ))
            = (cov2RmT g (fun i : Fin 6 => G i.succ)) from
          funext (fun y' => by
            rw [cov2RmT_apply]
            exact ckt_two_eq_cov2Rm hLC g (fun i : Fin 6 => G i.succ) htail y')]
      rw [show (∑ s : Fin 6, ckt g 2 (Work.Diff.GE.upd (Submission.Diff.lcOf g)
              (G 0) (fun i : Fin 6 => G i.succ) s) y)
            = (∑ s : Fin 6, cov2RmT g (Work.Diff.GE.upd (Submission.Diff.lcOf g)
              (G 0) (fun i : Fin 6 => G i.succ) s) y) from
          Finset.sum_congr rfl (fun s _ => by
            rw [cov2RmT_apply]
            exact ckt_two_eq_cov2Rm hLC g _ (hupd s) y)]]
  rw [extD_cov2RmT g y (G 0) (fun i : Fin 6 => G i.succ)]
  rw [Work.Diff.GE.cov3Rm]
  exact Work.Diff.GE.kato_cov3RmExt_field hLC g y
      ((fun i : Fin 6 => G i.succ) 0) ((fun i : Fin 6 => G i.succ) 1)
      ((fun i : Fin 6 => G i.succ) 2) ((fun i : Fin 6 => G i.succ) 3)
      ((fun i : Fin 6 => G i.succ) 4) ((fun i : Fin 6 => G i.succ) 5)
      (Submission.Diff.smoothExt y (G 1 y)) (Submission.Diff.smoothExt y (G 2 y))
      (Submission.Diff.smoothExt y (G 3 y)) (Submission.Diff.smoothExt y (G 4 y))
      (Submission.Diff.smoothExt y (G 5 y)) (Submission.Diff.smoothExt y (G 6 y))
      (hG (Fin.succ 0)) (hG (Fin.succ 1)) (hG (Fin.succ 2)) (hG (Fin.succ 3))
      (hG (Fin.succ 4)) (hG (Fin.succ 5))
      (Work.Diff.GE.smoothExt_cmdiff y (G 1 y)) (Work.Diff.GE.smoothExt_cmdiff y (G 2 y))
      (Work.Diff.GE.smoothExt_cmdiff y (G 3 y)) (Work.Diff.GE.smoothExt_cmdiff y (G 4 y))
      (Work.Diff.GE.smoothExt_cmdiff y (G 5 y)) (Work.Diff.GE.smoothExt_cmdiff y (G 6 y))
      (by show G 1 y = Submission.Diff.smoothExt y (G 1 y) y
          rw [Work.Diff.GE.smoothExt_apply])
      (by show G 2 y = Submission.Diff.smoothExt y (G 2 y) y
          rw [Work.Diff.GE.smoothExt_apply])
      (by show G 3 y = Submission.Diff.smoothExt y (G 3 y) y
          rw [Work.Diff.GE.smoothExt_apply])
      (by show G 4 y = Submission.Diff.smoothExt y (G 4 y) y
          rw [Work.Diff.GE.smoothExt_apply])
      (by show G 5 y = Submission.Diff.smoothExt y (G 5 y) y
          rw [Work.Diff.GE.smoothExt_apply])
      (by show G 6 y = Submission.Diff.smoothExt y (G 6 y) y
          rw [Work.Diff.GE.smoothExt_apply])
      (G 0 y)

/-- The third iterate on a `mkT`-packed tuple: `∇³Rm` on the values. -/
theorem ckt_three_mkT (hLC : Submission.Diff.LCSmooth I M)
    (g : Submission.Diff.SMet I M) (x : M)
    (w : Fin 3 → TField (I := I) (M := M)) (A B C D : TField (I := I) (M := M))
    (hw : ∀ i, CMDiff ∞ (T% (w i))) (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B))
    (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D)) :
    ckt g 3 (mkT w (Work.Diff.GE.rmPQuad A B C D)) x
      = Work.Diff.GE.cov3Rm g x (w 0 x) (w 1 x) (w 2 x) (A x) (B x) (C x) (D x) := by
  have hG : ∀ i : Fin 7, CMDiff ∞ (T% ((mkT w (Work.Diff.GE.rmPQuad A B C D)) i)) := by
    intro i
    refine Fin.addCases (motive := fun i => CMDiff ∞
      (T% ((mkT w (Work.Diff.GE.rmPQuad A B C D)) i))) ?_ ?_ i
    · intro j
      rw [mkT_castAdd]
      exact hw j
    · intro p
      rw [mkT_natAdd]
      exact Work.Diff.GE.rmPQuad_smooth hA hB hC hD p
  rw [ckt_three_eq_cov3Rm hLC g _ hG x,
    show (mkT w (Work.Diff.GE.rmPQuad A B C D)) 0 = w 0 from by
      rw [show (0 : Fin 7) = Fin.castAdd 4 (0 : Fin 3) from rfl, mkT_castAdd],
    show (mkT w (Work.Diff.GE.rmPQuad A B C D)) 1 = w 1 from by
      rw [show (1 : Fin 7) = Fin.castAdd 4 (1 : Fin 3) from rfl, mkT_castAdd],
    show (mkT w (Work.Diff.GE.rmPQuad A B C D)) 2 = w 2 from by
      rw [show (2 : Fin 7) = Fin.castAdd 4 (2 : Fin 3) from rfl, mkT_castAdd],
    show (mkT w (Work.Diff.GE.rmPQuad A B C D)) 3 = A from by
      rw [show (3 : Fin 7) = Fin.natAdd 3 (0 : Fin 4) from rfl, mkT_natAdd,
        Work.Diff.GE.rmPQuad_zero],
    show (mkT w (Work.Diff.GE.rmPQuad A B C D)) 4 = B from by
      rw [show (4 : Fin 7) = Fin.natAdd 3 (1 : Fin 4) from rfl, mkT_natAdd,
        Work.Diff.GE.rmPQuad_one],
    show (mkT w (Work.Diff.GE.rmPQuad A B C D)) 5 = C from by
      rw [show (5 : Fin 7) = Fin.natAdd 3 (2 : Fin 4) from rfl, mkT_natAdd,
        Work.Diff.GE.rmPQuad_two],
    show (mkT w (Work.Diff.GE.rmPQuad A B C D)) 6 = D from by
      rw [show (6 : Fin 7) = Fin.natAdd 3 (3 : Fin 4) from rfl, mkT_natAdd,
        Work.Diff.GE.rmPQuad_three]]

/-! ## The `k = 1` rough Laplacian of `∇Rm` in the two vocabularies -/

/-- **The tower at level `3` is `∇³Rm` on the values of the fields.**  Direct form of
`ckt_three_mkT` for the `Ext` tower `covKRmExt`. -/
theorem covKRmExt_three_eq_cov3Rm (hLC : Submission.Diff.LCSmooth I M)
    (g : Submission.Diff.SMet I M) (x : M)
    (w : Fin 3 → TField (I := I) (M := M)) (A B C D : TField (I := I) (M := M))
    (hw : ∀ i, CMDiff ∞ (T% (w i))) (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B))
    (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D)) :
    Work.Diff.EXT.covKRmExt g 3 w A B C D x
      = Work.Diff.GE.cov3Rm g x (w 0 x) (w 1 x) (w 2 x) (A x) (B x) (C x) (D x) := by
  rw [show Work.Diff.EXT.covKRmExt g 3 w A B C D x
        = ckt g 3 (mkT w (Work.Diff.GE.rmPQuad A B C D)) x from
      (ckt_mkT_eq g 3 w (Work.Diff.GE.rmPQuad A B C D) x).symm]
  exact ckt_three_mkT hLC g x w A B C D hw hA hB hC hD

section Boundaryless

variable [I.Boundaryless]

/-- **The `k = 1` case of the rough Laplacian of `∇^k Rm`.**  The `Ext`-tower component
`lapCovKRm g x 1 v a b c d` of the rough Laplacian `Δ∇Rm` is the GE-area `lapCovRmAt g x v a b c d`.
-/
theorem lapCovKRm_one_eq (g : Submission.Diff.SMet I M) (x : M)
    (v a b c d : TangentSpace I x) :
    Work.Diff.EXT.lapCovKRm g x 1 (fun _ => v) a b c d
      = Work.Diff.GE.lapCovRmAt g x v a b c d := by
  have hLC : Submission.Diff.LCSmooth I M := Work.Diff.T.lc_smooth (I := I) (M := M)
  rw [Work.Diff.EXT.lapCovKRm, Work.Diff.GE.lapCovRmAt]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  have h0 : ((Fin.cons (Submission.Diff.onFrame g x m)
      (Fin.cons (Submission.Diff.onFrame g x m) (fun _ : Fin 1 => v))) :
        Fin 3 → TangentSpace I x) 0 = Submission.Diff.onFrame g x m := rfl
  have h1 : ((Fin.cons (Submission.Diff.onFrame g x m)
      (Fin.cons (Submission.Diff.onFrame g x m) (fun _ : Fin 1 => v))) :
        Fin 3 → TangentSpace I x) 1 = Submission.Diff.onFrame g x m := rfl
  have h2 : ((Fin.cons (Submission.Diff.onFrame g x m)
      (Fin.cons (Submission.Diff.onFrame g x m) (fun _ : Fin 1 => v))) :
        Fin 3 → TangentSpace I x) 2 = v := rfl
  show Work.Diff.EXT.covKRmExt g 3
      (fun s : Fin 3 => Submission.Diff.smoothExt x
        (((Fin.cons (Submission.Diff.onFrame g x m)
          (Fin.cons (Submission.Diff.onFrame g x m) (fun _ : Fin 1 => v))) :
            Fin 3 → TangentSpace I x) s))
      (Submission.Diff.smoothExt x a) (Submission.Diff.smoothExt x b)
      (Submission.Diff.smoothExt x c) (Submission.Diff.smoothExt x d) x
    = Work.Diff.GE.cov3Rm g x (Submission.Diff.onFrame g x m)
        (Submission.Diff.onFrame g x m) v a b c d
  rw [covKRmExt_three_eq_cov3Rm hLC g x _
      (Submission.Diff.smoothExt x a) (Submission.Diff.smoothExt x b)
      (Submission.Diff.smoothExt x c) (Submission.Diff.smoothExt x d)
      (fun i => Work.Diff.GE.smoothExt_cmdiff x _)
      (Work.Diff.GE.smoothExt_cmdiff x a) (Work.Diff.GE.smoothExt_cmdiff x b)
      (Work.Diff.GE.smoothExt_cmdiff x c) (Work.Diff.GE.smoothExt_cmdiff x d)]
  simp only [Work.Diff.GE.smoothExt_apply]
  rw [h0, h1, h2]

end Boundaryless

/-! ## The assembly -/

theorem evolCompK_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (h : ∃ C : ℝ, 0 ≤ C ∧ ∀ (G : ℝ → Submission.Diff.SMet I M) (T : ℝ),
      Submission.Diff.IsRicciFlow G T → ∀ t ∈ Set.Ico 0 T, ∀ x : M,
      ∀ (e : ℝ → Fin (Module.finrank ℝ E) → TangentSpace I x)
        (edot : Fin (Module.finrank ℝ E) → TangentSpace I x) (K : ℝ), 0 ≤ K →
        (∀ᶠ s in nhdsWithin t (Set.Ico 0 T), Submission.Diff.IsONFrame (G s) x (e s)) →
        (∀ i, HasDerivWithinAt (fun s ↦ e s i) (edot i) (Set.Ico 0 T) t) →
        (∀ i, (G t).inner x (edot i) (edot i) ≤ K * Submission.Diff.rmNormSq (G t) x) →
        ∀ m i j k l : Fin (Module.finrank ℝ E), ∃ D : ℝ,
          HasDerivWithinAt
            (fun s ↦ Submission.Diff.covRm (G s) x (e s m) (e s i) (e s j) (e s k) (e s l))
            D (Set.Ico 0 T) t ∧
          |D - Work.Diff.GE.lapCovRmAt (G t) x (e t m) (e t i) (e t j) (e t k) (e t l)|
              ≤ C * (1 + K) * Real.sqrt (Submission.Diff.rmNormSq (G t) x)
                  * Real.sqrt (Submission.Diff.dRmNormSq (G t) x)) :
    Work.Diff.EXT.EvolCompK (I := I) (M := M) 1 := by
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨C, hC0, ?_⟩
  intro G T hflow t ht x e edot K' hK' het hvel hON hder u i j l m
  obtain ⟨D, hD, hDb⟩ := hC G T hflow t ht x e edot K' hK' hON hder hvel (u 0) i j l m
  refine ⟨D, ?_, ?_⟩
  · have hfun : (fun s => Work.Diff.EXT.covKRm (G s) x 1 (fun r : Fin 1 => e s (u r))
          (e s i) (e s j) (e s l) (e s m))
        = (fun s => Submission.Diff.covRm (G s) x (e s (u 0)) (e s i) (e s j) (e s l)
            (e s m)) := by
      funext s
      rw [show (fun r : Fin 1 => e s (u r)) = (fun _ : Fin 1 => e s (u 0)) from
        funext (fun r => by rw [Subsingleton.elim r 0])]
      exact Work.Diff.EXT.covKRm_one (G s) x (e s (u 0)) (e s i) (e s j) (e s l) (e s m)
    rwa [hfun]
  · have hlap : Work.Diff.EXT.lapCovKRm (G t) x 1
          (fun r : Fin 1 => Submission.Diff.onFrame (G t) x (u r))
          (Submission.Diff.onFrame (G t) x i) (Submission.Diff.onFrame (G t) x j)
          (Submission.Diff.onFrame (G t) x l) (Submission.Diff.onFrame (G t) x m)
        = Work.Diff.GE.lapCovRmAt (G t) x (e t (u 0)) (e t i) (e t j) (e t l) (e t m) := by
      rw [show (fun r : Fin 1 => Submission.Diff.onFrame (G t) x (u r))
            = (fun _ : Fin 1 => Submission.Diff.onFrame (G t) x (u 0)) from
          funext (fun r => by rw [Subsingleton.elim r 0])]
      rw [lapCovKRm_one_eq (G t) x (Submission.Diff.onFrame (G t) x (u 0))
        (Submission.Diff.onFrame (G t) x i) (Submission.Diff.onFrame (G t) x j)
        (Submission.Diff.onFrame (G t) x l) (Submission.Diff.onFrame (G t) x m)]
      rw [← het (u 0), ← het i, ← het j, ← het l, ← het m]
    rw [hlap]
    have hgoal : C * (1 + K') * (1 + ∑ j' ∈ Finset.range 1, Work.Diff.EXT.curvNormK (G t) x j')
          * (1 + Real.sqrt (Work.Diff.EXT.curvNormK (G t) x 1))
        = C * (1 + K') * (1 + Submission.Diff.rmNormSq (G t) x)
          * (1 + Real.sqrt (Submission.Diff.dRmNormSq (G t) x)) := by
      rw [Finset.sum_range_one, Work.Diff.EXT.curvNormK_zero_eq_rmNormSq,
        Work.Diff.EXT.curvNormK_one_eq_dRmNormSq]
    rw [hgoal]
    refine le_trans hDb ?_
    have h0 : 0 ≤ Submission.Diff.rmNormSq (G t) x :=
      Work.Diff.GE.Gest.rmNormSq_nonneg (g := G t) x
    have h1 : 0 ≤ Submission.Diff.dRmNormSq (G t) x :=
      Work.Diff.GE.Gest.dRmNormSq_nonneg (g := G t) x
    have hCK : 0 ≤ C * (1 + K') := mul_nonneg hC0 (by linarith)
    have h2 : Real.sqrt (Submission.Diff.rmNormSq (G t) x)
        ≤ 1 + Submission.Diff.rmNormSq (G t) x := by
      nlinarith [Real.sq_sqrt h0, Real.sqrt_nonneg (Submission.Diff.rmNormSq (G t) x)]
    have h3 : Real.sqrt (Submission.Diff.dRmNormSq (G t) x)
        ≤ 1 + Real.sqrt (Submission.Diff.dRmNormSq (G t) x) := by
      linarith [Real.sqrt_nonneg (Submission.Diff.dRmNormSq (G t) x)]
    calc C * (1 + K') * Real.sqrt (Submission.Diff.rmNormSq (G t) x)
            * Real.sqrt (Submission.Diff.dRmNormSq (G t) x)
        = (C * (1 + K')) * (Real.sqrt (Submission.Diff.rmNormSq (G t) x)
            * Real.sqrt (Submission.Diff.dRmNormSq (G t) x)) := by ring
      _ ≤ (C * (1 + K')) * ((1 + Submission.Diff.rmNormSq (G t) x)
            * (1 + Real.sqrt (Submission.Diff.dRmNormSq (G t) x))) := by
          refine mul_le_mul_of_nonneg_left ?_ hCK
          exact mul_le_mul h2 h3 (Real.sqrt_nonneg _) (by linarith)
      _ = C * (1 + K') * (1 + Submission.Diff.rmNormSq (G t) x)
            * (1 + Real.sqrt (Submission.Diff.dRmNormSq (G t) x)) := by ring

end Work.Diff.EXT
