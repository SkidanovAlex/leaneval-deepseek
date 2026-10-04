import Mathlib
import Submission.Work.Diff.EXT.lapComm_tower
import Submission.Work.Diff.EXT.lapCommInsT

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The product rule for the curvature-inserted tower

`Work.Diff.EXT.lapComm_curvActT_deriv`: for globally `C^∞` fields and the `(j+6)`-tuple `G`, the
`Ext`-derivative `∇_e (curvActT g j G)` of the curvature action `curvActT g j G` (the sum over the
`j+4` slots of the tail of `ckt g j` with the `s`-th slot replaced by the curvature field
`R(G 0, G 1)(G s.succ.succ)`) expands into the derivative of the inner tower plus the derivative of
the inserted curvature field: the second sum below is the single-slot insertion of `dCurvV`, and
the identity is the assembly of `Work.Diff.EXT.lapCommInsT` over the `j+4` slots.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

local macro "Tf" : term => `((y : M) → TangentSpace I y)
local notation "consF" X:max F:max => (Fin.cons (α := fun _ : _ => Tf) X F)

theorem lapComm_curvActT_deriv
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (j : ℕ) (x : M)
    (e : (y : M) → TangentSpace I y) (he : Work.Diff.GE.SmoothFieldT (I := I) (M := M) e)
    (G : Fin (j + 6) → ((y : M) → TangentSpace I y))
    (hG : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (G i)) :
    Work.Diff.GE.extD (Submission.Diff.lcOf g) (Work.Diff.EXT.curvActT (I := I) (M := M) g j) x e G
      = (∑ s : Fin (j + 4),
          Work.Diff.EXT.ckt g (j + 1)
            (Fin.cons (α := fun _ : Fin (j + 5) => ((y : M) → TangentSpace I y)) e
              (Function.update (fun i : Fin (j + 4) => G i.succ.succ) s
                (fun z => LeanEval.Geometry.SphereTheorem.curv (Submission.Diff.lcOf g)
                  (G 0) (G 1) (G s.succ.succ) z))) x)
        + (∑ s : Fin (j + 4),
          Work.Diff.EXT.ckt g j
            (Function.update (Function.update (fun i : Fin (j + 4) => G i.succ.succ) s
                (fun z => LeanEval.Geometry.SphereTheorem.curv (Submission.Diff.lcOf g)
                  (G 0) (G 1) (G s.succ.succ) z)) s
              (Work.Diff.EXT.dCurvV (Submission.Diff.lcOf g) e (G 0) (G 1) (G s.succ.succ))) x) := by
  obtain ⟨hcov⟩ := (hLC g).1
  -- the tower tuple with the `s`-th slot replaced by the curvature field
  set TL : Fin (j + 4) → Tf := fun i => G i.succ.succ with hTL
  set Cs : Fin (j + 4) → Tf := fun s => (fun y => curv (Submission.Diff.lcOf g) (G 0) (G 1)
    (TL s) y) with hCs
  set Tp : Fin (j + 4) → (Fin (j + 4) → Tf) := fun s => Function.update TL s (Cs s) with hTp
  have hTLsm : ∀ i, SmoothF (TL i) := fun i => hG i.succ.succ
  have hCssm : ∀ s, SmoothF (Cs s) := fun s => Work.Diff.GE.contMDiff_curv_fields
    (Submission.Diff.lcOf g) hcov (hG 0) (hG 1) (hTLsm s)
  have hTpsm : ∀ s, ∀ i, SmoothF (Tp s i) := fun s i => smoothF_update hTLsm (hCssm s) i
  -- the curvature action is the sum of the tower values on the replaced tuples
  have hcurvAct : curvActT (I := I) (M := M) g j G = (fun y => ∑ s, ckt g j (Tp s) y) := by
    funext y
    rw [hTp, hCs, hTL]
    rfl
  rw [Work.Diff.GE.extD_eq, hcurvAct]
  -- the derivative of the sum of tower values, one slot at a time
  have hder : mvfderiv I (fun y : M => ∑ s, ckt g j (Tp s) y) x (e x)
      = ∑ s, (ckt g (j + 1) (consF e (Tp s)) x
          + ∑ i : Fin (j + 4), ckt g j (Function.update (Tp s) i
              (dirF g ((Tp s) i) e)) x) := by
    rw [Work.Diff.GE.Kato3.mvfderiv_sum Finset.univ
      (fun s : Fin (j + 4) => fun y : M => ckt g j (Tp s) y)
      (fun s => (tensProp_all hLC g j (Tp s) (hTpsm s)).1) x (e x)]
    exact Finset.sum_congr rfl fun s _ => mvfderiv_ckt_gen' g j (Tp s) e x
  rw [hder]
  -- the corrections produced by the outer derivative hitting the fields of `G`
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
  rw [hcorr, Finset.sum_comm, Finset.sum_add_distrib]
  -- `upd` is the slotwise Leibniz update, so the `q`-terms are those of the insertion identity
  have hupd : ∀ q : Fin (j + 6), Work.Diff.GE.upd (Submission.Diff.lcOf g) e G q
      = Function.update G q (dirF g (G q) e) := fun q => rfl
  simp only [hupd]
  -- termwise, the single-slot insertion identity (`lapCommInsT`), summed over the `j+4` slots
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
            (dCurvV (Submission.Diff.lcOf g) e (G 0) (G 1) (G s.succ.succ))) x := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    have h := lapCommInsT (I := I) (M := M) hLC g j x e he G hG s
    rw [hTp, hCs, hTL]
    simpa only [hupd] using h
  -- the first sums agree as well
  have hAsum : (∑ s : Fin (j + 4), ckt g (j + 1) (consF e (Tp s)) x)
      = ∑ s : Fin (j + 4), ckt g (j + 1)
          (consF e (Function.update (fun i : Fin (j + 4) => G i.succ.succ) s
            (fun z => curv (Submission.Diff.lcOf g) (G 0) (G 1) (G s.succ.succ) z))) x := by
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hTp, hCs, hTL]
  linarith [hsum, hAsum]

end Work.Diff.EXT
