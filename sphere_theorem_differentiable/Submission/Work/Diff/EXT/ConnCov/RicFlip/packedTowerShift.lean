import Mathlib
import Submission.Work.Diff.EXT.ConnCov.RicFlip.FlipConv
import Submission.Work.Diff.EXT.ConnCov.RicFlip.RicT_props
import Submission.Work.Diff.EXT.ConnCov.baseRic_tower_hypotheses
import Submission.Work.Diff.EXT.ConnCov.RicTrNT.TowerBoundOfHtowerBound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.ConnCov.RicFlip

open Work.Diff.EXT.ATower Work.Diff.EXT.ConnCov Work.Diff.EXT.ConnCov.AMB

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-!
# The packed shift identity

The *modified* tower `ATower.tower cov (baseRic g) m` (the iterated covariant derivative of the
`(0,3)`-tensor `baseRic g = (A,B,C) ↦ Ric(A,B)`, whose third value slot is a dummy) and the
*honest* tower of the Ricci tensor (`pDiter2 cov (ric2 g) i`, the iterated covariant derivative of
`Ric` read as a `(0,2)`-tensor) are related by the **shift identity**: the modified tower is the
signed selection sum

  `pack (tower cov (baseRic g) m) F = Σ_{j ≤ m} (-1)^{m+j} (m-j)! Σ_{f : Fin j ↪o Fin m}
      pDiter2 cov (ric2 g) j (subTuple F f)`

of the honest towers, evaluated on the `f`-selected direction slots of the tuple.  This is the
statement proved here; it is the bridge that lets the two-connection flip, whose hypotheses
(`SlotAddP`) hold for the honest towers but **not** for the modified one, be applied to the modified
tower of the target.

The proof has two ingredients:

* the **selection-sum expansion** `RicTrNT.tower_eval_eq_tb` (the shift identity for the *curried*
  honest tower `htower`), which holds on smooth tuples — the smoothness hypothesis `hF` on `F`
  is essential (`mvfderiv` is additive only on functions differentiable at the point, so the
  identity is false for arbitrary tuples);
* the **packed bridge** `pack_htower_pDiter2`, identifying the packed curried honest tower of
  `baseRic g` with the packed honest tower `pDiter2 cov (ric2 g) i` of `Ric` (the dummy third value
  slot is dropped, and the identity holds for an arbitrary connection `cov`).

The remaining work is the tuple bookkeeping through `liftTup`/`subTuple`.
-/

/-- **The packed bridge between the curried honest tower of `baseRic` and the honest Ricci tower.**
`AMB.pack (htower cov (baseRic g) i) F` is `pDiter2 cov (ric2 g) i` read on the first `i + 2` slots
of the tuple `F` — the (dummy) third value slot, `htower` being independent of it, is dropped. -/
theorem pack_htower_pDiter2 (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (g : Submission.Diff.SMet I M) :
    ∀ (i : ℕ) (F : Fin (i + 3) → AMB.TF (I := I) (M := M)),
      AMB.pack (htower cov (baseRic g) i) F
        = pDiter2 cov (ric2 g) i (fun l : Fin (i + 2) => F (Fin.castSucc l)) := by
  intro i
  induction i with
  | zero =>
      intro F
      funext x
      simp only [htower_zero, AMB.pack_apply, ric2, baseRic, pDiter2]
      rfl
  | succ i ih =>
      intro F
      have hpack : AMB.pack (htower cov (baseRic g) i) = lift (pDiter2 cov (ric2 g) i) :=
        funext ih
      rw [show htower cov (baseRic g) (i + 1) = hstep cov (htower cov (baseRic g) i) from rfl]
      rw [pack_hstep cov]
      rw [hpack]
      rw [pD_lift]
      rw [sub_add_cancel]
      rw [show pDiter2 cov (ric2 g) (i + 1) = AMB.pD cov (pDiter2 cov (ric2 g) i) from rfl]
      rfl

theorem packedTowerShift
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ∀ (Y Z : Π y : M, TangentSpace I y), Work.Diff.EXT.ATower.SmE I M Y →
      Work.Diff.EXT.ATower.SmE I M Z →
      Work.Diff.EXT.ATower.SmE I M (fun y => cov Y y (Z y)))
    (g : Submission.Diff.SMet I M) (m : ℕ)
    (F : Fin (m + 3) → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M))
    (hF : ∀ s, Work.Diff.EXT.ATower.SmE I M (F s)) :
    Work.Diff.EXT.ConnCov.AMB.pack
        (Work.Diff.EXT.ATower.tower cov (Work.Diff.EXT.ConnCov.baseRic g) m) F
      = Work.Diff.EXT.ConnCov.RicFlip.shiftSum cov g m F := by
  obtain ⟨hsm, _, _, _, _⟩ := Work.Diff.EXT.ConnCov.baseRic_tower_hypotheses hLC g
  funext x
  rw [AMB.pack_apply]
  rw [Work.Diff.EXT.ConnCov.RicTrNT.tower_eval_eq_tb cov hcov (baseRic g) hsm m
        (fun i : Fin m => F (Fin.castAdd 3 i))
        (F (Fin.natAdd m 0)) (F (Fin.natAdd m 1)) (F (Fin.natAdd m 2)) x
        (fun i => hF _) (hF _) (hF _) (hF _)]
  rw [shiftSum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [show Work.Diff.EXT.ConnCov.RicTrNT.shCo m j
        = (-1 : ℝ) ^ (m + j) * ((m - j).factorial : ℝ) from rfl]
  congr 1
  refine Finset.sum_congr rfl (fun f _ => ?_)
  -- the term: the honest tower of `baseRic` on the `f`-selection is the honest Ricci tower
  have hb := congrFun (pack_htower_pDiter2 (I := I) (M := M) cov g j
    (liftTup (subTuple F f.val))) x
  rw [AMB.pack_apply] at hb
  rw [show (fun l : Fin (j + 2) => liftTup (subTuple F f.val) (Fin.castSucc l))
        = subTuple F f.val from by funext l; exact liftTup_castAdd _ l] at hb
  rw [← hb]
  -- the entries of `liftTup (subTuple F f)` reproduce the tuple of the left-hand side
  have hfun : (fun i : Fin j => liftTup (subTuple F f.val) (Fin.castAdd 3 i))
      = fun l => F (Fin.castAdd 3 (f.val l)) := by
    funext i
    rw [show (Fin.castAdd 3 i : Fin (j + 3)) = Fin.castAdd 1 (Fin.castAdd 2 i) from by
      ext; simp [Fin.val_castAdd]]
    rw [liftTup_castAdd]
    exact subTuple_castAdd F f.val i
  have hA : liftTup (subTuple F f.val) (Fin.natAdd j (0 : Fin 3)) = F (Fin.natAdd m 0) := by
    rw [show (Fin.natAdd j (0 : Fin 3) : Fin (j + 3))
          = Fin.castAdd 1 (Fin.natAdd j (0 : Fin 2)) from by
      ext; simp [Fin.val_natAdd, Fin.val_castAdd]]
    rw [liftTup_castAdd, subTuple_natAdd_zero, Fin.castSucc_zero]
  have hB : liftTup (subTuple F f.val) (Fin.natAdd j (1 : Fin 3)) = F (Fin.natAdd m 1) := by
    rw [show (Fin.natAdd j (1 : Fin 3) : Fin (j + 3))
          = Fin.castAdd 1 (Fin.natAdd j (1 : Fin 2)) from by
      ext; simp [Fin.val_natAdd, Fin.val_castAdd]]
    rw [liftTup_castAdd, subTuple_natAdd_one, Fin.castSucc_one]
  have hC : liftTup (subTuple F f.val) (Fin.natAdd j (2 : Fin 3))
      = fun y : M => (0 : TangentSpace I y) := by
    rw [show (Fin.natAdd j (2 : Fin 3) : Fin (j + 3)) = Fin.natAdd (j + 2) (0 : Fin 1) from by
      ext; simp [Fin.val_natAdd]]
    exact Fin.addCases_right _
  rw [hfun, hA, hB, hC]
  exact cIndep_htower cov (cIndep_baseRic g) j _ _ _
    (F (Fin.natAdd m 2)) (fun y : M => (0 : TangentSpace I y)) x

end Work.Diff.EXT.ConnCov.RicFlip
