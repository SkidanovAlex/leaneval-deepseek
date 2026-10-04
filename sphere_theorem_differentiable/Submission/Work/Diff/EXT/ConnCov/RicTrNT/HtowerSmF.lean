import Mathlib
import Submission.Work.Diff.EXT.ConnCov.honestTower
import Submission.Work.Diff.EXT.ATower.tower_slotAdd_smF

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
/-!
# Smoothness of the honest tower (stand-alone copy, no `deltaTower` in the import closure)

This is a copy of `Submission/Work/Diff/EXT/ConnCov/RicTr/htower_smF.lean`, kept in the namespace
`Work.Diff.EXT.ConnCov.RicTrNT` and importing only `honestTower` and
`ATower.tower_slotAdd_smF`.  The original imports `RicTr/ricTowerBound_fixed` (which it does not
use), and that module reaches `ConnCov/deltaTower`; since the Ricci-tower chapter
(`ConnCov/RicTowerDefs`) declares a constant with the same name `Op2`, no module can import both
legs.  The present stand-alone copy avoids the collision.
-/

/-!
# Smoothness of the *honest* tower `htower cov base k` on smooth fields

`Work.Diff.EXT.ConnCov.htower cov base k` is the `k`-th iterated derivative of the base operator
`base` with respect to the *honest* recursion step `hstep cov = step cov + drop`.  Because `drop`
simply discards the first direction slot, one application of `hstep` involves only

* one `mvfderiv` of the previously built object (against the head direction field `v 0`), and
* `k + 4` evaluations of the previously built object on smooth fields (the connection corrections
  in the derivative slots, in the two "value" slots `A`, `B`, and — through `drop` — the value of
  the object itself).

Consequently, if `τ` sends smooth fields to smooth functions and the connection `cov` sends pairs
of smooth fields to smooth fields, then so does `hstep cov τ`; an induction on `k` then gives
smoothness of `htower cov base k` for every `k`.  This is the scalar-function counterpart of
`Work.Diff.EXT.ATower.tower_slotAdd_smF` (which treats the non-honest `tower`), and it is the
smoothness input needed to make sense of differentiating the honest Ric-tower.

The only library inputs used are

* `Work.Diff.EXT.ATower.stepAux_smF` — smoothness of the (non-honest) recursion step `step`, and
* `Work.Diff.C.mvfderiv_contMDiffAt` (used inside `stepAux_smF`) for the `mvfderiv` term.
-/

set_option maxHeartbeats 800000

namespace Work.Diff.EXT.ConnCov.RicTrNT

open Work.Diff.EXT.ATower

/-- **Smoothness of one honest recursion step.**  If `τ` sends smooth fields to smooth functions,
then so does `hstep cov τ`. -/
theorem hstep_smF
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    {k : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ∀ (Y Z : Π y : M, TangentSpace I y), SmE I M Y → SmE I M Z →
      SmE I M (fun y => cov Y y (Z y)))
    (τ : Op3 (I := I) (M := M) k)
    (hτsm : ∀ (u : Fin k → (Π y : M, TangentSpace I y)) (A B C : Π y : M, TangentSpace I y),
      (∀ j, SmE I M (u j)) → SmE I M A → SmE I M B → SmE I M C → SmF I M (τ u A B C))
    (v : Fin (k + 1) → (Π y : M, TangentSpace I y)) (A B C : Π y : M, TangentSpace I y)
    (hv : ∀ j, SmE I M (v j)) (hA : SmE I M A) (hB : SmE I M B) (hC : SmE I M C) :
    SmF I M (Work.Diff.EXT.ConnCov.hstep cov τ v A B C) := by
  -- the differentiation term and the connection corrections, i.e. the non-honest `step`
  have hstep_sm : SmF I M (Work.Diff.EXT.ATower.step cov τ v A B C) := by
    rw [step_eq_stepAux]
    exact stepAux_smF cov τ hτsm hcov (hv 0) (fun i => hv i.succ) hA hB hC
  -- the `drop` correction, i.e. `τ` itself read on the tail of the direction tuple
  have hdrop_sm : SmF I M (Work.Diff.EXT.ConnCov.drop τ v A B C) :=
    hτsm (fun i : Fin k => v i.succ) A B C (fun i => hv i.succ) hA hB hC
  exact hstep_sm.add hdrop_sm

/-- **The induction.**  The `k`-th honest tower sends smooth fields to smooth functions. -/
theorem htower_smF_aux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ∀ (Y Z : Π y : M, TangentSpace I y), SmE I M Y → SmE I M Z →
      SmE I M (fun y => cov Y y (Z y)))
    (base : Op3 (I := I) (M := M) 0)
    (hsm : ∀ (v : Fin 0 → (Π y : M, TangentSpace I y)) (A B C : Π y : M, TangentSpace I y),
      SmE I M A → SmE I M B → SmE I M C → SmF I M (base v A B C)) :
    ∀ (k : ℕ) (v : Fin k → (Π y : M, TangentSpace I y)) (A B C : Π y : M, TangentSpace I y),
      (∀ i, SmE I M (v i)) → SmE I M A → SmE I M B → SmE I M C →
      SmF I M (Work.Diff.EXT.ConnCov.htower cov base k v A B C) := by
  intro k
  induction k with
  | zero =>
      intro v A B C _hv hA hB hC
      exact hsm v A B C hA hB hC
  | succ k ih =>
      intro v A B C hv hA hB hC
      exact hstep_smF cov hcov (Work.Diff.EXT.ConnCov.htower cov base k)
        (fun u A' B' C' hu hA' hB' hC' => ih u A' B' C' hu hA' hB' hC')
        v A B C hv hA hB hC

theorem htower_smF
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ∀ (Y Z : Π y : M, TangentSpace I y), Work.Diff.EXT.ATower.SmE I M Y →
      Work.Diff.EXT.ATower.SmE I M Z →
      Work.Diff.EXT.ATower.SmE I M (fun y => cov Y y (Z y)))
    (base : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) 0)
    (hsm : ∀ (v : Fin 0 → (Π y : M, TangentSpace I y)) (A B C : Π y : M, TangentSpace I y),
      Work.Diff.EXT.ATower.SmE I M A → Work.Diff.EXT.ATower.SmE I M B →
      Work.Diff.EXT.ATower.SmE I M C →
      Work.Diff.EXT.ATower.SmF I M (base v A B C))
    (k : ℕ) (v : Fin k → (Π y : M, TangentSpace I y)) (A B C : Π y : M, TangentSpace I y)
    (hv : ∀ i, Work.Diff.EXT.ATower.SmE I M (v i))
    (hA : Work.Diff.EXT.ATower.SmE I M A) (hB : Work.Diff.EXT.ATower.SmE I M B)
    (hC : Work.Diff.EXT.ATower.SmE I M C) :
    Work.Diff.EXT.ATower.SmF I M (Work.Diff.EXT.ConnCov.htower cov base k v A B C) :=
  htower_smF_aux cov hcov base hsm k v A B C hv hA hB hC

end Work.Diff.EXT.ConnCov.RicTrNT
