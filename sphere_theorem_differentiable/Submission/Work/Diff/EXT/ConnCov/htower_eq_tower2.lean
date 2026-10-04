import Mathlib
import Submission.Work.Diff.EXT.ConnCov.honestTower
import Submission.Work.Diff.EXT.ConnCov.RicTowerDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false

namespace Work.Diff.EXT.ConnCov

open Work.Diff.EXT.ATower

section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- The lift of an `Op2 k` to an `Op3 k` with a **dummy third value slot** — the level-`k` version
of `lift23` (which only exists at level `0`).  Both `baseRic g` and the `(0,2)`-tower `tower2`
ignore their third value slot, and this is the object that makes that precise. -/
noncomputable def lift23k {k : ℕ} (σ : Op2 (I := I) (M := M) k) : Op3 (I := I) (M := M) k :=
  fun v A B _ y => σ v A B y

/-- **The honest recursion step commutes with the lift.**  `hstep cov τ = step cov τ + drop τ`,
and on a lifted object the third-slot correction of `step` (`−τ ... B (∇C)`) is exactly cancelled
by the `drop` term `τ v_{>0} A B C`: for the lift the two are the same number `σ v_{>0} A B x`.
So `hstep` on a lift is the `(0,2)`-tensor recursion step `step2`. -/
theorem hstep_lift23k (cov : CovariantDerivative I E (TangentSpace I (M := M))) {k : ℕ}
    (σ : Op2 (I := I) (M := M) k) :
    hstep cov (lift23k σ) = lift23k (step2 cov σ) := by
  funext v A B C x
  simp only [hstep, lift23k, step, step2, drop, Pi.add_apply]
  rw [show (lift23k σ) (fun i : Fin k => v i.succ) A B C = σ (fun i : Fin k => v i.succ) A B
        from rfl]
  ring

/-- **The honest tower of a lifted `(0,2)`-base is the honest `(0,2)`-tower of the base.**
Immediate induction from `hstep_lift23k`. -/
theorem htower_lift23k (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (β : Op2 (I := I) (M := M) 0) (k : ℕ) :
    htower cov (lift23k β) k = lift23k (tower2 cov β k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [htower_succ, ih, hstep_lift23k]; rfl

end

/-- `baseRic` is the lift of `baseRic2` (definitionally). -/
theorem baseRic_eq_lift23k_baseRic2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (g : Submission.Diff.SMet I M) :
    baseRic (I := I) (M := M) g = lift23k (baseRic2 (I := I) (M := M) g) := rfl

theorem htower_eq_tower2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (g : Submission.Diff.SMet I M) (k : ℕ)
    (v : Fin k → (Π y : M, TangentSpace I y)) (A B C : Π y : M, TangentSpace I y) (x : M) :
    Work.Diff.EXT.ConnCov.htower (Submission.Diff.lcOf g)
        (Work.Diff.EXT.ConnCov.baseRic (I := I) (M := M) g) k v A B C x
      = Work.Diff.EXT.ConnCov.tower2 (Submission.Diff.lcOf g)
        (Work.Diff.EXT.ConnCov.baseRic2 (I := I) (M := M) g) k v A B x := by
  have h := htower_lift23k (I := I) (M := M) (Submission.Diff.lcOf g)
    (baseRic2 (I := I) (M := M) g) k
  exact congrFun (congrFun (congrFun (congrFun (congrFun h v) A) B) C) x

end Work.Diff.EXT.ConnCov
