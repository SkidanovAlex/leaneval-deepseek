import Mathlib
import Submission.Work.Diff.EXT.ATower.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.ATower

theorem step_flip
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    {k : ℕ} (τ : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) k) (hτ : Work.Diff.EXT.ATower.SlotAdd τ)
    {cov cov' : CovariantDerivative I E (TangentSpace I (M := M))}
    (δ : (Π y : M, TangentSpace I y) → (Π y : M, TangentSpace I y) → (Π y : M, TangentSpace I y))
    (hcov : ∀ (Y Z : Π y : M, TangentSpace I y), Work.Diff.EXT.ATower.SmE I M Y → Work.Diff.EXT.ATower.SmE I M Z →
      Work.Diff.EXT.ATower.SmE I M (fun y => cov Y y (Z y)))
    (hcov' : ∀ (Y Z : Π y : M, TangentSpace I y), Work.Diff.EXT.ATower.SmE I M Y → Work.Diff.EXT.ATower.SmE I M Z →
      Work.Diff.EXT.ATower.SmE I M (fun y => cov' Y y (Z y)))
    (hδsm : ∀ (Y Z : Π y : M, TangentSpace I y), Work.Diff.EXT.ATower.SmE I M Y → Work.Diff.EXT.ATower.SmE I M Z →
      Work.Diff.EXT.ATower.SmE I M (fun y => δ Y Z y))
    (hδ : ∀ (Y Z : Π y : M, TangentSpace I y), Work.Diff.EXT.ATower.SmE I M Y → Work.Diff.EXT.ATower.SmE I M Z → ∀ y : M,
      cov' Y y (Z y) = cov Y y (Z y) + δ Y Z y)
    (v : Fin (k + 1) → (Π y : M, TangentSpace I y)) (A B C : Π y : M, TangentSpace I y)
    (hv : ∀ j, Work.Diff.EXT.ATower.SmE I M (v j)) (hA : Work.Diff.EXT.ATower.SmE I M A) (hB : Work.Diff.EXT.ATower.SmE I M B) (hC : Work.Diff.EXT.ATower.SmE I M C) :
    Work.Diff.EXT.ATower.step cov τ v A B C = fun x => Work.Diff.EXT.ATower.step cov' τ v A B C x
      + (∑ i : Fin k, Work.Diff.EXT.ATower.insD i δ τ v A B C x)
      + Work.Diff.EXT.ATower.insA δ τ v A B C x + Work.Diff.EXT.ATower.insB δ τ v A B C x + Work.Diff.EXT.ATower.insC δ τ v A B C x := by
  funext x
  -- Unfold the two `step`s and use `SlotAdd τ` slot by slot: the `cov'`-correction field is the
  -- `cov`-correction field plus the `δ`-field, pointwise.
  have hsum' : (∑ i : Fin k, τ (Function.update (fun j : Fin k => v j.succ) i
          (fun y => cov' (v i.succ) y (v 0 y))) A B C x)
      = (∑ i : Fin k, τ (Function.update (fun j : Fin k => v j.succ) i
            (fun y => cov (v i.succ) y (v 0 y))) A B C x)
        + (∑ i : Fin k, τ (Function.update (fun j : Fin k => v j.succ) i
            (fun y => δ (v i.succ) (v 0) y)) A B C x) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by
      have hfield : (fun y : M => cov' (v i.succ) y (v 0 y))
          = (fun y : M => cov (v i.succ) y (v 0 y))
            + (fun y : M => δ (v i.succ) (v 0) y) := by
        funext y
        exact hδ (v i.succ) (v 0) (hv _) (hv 0) y
      rw [hfield]
      exact congrFun (hτ.1 i (fun j : Fin k => v j.succ) (fun y => cov (v i.succ) y (v 0 y))
        (fun y => δ (v i.succ) (v 0) y) A B C (fun j => hv j.succ)
        (hcov (v i.succ) (v 0) (hv _) (hv 0)) (hδsm (v i.succ) (v 0) (hv _) (hv 0)) hA hB hC) x
  have hA' : τ (fun j : Fin k => v j.succ) (fun y => cov' A y (v 0 y)) B C x
      = τ (fun j : Fin k => v j.succ) (fun y => cov A y (v 0 y)) B C x
        + τ (fun j : Fin k => v j.succ) (fun y => δ A (v 0) y) B C x := by
    have hfield : (fun y : M => cov' A y (v 0 y))
        = (fun y : M => cov A y (v 0 y)) + (fun y : M => δ A (v 0) y) := by
      funext y
      exact hδ A (v 0) hA (hv 0) y
    rw [hfield]
    exact congrFun (hτ.2.1 (fun j : Fin k => v j.succ) (fun y => cov A y (v 0 y))
      (fun y => δ A (v 0) y) B C (fun j => hv j.succ) (hcov A (v 0) hA (hv 0))
      (hδsm A (v 0) hA (hv 0)) hB hC) x
  have hB' : τ (fun j : Fin k => v j.succ) A (fun y => cov' B y (v 0 y)) C x
      = τ (fun j : Fin k => v j.succ) A (fun y => cov B y (v 0 y)) C x
        + τ (fun j : Fin k => v j.succ) A (fun y => δ B (v 0) y) C x := by
    have hfield : (fun y : M => cov' B y (v 0 y))
        = (fun y : M => cov B y (v 0 y)) + (fun y : M => δ B (v 0) y) := by
      funext y
      exact hδ B (v 0) hB (hv 0) y
    rw [hfield]
    exact congrFun (hτ.2.2.1 (fun j : Fin k => v j.succ) A (fun y => cov B y (v 0 y))
      (fun y => δ B (v 0) y) C (fun j => hv j.succ) hA (hcov B (v 0) hB (hv 0))
      (hδsm B (v 0) hB (hv 0)) hC) x
  have hC' : τ (fun j : Fin k => v j.succ) A B (fun y => cov' C y (v 0 y)) x
      = τ (fun j : Fin k => v j.succ) A B (fun y => cov C y (v 0 y)) x
        + τ (fun j : Fin k => v j.succ) A B (fun y => δ C (v 0) y) x := by
    have hfield : (fun y : M => cov' C y (v 0 y))
        = (fun y : M => cov C y (v 0 y)) + (fun y : M => δ C (v 0) y) := by
      funext y
      exact hδ C (v 0) hC (hv 0) y
    rw [hfield]
    exact congrFun (hτ.2.2.2 (fun j : Fin k => v j.succ) A B (fun y => cov C y (v 0 y))
      (fun y => δ C (v 0) y) (fun j => hv j.succ) hA hB (hcov C (v 0) hC (hv 0))
      (hδsm C (v 0) hC (hv 0))) x
  simp only [Work.Diff.EXT.ATower.step, Work.Diff.EXT.ATower.insD, Work.Diff.EXT.ATower.insA,
    Work.Diff.EXT.ATower.insB, Work.Diff.EXT.ATower.insC]
  rw [hsum', hA', hB', hC']
  ring

end Work.Diff.EXT.ATower
