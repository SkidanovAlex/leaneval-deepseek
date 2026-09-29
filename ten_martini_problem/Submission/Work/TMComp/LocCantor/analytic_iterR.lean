import Mathlib
import Submission.Work.TMC7Core.Solutions.lyap_periodic

/-!
# Analyticity of the real transfer cocycle in the point

The real iterated transfer matrix `iterR α λ E n x` is a finite product of the transfer
matrices `tmR λ E (x + kα) = !![E - 2λ cos(2π(x + kα)), -1; 1, 0]`, each of whose entries
is a constant or an affine function of `cos`, hence real-analytic in `x`.  This file records
that every entry of `iterR α λ E n ·` is real-analytic on all of `ℝ`.
-/

namespace Work.TMComp.LocCantor

open Set

/-- Every entry of `x ↦ tmR λ E (x + c)` is real-analytic on `ℝ`. -/
theorem analyticOnNhd_tmR (lam E c : ℝ) (i j : Fin 2) :
    AnalyticOnNhd ℝ (fun x : ℝ => Work.TMC7Core.tmR lam E (x + c) i j) Set.univ := by
  fin_cases i <;> fin_cases j <;>
    · simp only [Work.TMC7Core.tmR, Matrix.of_apply, Fin.reduceFinMk,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      intro x _
      fun_prop

/-- Every entry of the real iterated transfer matrix is real-analytic on `ℝ`. -/
theorem analyticOnNhd_iterR_entry (α lam E : ℝ) (n : ℕ) : ∀ i j : Fin 2,
    AnalyticOnNhd ℝ (fun x : ℝ => Work.TMC7Core.Solutions.iterR α lam E n x i j) Set.univ := by
  induction n with
  | zero =>
    intro i j
    have h : (fun x : ℝ => Work.TMC7Core.Solutions.iterR α lam E 0 x i j)
        = fun _ : ℝ => (1 : Matrix (Fin 2) (Fin 2) ℝ) i j := by
      funext x; rw [Work.TMC7Core.Solutions.iterR.eq_1]
    rw [h]
    exact analyticOnNhd_const
  | succ n ih =>
    intro i j
    rw [show (fun x : ℝ => Work.TMC7Core.Solutions.iterR α lam E (n + 1) x i j)
        = (∑ k : Fin 2, fun x : ℝ => Work.TMC7Core.tmR lam E (x + (n : ℝ) * α) i k
              * Work.TMC7Core.Solutions.iterR α lam E n x k j) from by
          funext x
          rw [Work.TMC7Core.Solutions.iterR.eq_2, Matrix.mul_apply]
          simp only [Finset.sum_apply]]
    refine Finset.analyticOnNhd_sum (Finset.univ : Finset (Fin 2)) (fun k _ => ?_)
    exact (analyticOnNhd_tmR lam E ((n : ℝ) * α) i k).mul (ih k j)

theorem analytic_iterR (α lam E : ℝ) (n : ℕ) (i j : Fin 2) :
    AnalyticOnNhd ℝ (fun x : ℝ => Work.TMC7Core.Solutions.iterR α lam E n x i j) Set.univ :=
  analyticOnNhd_iterR_entry α lam E n i j

end Work.TMComp.LocCantor
