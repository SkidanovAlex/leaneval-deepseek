import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Cocycle.frob_mul_le
import Submission.Work.TMC7Core.Cocycle.frob_sqrt_two_le_of_det_one

/-!
# TMC7Core: continuity of the averaged log-Frobenius norm in the energy

For fixed `α, λ, n` the map
`E ↦ (1/(n+1)) ∫_0^1 log ‖A_{n+1}(x; E)‖_F dx`
is continuous on `ℂ`.

The proof has three ingredients:

* `xfrob : ℂ → ℝ → ℝ`, `(E, x) ↦ log (frob (iterC α lam E (n+1) x))` is **jointly**
  continuous: `frob` is continuous (`continuous_frob_matrix`, from its explicit
  definition), `iterC` is jointly continuous (`continuous_iterC_prod`, by induction on
  the number of factors) and `Real.log` is continuous on its support, the transfer
  matrices having determinant `1` so that `frob ≥ √2 > 0` (`frob_iterC_pos`).
* the parametric interval integral of a jointly continuous function is continuous
  (`intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'`).
* division by the constant `(n : ℝ) + 1`.
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMC7Core.Lyap

open Work.TMC7Core

/-! ## Continuity of `frob` -/

/-- `frob` is continuous (it is the square root of a sum of squares of the entries). -/
theorem continuous_frob_matrix : Continuous (fun A : Matrix (Fin 2) (Fin 2) ℂ => frob A) := by
  have h : (fun A : Matrix (Fin 2) (Fin 2) ℂ => frob A)
      = fun A => Real.sqrt (‖A 0 0‖ ^ 2 + ‖A 0 1‖ ^ 2 + ‖A 1 0‖ ^ 2 + ‖A 1 1‖ ^ 2) := rfl
  rw [h]
  fun_prop

/-! ## Joint continuity of the cocycle -/

/-- `(E, x) ↦ A_k(x; E)` is jointly continuous. -/
theorem continuous_iterC_prod (α lam : ℝ) (k : ℕ) :
    Continuous (fun p : ℂ × ℝ => iterC α lam p.1 k p.2) := by
  induction k with
  | zero =>
    simpa [iterC_zero] using
      (continuous_const : Continuous fun _ : ℂ × ℝ => (1 : Matrix (Fin 2) (Fin 2) ℂ))
  | succ k ih =>
    have h : (fun p : ℂ × ℝ => iterC α lam p.1 (k + 1) p.2)
        = fun p : ℂ × ℝ => tmC lam p.1 (p.2 + (k : ℝ) * α) * iterC α lam p.1 k p.2 := rfl
    rw [h]
    refine Continuous.matrix_mul ?_ ih
    apply continuous_matrix
    intro i j
    fin_cases i <;> fin_cases j <;> simp [tmC] <;> fun_prop

/-! ## Positivity of the Frobenius norm -/

/-- The transfer matrices have determinant `1`, hence `frob ≥ √2`; in particular the
Frobenius norm never vanishes and `Real.log` is applied at a genuine point of its
domain. -/
theorem frob_iterC_pos (α lam : ℝ) (E : ℂ) (k : ℕ) (x : ℝ) :
    0 < frob (iterC α lam E k x) := by
  have h2 : Real.sqrt 2 ≤ frob (iterC α lam E k x) :=
    Work.TMC7Core.Cocycle.frob_sqrt_two_le_of_det_one (det_iterC α lam E k x)
  have h3 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  linarith

/-- `(E, x) ↦ log (frob (iterC α lam E k x))` is jointly continuous. -/
theorem continuous_log_frob_iterC_prod (α lam : ℝ) (k : ℕ) :
    Continuous (fun p : ℂ × ℝ => Real.log (frob (iterC α lam p.1 k p.2))) :=
  (continuous_frob_matrix.comp (continuous_iterC_prod α lam k)).log
    (fun p => ne_of_gt (frob_iterC_pos α lam p.1 k p.2))

/-! ## The averaged log-Frobenius norm is continuous in the energy -/

theorem continuous_lyapAvg_energy (α lam : ℝ) (n : ℕ) : Continuous (fun E : ℂ => (∫ x in (0 : ℝ)..1, Real.log (frob (iterC α lam E (n + 1) x))) / ((n : ℝ) + 1)) := by
  have hjoint : Continuous (Function.uncurry
      (fun (E : ℂ) (x : ℝ) => Real.log (frob (iterC α lam E (n + 1) x)))) :=
    continuous_log_frob_iterC_prod α lam (n + 1)
  have hcomp := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) hjoint (0 : ℝ) 1
  exact hcomp.div_const _

end Work.TMC7Core.Lyap

end
