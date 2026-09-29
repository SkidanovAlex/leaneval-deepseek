import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Cocycle.log_frob_iterC_nonneg

/-!
# Boundedness below of the averaged log-Frobenius quotients

The quantity whose boundedness is asserted is

`n ↦ (∫₀¹ log ‖A_n(x)‖_F dx) / n`,

the averaged logarithm of the Frobenius norm of the `n`-th transfer iterate, divided by `n`
(this is the sequence whose infimum is the Lyapunov exponent, cf. `lyap`).

Every iterate `A_n(x)` of the transfer cocycle has determinant one (`det_iterC`), so its
Frobenius norm is at least `√2 > 1` (`frob_sqrt_two_le_of_det_one`), and therefore
`log ‖A_n(x)‖_F ≥ 0` for every `n` and `x` (`Cocycle.log_frob_iterC_nonneg`).  Integrating,
every numerator is nonnegative; dividing by the (nonnegative) `n` — and using Lean's
convention `x / 0 = 0` for the term `n = 0` — leaves every value nonnegative.  Hence the set
is bounded below by `0`.
-/

open MeasureTheory Filter Topology Set

namespace Work.TMC7Core.Lyap

theorem lyap_bddBelow (α lam : ℝ) (E : ℂ) : BddBelow (Set.range fun n : ℕ => (∫ x in (0 : ℝ)..1, Real.log (frob (iterC α lam E n x))) / (n : ℝ)) := by
  refine ⟨0, ?_⟩
  rintro y ⟨n, rfl⟩
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp
  · have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    refine div_nonneg ?_ (le_of_lt hpos)
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun x _ => Cocycle.log_frob_iterC_nonneg α lam E n x)

end Work.TMC7Core.Lyap
