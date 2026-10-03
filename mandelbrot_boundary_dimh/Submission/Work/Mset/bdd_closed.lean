import Mathlib
import Submission.Work.Interfaces.Basic

/-!
# Closedness of the bounded-orbit locus `{c | ∀ n, ‖T_c^n(0)‖ ≤ 2}`

The `n`-th iterate of the critical point `0` under `T_c` is a polynomial function
of `c` (recursively `z_{n+1} = z_n² + c`, `z_0 = 0`), hence continuous in `c`.
Therefore each sublevel set `{c | ‖T_c^n(0)‖ ≤ 2}` is closed, and the whole
bounded-orbit locus is their (countable) intersection.
-/

namespace Work.Mset

open LeanEval.Dynamics.MandelbrotBoundary

/-- The `n`-th iterate of `T_c` at the critical point `0` is a continuous
(polynomial) function of the parameter `c`. -/
theorem continuous_iterate_zero (n : ℕ) :
    Continuous fun c : ℂ => (Tc c)^[n] 0 := by
  induction n with
  | zero => simpa using continuous_const
  | succ n ih =>
    have h : (fun c : ℂ => (Tc c)^[n + 1] 0)
        = fun c : ℂ => (((Tc c)^[n] 0) ^ 2 + c) := by
      funext c
      rw [Function.iterate_succ_apply']
      rfl
    rw [h]
    exact (ih.pow 2).add continuous_id

theorem bdd_closed :
    IsClosed {c : ℂ | ∀ n : ℕ, ‖(LeanEval.Dynamics.MandelbrotBoundary.Tc c)^[n] 0‖ ≤ 2} := by
  have h : {c : ℂ | ∀ n : ℕ, ‖(Tc c)^[n] 0‖ ≤ 2}
      = ⋂ n, {c : ℂ | ‖(Tc c)^[n] 0‖ ≤ 2} := by
    ext c
    simp
  rw [h]
  refine isClosed_iInter fun n => ?_
  exact IsClosed.preimage ((continuous_iterate_zero n).norm) isClosed_Iic

end Work.Mset
