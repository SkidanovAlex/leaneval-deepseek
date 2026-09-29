import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Solutions.iterC_mulVec_solution

/-!
# Block transfer for the rational almost Mathieu operator

For `α = p / q` the potential `n ↦ 2λ cos 2π(n α)` of the almost Mathieu operator is periodic
with period `q`.  Consequently, if `u` is a formal solution of the eigenvalue equation
`amoAct α lam 0 u = E u`, then so is the sequence `n ↦ u (n + k q)` for every `k : ℤ`, and
applying the `q`-step transfer matrix `iterC α lam E q 0` to the pair `(u (k q), u (k q - 1))`
produces `(u ((k+1) q), u ((k+1) q - 1))`.  This is the Floquet step that lifts a solution
from one period block to the next.
-/

namespace Work.TMC7Core.Solutions

open Work.TMC7Core

/-- For `α = p / q` with `q ≥ 1`, the phase-`0` almost Mathieu potential is invariant under a
shift of the index by an integer multiple of `q`. -/
lemma amoPot_shift_period (p : ℤ) (q : ℕ) (hq : 1 ≤ q) (lam : ℝ) (k n : ℤ) :
    amoPot ((p : ℝ) / (q : ℝ)) lam 0 (n + k * (q : ℤ)) =
      amoPot ((p : ℝ) / (q : ℝ)) lam 0 n := by
  have hqα : (q : ℝ) * ((p : ℝ) / (q : ℝ)) = (p : ℝ) := by
    have : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    field_simp
  have hcos : Real.cos (2 * Real.pi * (((n + k * (q : ℤ) : ℤ) : ℝ) * ((p : ℝ) / (q : ℝ))))
      = Real.cos (2 * Real.pi * ((n : ℝ) * ((p : ℝ) / (q : ℝ)))) := by
    have harg : (2 * Real.pi) * (((n + k * (q : ℤ) : ℤ) : ℝ) * ((p : ℝ) / (q : ℝ)))
        = (2 * Real.pi) * ((n : ℝ) * ((p : ℝ) / (q : ℝ)))
          + ((k * p : ℤ) : ℝ) * (2 * Real.pi) := by
      push_cast
      rw [add_mul]
      have hk : (k : ℝ) * (q : ℝ) * ((p : ℝ) / (q : ℝ)) = (k : ℝ) * (p : ℝ) := by
        rw [mul_assoc, hqα]
      rw [hk]
      ring
    rw [harg, Real.cos_add_int_mul_two_pi]
  simp only [amoPot, zero_add]
  rw [hcos]

/-- **Block transfer.**  If `u` solves the almost Mathieu eigenvalue equation with rational
frequency `α = p/q` and phase `0`, then the `q`-step transfer matrix at energy `E` maps the
pair `(u (k q), u (k q - 1))` to `(u ((k+1) q), u ((k+1) q - 1))`, for every `k : ℤ`. -/
theorem block_transfer (p : ℤ) (q : ℕ) (hq : 1 ≤ q) (lam E : ℝ) (u : ℤ → ℂ)
    (hu : ∀ n : ℤ, Work.TMC7Core.amoAct ((p : ℝ) / (q : ℝ)) lam 0 u n = (E : ℂ) * u n) (k : ℤ) :
    (Work.TMC7Core.iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q 0).mulVec ![u (k * q), u (k * q - 1)]
      = ![u ((k + 1) * q), u ((k + 1) * q - 1)] := by
  have hpot : ∀ n : ℤ, amoPot ((p : ℝ) / (q : ℝ)) lam 0 (n + k * (q : ℤ)) =
      amoPot ((p : ℝ) / (q : ℝ)) lam 0 n := fun n => amoPot_shift_period p q hq lam k n
  -- The sequence `v n = u (n + k q)` solves the same difference equation, because the
  -- potential is `q`-periodic.
  set v : ℤ → ℂ := fun n => u (n + k * (q : ℤ)) with hv
  have hv_sol : ∀ n : ℤ, amoAct ((p : ℝ) / (q : ℝ)) lam 0 v n = (E : ℂ) * v n := by
    intro n
    have h := hu (n + k * (q : ℤ))
    simp only [amoAct] at h ⊢
    rw [hpot n] at h
    have hn1 : v (n + 1) = u (n + 1 + k * (q : ℤ)) := rfl
    have hnm1 : v (n - 1) = u (n - 1 + k * (q : ℤ)) := rfl
    have hn : v n = u (n + k * (q : ℤ)) := rfl
    rw [hn1, hnm1, hn]
    rw [show u (n + 1 + k * (q : ℤ)) = u ((n + k * (q : ℤ)) + 1) from by congr 1; ring,
        show u (n - 1 + k * (q : ℤ)) = u ((n + k * (q : ℤ)) - 1) from by congr 1; ring]
    exact h
  -- One period of the cocycle moves `(v 0, v (-1))` to `(v q, v (q-1))`.
  have hmain := iterC_mulVec_solution ((p : ℝ) / (q : ℝ)) lam 0 E v hv_sol q
  have hv0 : v 0 = u (k * q) := by rw [hv]; simp
  have hvm1 : v (-1) = u (k * q - 1) := by rw [hv]; beta_reduce; congr 1; ring
  have hvq : v (q : ℤ) = u ((k + 1) * q) := by rw [hv]; beta_reduce; congr 1; ring
  have hvq1 : v ((q : ℤ) - 1) = u ((k + 1) * q - 1) := by
    rw [hv]; beta_reduce; congr 1; ring
  rw [show ![u (k * q), u (k * q - 1)] = ![v 0, v (-1)] by rw [hv0, hvm1], hmain,
      show ![v (q : ℤ), v ((q : ℤ) - 1)] = ![u ((k + 1) * q), u ((k + 1) * q - 1)] by
        rw [hvq, hvq1]]

end Work.TMC7Core.Solutions
