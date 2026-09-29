import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.FtbAux.floquet_core
import Submission.Work.TMC7Core.Solutions.block_transfer
import Submission.Work.TMC7Core.Solutions.iterC_mulVec_solution

/-!
# General-phase block transfer for the rational almost Mathieu operator

The `q`-periodic potential of the almost Mathieu operator at rational frequency `α = p/q`
is invariant under shifts of the index by multiples of `q`, *at every phase* `θ`
(`amoPot_shift_period_phase`).  Consequently the `q`-step transfer matrix
`A_q(θ) = iterC α lam E q θ = S(θ+(q-1)α)⋯S(θ)` advances the state over one period block,
`W (k+1) = A_q(θ) ·ᵥ W k` with `W k = (u (k q), u (k q - 1))`, for any formal solution `u`
of the eigenvalue equation at phase `θ` (`block_transfer_phase`).

This is the phase-`θ` analogue of `Work.TMC7Core.Solutions.block_transfer` (which is stated
for phase `0`); the phase drop out of the period argument because `tmC` is `1`-periodic in its
argument, so `S(θ + k q α) = S(θ + k p) = S(θ)`.
-/

namespace Work.TMC7Core.Scale

open Work.TMC7Core

/-- For `α = p / q` with `q ≥ 1`, the almost Mathieu potential at phase `θ` is invariant
under a shift of the index by an integer multiple of `q`. -/
lemma amoPot_shift_period_phase (p : ℤ) (q : ℕ) (hq : 1 ≤ q) (lam θ : ℝ) (k n : ℤ) :
    amoPot ((p : ℝ) / (q : ℝ)) lam θ (n + k * (q : ℤ)) =
      amoPot ((p : ℝ) / (q : ℝ)) lam θ n := by
  have hqα : (q : ℝ) * ((p : ℝ) / (q : ℝ)) = (p : ℝ) := by
    have : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    field_simp
  simp only [amoPot]
  have hcos : Real.cos (2 * Real.pi * (θ + (((n + k * (q : ℤ) : ℤ)) : ℝ) * ((p : ℝ) / (q : ℝ))))
      = Real.cos (2 * Real.pi * (θ + (n : ℝ) * ((p : ℝ) / (q : ℝ)))) := by
    have harg : 2 * Real.pi * (θ + (((n + k * (q : ℤ) : ℤ)) : ℝ) * ((p : ℝ) / (q : ℝ)))
        = 2 * Real.pi * (θ + (n : ℝ) * ((p : ℝ) / (q : ℝ))) + ((k * p : ℤ) : ℝ) * (2 * Real.pi) := by
      push_cast
      rw [add_mul]
      have hk : (k : ℝ) * (q : ℝ) * ((p : ℝ) / (q : ℝ)) = (k : ℝ) * (p : ℝ) := by
        rw [mul_assoc, hqα]
      rw [hk]; ring
    rw [harg, Real.cos_add_int_mul_two_pi]
  exact congrArg (fun z => 2 * lam * z) hcos

/-- **Block transfer at phase `θ`.**  If `u` solves the almost Mathieu eigenvalue equation
with rational frequency `α = p/q` and phase `θ`, then the `q`-step transfer matrix at energy
`E` maps the pair `(u (k q), u (k q - 1))` to `(u ((k+1) q), u ((k+1) q - 1))`, for every
`k : ℤ`. -/
theorem block_transfer_phase (p : ℤ) (q : ℕ) (hq : 1 ≤ q) (lam θ E : ℝ) (u : ℤ → ℂ)
    (hu : ∀ n : ℤ, amoAct ((p : ℝ) / (q : ℝ)) lam θ u n = (E : ℂ) * u n) (k : ℤ) :
    (iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q θ).mulVec ![u (k * q), u (k * q - 1)]
      = ![u ((k + 1) * q), u ((k + 1) * q - 1)] := by
  have hpot : ∀ n : ℤ, amoPot ((p : ℝ) / (q : ℝ)) lam θ (n + k * (q : ℤ)) =
      amoPot ((p : ℝ) / (q : ℝ)) lam θ n :=
    fun n => amoPot_shift_period_phase p q hq lam θ k n
  set v : ℤ → ℂ := fun n => u (n + k * (q : ℤ)) with hv
  have hv_sol : ∀ n : ℤ, amoAct ((p : ℝ) / (q : ℝ)) lam θ v n = (E : ℂ) * v n := by
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
  have hmain := Solutions.iterC_mulVec_solution ((p : ℝ) / (q : ℝ)) lam θ E v hv_sol q
  have hv0 : v 0 = u (k * q) := by rw [hv]; simp
  have hvm1 : v (-1) = u (k * q - 1) := by rw [hv]; beta_reduce; congr 1; ring
  have hvq : v (q : ℤ) = u ((k + 1) * q) := by rw [hv]; beta_reduce; congr 1; ring
  have hvq1 : v ((q : ℤ) - 1) = u ((k + 1) * q - 1) := by rw [hv]; beta_reduce; congr 1; ring
  rw [show ![u (k * q), u (k * q - 1)] = ![v 0, v (-1)] by rw [hv0, hvm1], hmain,
      show ![v (q : ℤ), v ((q : ℤ) - 1)] = ![u ((k + 1) * q), u ((k + 1) * q - 1)] by rw [hvq, hvq1]]

end Work.TMC7Core.Scale
