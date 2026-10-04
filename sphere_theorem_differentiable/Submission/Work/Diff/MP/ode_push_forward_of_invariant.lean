import Mathlib
import Submission.Work.Diff.MP.Basic
import Submission.Work.Diff.MP.Q_sub_norm_le
import Submission.Work.Diff.MP.exists_local_solution_Q
import Submission.Work.Diff.MP.ode_taylor_estimates

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The one-step push-forward of an ODE-invariant family

If the fibrewise set `K t` is invariant under Hamilton's ODE `R' = Q R`, then for every
`S ∈ K t` there is a curve `Ψ` on a small interval `[0, δ]` with `Ψ 0 = S`, `Ψ h ∈ K (t + h)` and
the uniform Taylor bounds
`frobDist (Ψ h) (S + h • Q S) ≤ C h²`, `frobNorm (Ψ h - S) ≤ C h`.

The curve is the local solution `α` of the ODE `α' = Q (α)` with `α 0 = S`; the membership is the
invariance hypothesis applied to the time-shifted curve `h ↦ α (h - t)` started at time `t`
(note that the interval in the definition of `ODEInvariantFamily` is left-closed, so the shift has
to be run up to `t + ε`, not just `t + δ`).  The two estimates are the second-order Taylor
expansion of `α` at `0` (module `Submission.Work.Diff.MP.ode_taylor_estimates`), translated from
the sup norm `‖·‖` on `Curv4 n` to the Frobenius norm by `Work.Diff.MP.frobNorm_le_mul_norm`.
-/

namespace Work.Diff.MP

open Set Submission.Diff.Alg
open Work.Diff.MP

theorem ode_push_forward_of_invariant (n : ℕ) (K : ℝ → Set (Curv4 n))
    (hK : ODEInvariantFamily K) (t : ℝ) (S : Curv4 n) (hS : S ∈ K t) :
    ∃ δ > 0, ∃ C : ℝ, 0 ≤ C ∧ ∃ Ψ : ℝ → Curv4 n, Ψ 0 = S ∧
      (∀ h ∈ Icc 0 δ, Ψ h ∈ K (t + h)) ∧
      (∀ h ∈ Icc 0 δ, frobDist (Ψ h) (S + h • Q S) ≤ C * h ^ 2) ∧
      (∀ h ∈ Icc 0 δ, frobNorm (Ψ h - S) ≤ C * h) := by
  -- The elementary quadratic estimate for Hamilton's reaction term, with `c = 5 n²`.
  have hQ : ∀ R T : Curv4 n, ‖Q R - Q T‖ ≤ 5 * (n : ℝ) ^ 2 * (‖R‖ + ‖T‖) * ‖R - T‖ :=
    fun R T => Q_sub_norm_le n R T
  have hc : (0 : ℝ) ≤ 5 * (n : ℝ) ^ 2 := by positivity
  -- A local solution of `α' = Q α` with `α 0 = S`, and its Taylor estimates on `[0, δ]`.
  obtain ⟨ε, hε, α, hα0, hODE⟩ := exists_local_solution_Q n S
  obtain ⟨δ, hδ, hδε, C, hC, hQuad, hLin⟩ :=
    ode_taylor_estimates n S ε hε α hα0 hODE (5 * (n : ℝ) ^ 2) hc hQ
  refine ⟨δ, hδ, (n : ℝ) ^ 2 * C, mul_nonneg (sq_nonneg _) hC, α, hα0, ?_, ?_, ?_⟩
  · -- `α h ∈ K (t + h)`: invariance applied to the time-shifted solution.
    intro h hh
    have hR : ∀ s ∈ Ico t (t + ε), HasDerivWithinAt (fun s : ℝ => α (s - t))
        (Q (α (s - t))) (Ico t (t + ε)) s := by
      intro s hs
      have hu : s - t ∈ Ioo (-ε) ε := ⟨by linarith [hs.1], by linarith [hs.2]⟩
      have h1 : HasDerivAt α (Q (α (s - t))) (s - t) := hODE (s - t) hu
      have h2 : HasDerivWithinAt (fun s : ℝ => s - t) 1 (Ico t (t + ε)) s :=
        ((hasDerivAt_id s).sub_const t).hasDerivWithinAt
      have h3 := HasDerivAt.scomp_hasDerivWithinAt (x := s) (h := fun s : ℝ => s - t) h1 h2
      rw [one_smul] at h3
      exact h3
    have h0 : (fun s : ℝ => α (s - t)) t ∈ K t := by
      simp only [sub_self, hα0]
      exact hS
    have hres := hK t (t + ε) (fun s : ℝ => α (s - t)) h0 hR
    have hs : t + h ∈ Ico t (t + ε) := ⟨by linarith [hh.1], by linarith [hh.2, hδε]⟩
    have := hres (t + h) hs
    simpa using this
  · -- Second order remainder, in the Frobenius distance.
    intro h hh
    have h1 := frobNorm_le_mul_norm (α h - (S + h • Q S))
    have h2 := hQuad h hh
    have h3 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := sq_nonneg _
    calc frobDist (α h) (S + h • Q S) = frobNorm (α h - (S + h • Q S)) := rfl
      _ ≤ (n : ℝ) ^ 2 * ‖α h - (S + h • Q S)‖ := h1
      _ ≤ (n : ℝ) ^ 2 * (C * h ^ 2) := mul_le_mul_of_nonneg_left h2 h3
      _ = ((n : ℝ) ^ 2 * C) * h ^ 2 := by ring
  · -- First order remainder, in the Frobenius norm.
    intro h hh
    have h1 := frobNorm_le_mul_norm (α h - S)
    have h2 := hLin h hh
    have h3 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := sq_nonneg _
    calc frobNorm (α h - S) ≤ (n : ℝ) ^ 2 * ‖α h - S‖ := h1
      _ ≤ (n : ℝ) ^ 2 * (C * h) := mul_le_mul_of_nonneg_left h2 h3
      _ = ((n : ℝ) ^ 2 * C) * h := by ring

end Work.Diff.MP
