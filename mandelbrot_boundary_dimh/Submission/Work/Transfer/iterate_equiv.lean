import Mathlib
import Submission.Work.Transfer.Setup

open LeanEval.Dynamics.MandelbrotBoundary

namespace Work.Transfer

/-- Iterating the equivariance relation of `MotionData` along the first `k` letters of a code:
the `k`-th partial product of the branch degrees `n (u j)` applied to `phi c u` is the point of the
limit set coded by the shifted word `j ↦ u (j + k)`. -/
theorem iterate_equiv {N : ℕ} {c₀ : ℂ} {τ : Fin N → ℂ → ℂ} {n : Fin N → ℕ} {p : ℂ} {ρ a : ℝ}
    {phi : ℂ → (ℕ → Fin N) → ℂ} (hMD : Work.Transfer.MotionData c₀ N τ n p ρ a phi)
    {c : ℂ} (hc : c ∈ Metric.ball c₀ ρ) (u : ℕ → Fin N) (k : ℕ) :
    (LeanEval.Dynamics.MandelbrotBoundary.Tc c)^[∑ j ∈ Finset.range k, n (u j)] (phi c u)
      = phi c (fun j => u (j + k)) := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    have hA : (∑ j ∈ Finset.range (k + 1), n (u j))
        = (∑ j ∈ Finset.range k, n (u j)) + n (u k) :=
      Finset.sum_range_succ _ _
    rw [hA]
    have hstep : (Tc c)^[(∑ j ∈ Finset.range k, n (u j)) + n (u k)] (phi c u)
        = (Tc c)^[n (u k)] ((Tc c)^[∑ j ∈ Finset.range k, n (u j)] (phi c u)) := by
      rw [Nat.add_comm, Function.iterate_add_apply]
    rw [hstep, ih]
    have heq := hMD.equiv c hc (fun j => u (j + k))
    simp only [Nat.zero_add] at heq
    rw [heq]
    congr 1
    funext j
    exact congrArg u (by omega)

end Work.Transfer
