import Mathlib
import Submission.Work.Interfaces.Basic

namespace Work.Mset

open LeanEval.Dynamics.MandelbrotBoundary Filter

theorem escape (c z : ℂ) (hz : 2 < ‖z‖) (hc : ‖c‖ ≤ ‖z‖) :
    (∀ k : ℕ, ‖z‖ * (‖z‖ - 1) ^ k ≤ ‖(LeanEval.Dynamics.MandelbrotBoundary.Tc c)^[k] z‖) ∧
    Filter.Tendsto (fun k : ℕ => ‖(LeanEval.Dynamics.MandelbrotBoundary.Tc c)^[k] z‖) Filter.atTop Filter.atTop := by
  have hrpos : 0 < ‖z‖ := by linarith
  have hr1 : 1 < ‖z‖ - 1 := by linarith
  have step : ∀ w : ℂ, ‖z‖ ≤ ‖w‖ → (‖z‖ - 1) * ‖w‖ ≤ ‖Tc c w‖ := by
    intro w hw
    have h2 : ‖w ^ 2‖ - ‖c‖ ≤ ‖Tc c w‖ := by
      have h := norm_sub_norm_le (w ^ 2) (-c)
      simpa [Tc, norm_neg, sub_neg_eq_add] using h
    rw [norm_pow] at h2
    have hprod : 0 ≤ (‖w‖ - ‖z‖) * (‖w‖ + 1) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [h2, hc, hprod]
  have hmain : ∀ k : ℕ, ‖z‖ * (‖z‖ - 1) ^ k ≤ ‖(Tc c)^[k] z‖ := by
    intro k
    induction k with
    | zero => simp
    | succ n ih =>
      have hge : ‖z‖ ≤ ‖(Tc c)^[n] z‖ := by
        have h1 : ‖z‖ ≤ ‖z‖ * (‖z‖ - 1) ^ n := by
          have : (1:ℝ) ≤ (‖z‖ - 1) ^ n := one_le_pow₀ (by linarith)
          nlinarith [hrpos]
        linarith
      calc ‖z‖ * (‖z‖ - 1) ^ (n + 1)
          = (‖z‖ - 1) * (‖z‖ * (‖z‖ - 1) ^ n) := by ring
        _ ≤ (‖z‖ - 1) * ‖(Tc c)^[n] z‖ := mul_le_mul_of_nonneg_left ih (by linarith)
        _ ≤ ‖Tc c ((Tc c)^[n] z)‖ := step _ hge
        _ = ‖(Tc c)^[n+1] z‖ := by rw [Function.iterate_succ_apply']
  refine ⟨hmain, ?_⟩
  have htend : Tendsto (fun k : ℕ => ‖z‖ * (‖z‖ - 1) ^ k) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (r := ‖z‖ - 1) hr1).const_mul_atTop hrpos
  exact tendsto_atTop_mono hmain htend

end Work.Mset
