import Mathlib
import Submission.Work.Lattice.MaxNormFlow
import Submission.Work.Lattice.FlowRateAsymptotic

/-!
# The level derivative of the max-norm flow data

Two analytic facts used to identify the **effective capacities** of the accounting
(`MaxNormAccounting`) with the **positions** of the flag members:

* `deriv_eq_of_le_of_eq` — if two functions touch from below at a point and are both
  differentiable there, their derivatives agree;
* `eventually_deriv_log_cnorm_map_flow_eq` — for a fixed `k`-vector `w ≠ 0`, the derivative in
  `t` of `log cnorm (⋀^k a_t w)` is *eventually constant*, equal to the top-block eigenvalue
  `σ_{u₀}`, `u₀ = topBlockIndex ℓ w` (`MaxNormFlow.eventually_cnorm_map_flow_eq_top`).

Module `Submission.Work.Lattice.LevelDeriv`, namespace `Submission.LevelDeriv`.
-/

noncomputable section

open Module exteriorPower Real Filter
open scoped BigOperators Topology
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Submission.LevelDeriv

open Submission.MaxNorm
open Submission.MaxNormFlow
open Submission.FlowRateAsymptotic
open Submission.ExteriorCoordinates
open Submission.DiagonalFlow

variable {d : ℕ}

/-- **Two functions touching from below at a point have the same derivative there.** -/
theorem deriv_eq_of_le_of_eq {f g : ℝ → ℝ} {t₀ : ℝ} (hfd : DifferentiableAt ℝ f t₀)
    (hgd : DifferentiableAt ℝ g t₀) (hle : ∀ t, f t ≤ g t) (heq : f t₀ = g t₀) :
    deriv f t₀ = deriv g t₀ := by
  have hmax : IsLocalMax (fun t => f t - g t) t₀ := by
    filter_upwards with t
    have h := hle t
    have h0 : f t₀ - g t₀ = 0 := by rw [heq]; ring
    linarith [h, h0]
  have hd : deriv (fun t => f t - g t) t₀ = 0 := hmax.deriv_eq_zero
  have hsub : deriv (fun t => f t - g t) t₀ = deriv f t₀ - deriv g t₀ := deriv_sub hfd hgd
  linarith [hd, hsub]

/-- **The derivative of the flowed sup-norm is eventually the top-block eigenvalue.** -/
theorem eventually_deriv_log_cnorm_map_flow_eq {k ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d)
    (hk : k ≤ d) (w : WK d k) (hw : w ≠ 0) :
    ∃ T : ℝ, ∀ t : ℝ, T < t →
      deriv (fun s => Real.log (cnorm (d := d) hk (exteriorPower.map k
          (scaleMap (twoScale (Real.exp (-s / (ℓ : ℝ)))
            (Real.exp (s / ((d - ℓ : ℕ) : ℝ))) ℓ)) w))) t
        = sig (d := d) k ℓ (topBlockIndex (d := d) ℓ w) := by
  obtain ⟨T, hT⟩ := eventually_cnorm_map_flow_eq_top (d := d) hℓ0 hℓd hk w hw
  refine ⟨T, fun t ht => ?_⟩
  set u₀ := topBlockIndex (d := d) ℓ w with hu₀
  set σ := sig (d := d) k ℓ u₀ with hσ
  set c₀ := cnorm (d := d) hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u₀) with hc₀def
  have hc₀pos : 0 < c₀ :=
    cnorm_pos_of_ne_zero (d := d) hk _ (blockElem_topBlockIndex_ne_zero (d := d) (k := k) w hw)
  have hev : (fun s => Real.log (cnorm (d := d) hk (exteriorPower.map k
        (scaleMap (twoScale (Real.exp (-s / (ℓ : ℝ)))
          (Real.exp (s / ((d - ℓ : ℕ) : ℝ))) ℓ)) w))) =ᶠ[𝓝 t]
      (fun s => s * σ + Real.log c₀) := by
    filter_upwards [Ici_mem_nhds ht] with s hs
    rw [hT s hs]
    rw [Real.log_mul (ne_of_gt (Real.exp_pos _)) (ne_of_gt hc₀pos), Real.log_exp]
  have hderiv : HasDerivAt (fun s : ℝ => s * σ + Real.log c₀) σ t := by
    simpa using ((hasDerivAt_id t).mul_const σ).add_const (Real.log c₀)
  exact hev.deriv_eq.trans hderiv.deriv

end Submission.LevelDeriv

end
