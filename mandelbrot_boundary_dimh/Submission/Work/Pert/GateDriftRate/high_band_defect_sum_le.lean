import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup
import Submission.Work.Pert.sigma_le_norm_alpha
import Submission.Work.Pert.tauC_decay_high
import Submission.Work.Pert.liftF_defect_le_tau_explicit
import Submission.Work.Pert.GateDriftRate.high_decay_sum_uniform

/-!
# `Work.Pert.GateDriftRate.high_band_defect_sum_le`

The contribution of the **high band** `1 ≤ Im (α w)` of a legal walk `w_j = F^[j] z`
(`F = liftF u σ α`) in the lower gate `Qm Ξ α` to the defect sum of the drift estimate:

  `∑_{j<n, 1 ≤ Im (α w_j)} ‖F (w_j) - (w_j + 1)‖ ≤ 2^28 (1 + Ξ + 1/Ξ + 1/rr) (1 + log (2+M) + log (2+‖z‖))`.

The estimate is *uniform in the length* of the walk: in the high band the defect is controlled by
`‖τ_f (w_j)‖`, which decays like `exp (-2π Im (α w_j))`, and the weighted count
`‖α‖ * ∑_{j∈J} exp (-2π Im (α w_j))` is bounded uniformly in `Ξ` — the delegated lemma
`Work.Pert.GateDriftRate.high_decay_sum_uniform`.

The two analytic inputs are already proved in the workspace:

* `Work.Pert.liftF_defect_le_tau_explicit` (explicit constant `2^12 (1 + 1/rr)`),
* `Work.Pert.tauC_decay_high` (with `‖σ‖ ≤ 32 ‖α‖` from `Work.Pert.sigma_le_norm_alpha`).
-/

namespace Work.Pert.GateDriftRate

set_option linter.unusedVariables false

open MandelDim Complex
open scoped BigOperators

noncomputable section

theorem high_band_defect_sum_le {Ξ rr M : ℝ} {α σ : ℂ} {u : ℂ → ℂ} {z : ℂ} {n : ℕ}
    (hΞ : 0 < Ξ) (hrr : 0 < rr) (hM : 2 ^ 10 ≤ M) (hInF1 : MandelDim.InF1 α)
    (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ)))
    (hσ : σ ≠ 0) (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr))
    (hu2 : ∀ w ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u w‖ ∧ ‖u w‖ ≤ 2)
    (hτQ : ∀ w ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α w ∈ Metric.ball (0 : ℂ) rr)
    (hNT : ∀ w ∈ Work.Pert.Qm Ξ α, ‖Work.Pert.liftF u σ α w - (w + 1)‖ ≤ 1 / 32)
    (hz : z ∈ Work.Pert.Qm Ξ α)
    (hwalk : ∀ j ≤ n, (Work.Pert.liftF u σ α)^[j] z ∈ Work.Pert.Qm Ξ α) :
    ∑ j ∈ (Finset.range n).filter
            (fun j => 1 ≤ (α * (Work.Pert.liftF u σ α)^[j] z).im),
        ‖Work.Pert.liftF u σ α ((Work.Pert.liftF u σ α)^[j] z)
          - ((Work.Pert.liftF u σ α)^[j] z + 1)‖
      ≤ 2 ^ 28 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M) + Real.log (2 + ‖z‖)) := by
  classical
  set F : ℂ → ℂ := Work.Pert.liftF u σ α with hFdef
  have hFval : ∀ w : ℂ, F w = Work.Pert.liftF u σ α w := fun w => by rw [hFdef]
  -- ## 0. the numerical hypotheses
  have hα64 : ‖α‖ ≤ 1 / 64 := by
    have h1 : (64 : ℝ) ≤ 32 * (M + 2 + Ξ) := by
      have h2 : ((2 : ℝ) ^ 10) = 1024 := by norm_num
      nlinarith [hM, hΞ]
    have h2 : (0 : ℝ) < 32 * (M + 2 + Ξ) := by linarith
    calc ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ)) := hα
      _ ≤ 1 / 64 := one_div_le_one_div_of_le (by norm_num) h1
  -- the normalisation gives `‖σ‖ ≤ 32 ‖α‖`
  have hσb : ‖σ‖ ≤ 32 * ‖α‖ :=
    sigma_le_norm_alpha hα64 (hu2 0 (Metric.mem_ball_self hrr)).1 hnorm
  -- ## 1. the analytic input: defect vs `τ_f`, with an explicit constant
  have hpt : ∀ w ∈ Work.Pert.Qm Ξ α,
      ‖Work.Pert.liftF u σ α w - (w + 1)‖
        ≤ 2 ^ 12 * (1 + 1 / rr) * ‖Work.Pert.tauC σ α w‖ :=
    liftF_defect_le_tau_explicit hΞ hrr hInF1 hα64 hσ hnorm hu hu2 hτQ hNT
  -- ## 2. the walk is a `1/32`-near-translation walk in the gate
  have hgate : ∀ j ≤ n, F^[j] z ∈ Work.Pert.Qm Ξ α := by
    intro j hj
    rw [hFdef]
    exact hwalk j hj
  have hstep : ∀ j < n, ‖F^[(j + 1)] z - (F^[j] z + 1)‖ ≤ 1 / 32 := by
    intro j hj
    have hjQ : F^[j] z ∈ Work.Pert.Qm Ξ α := hgate j (le_of_lt hj)
    have h1 : F^[(j + 1)] z = F (F^[j] z) := Function.iterate_succ_apply' F j z
    rw [h1]
    have h2 : ‖Work.Pert.liftF u σ α (F^[j] z) - (F^[j] z + 1)‖ ≤ 1 / 32 := hNT _ hjQ
    rw [hFval]
    exact h2
  -- ## 3. the uniform weighted count of the high band
  have hcount : ‖α‖ * (∑ j ∈ Finset.range n,
        (if 1 ≤ (α * F^[j] z).im then Real.exp (-(2 * Real.pi * (α * F^[j] z).im)) else 0))
      ≤ 2 ^ 6 :=
    high_decay_sum_uniform hΞ hInF1 hα64 hstep hgate
  -- ## 4. the termwise bound
  have hterm : ∀ j ∈ Finset.range n,
      (if 1 ≤ (α * F^[j] z).im then ‖F (F^[j] z) - (F^[j] z + 1)‖ else 0)
        ≤ (if 1 ≤ (α * F^[j] z).im then
            2 ^ 18 * (1 + 1 / rr) * ‖α‖
              * Real.exp (-(2 * Real.pi * (α * F^[j] z).im)) else 0) := by
    intro j hj
    rw [Finset.mem_range] at hj
    by_cases hP : 1 ≤ (α * F^[j] z).im
    · rw [ite_eq_left hP, ite_eq_left hP]
      have hjQ : F^[j] z ∈ Work.Pert.Qm Ξ α := hgate j (le_of_lt hj)
      have h1 : ‖F (F^[j] z) - (F^[j] z + 1)‖
          ≤ 2 ^ 12 * (1 + 1 / rr) * ‖Work.Pert.tauC σ α (F^[j] z)‖ := by
        rw [hFval]
        exact hpt _ hjQ
      have h2 : ‖Work.Pert.tauC σ α (F^[j] z)‖
          ≤ 2 ^ 6 * ‖α‖ * Real.exp (-(2 * Real.pi * (α * F^[j] z).im)) :=
        tauC_decay_high hP hσb
      calc ‖F (F^[j] z) - (F^[j] z + 1)‖
          ≤ 2 ^ 12 * (1 + 1 / rr) * ‖Work.Pert.tauC σ α (F^[j] z)‖ := h1
        _ ≤ 2 ^ 12 * (1 + 1 / rr) * (2 ^ 6 * ‖α‖
              * Real.exp (-(2 * Real.pi * (α * F^[j] z).im))) :=
              mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = 2 ^ 18 * (1 + 1 / rr) * ‖α‖
              * Real.exp (-(2 * Real.pi * (α * F^[j] z).im)) := by ring
    · rw [ite_eq_right hP, ite_eq_right hP]
  -- ## 5. summation
  have hstep2 : (∑ j ∈ Finset.range n,
        (if 1 ≤ (α * F^[j] z).im then ‖F (F^[j] z) - (F^[j] z + 1)‖ else 0))
      ≤ 2 ^ 18 * (1 + 1 / rr) * (‖α‖ * (∑ j ∈ Finset.range n,
        (if 1 ≤ (α * F^[j] z).im then Real.exp (-(2 * Real.pi * (α * F^[j] z).im))
          else 0))) := by
    calc (∑ j ∈ Finset.range n,
        (if 1 ≤ (α * F^[j] z).im then ‖F (F^[j] z) - (F^[j] z + 1)‖ else 0))
        ≤ ∑ j ∈ Finset.range n,
            (if 1 ≤ (α * F^[j] z).im then
              2 ^ 18 * (1 + 1 / rr) * ‖α‖
                * Real.exp (-(2 * Real.pi * (α * F^[j] z).im)) else 0) :=
          Finset.sum_le_sum hterm
      _ = 2 ^ 18 * (1 + 1 / rr) * (‖α‖ * (∑ j ∈ Finset.range n,
            (if 1 ≤ (α * F^[j] z).im then Real.exp (-(2 * Real.pi * (α * F^[j] z).im))
              else 0))) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          by_cases hP : 1 ≤ (α * F^[j] z).im
          · rw [ite_eq_left hP, ite_eq_left hP]; ring
          · rw [ite_eq_right hP, ite_eq_right hP]; ring
  -- ## 6. filtered sum = `if`-sum
  have hLHS : (∑ j ∈ (Finset.range n).filter (fun j => 1 ≤ (α * F^[j] z).im),
        ‖F (F^[j] z) - (F^[j] z + 1)‖)
      = ∑ j ∈ Finset.range n,
        (if 1 ≤ (α * F^[j] z).im then ‖F (F^[j] z) - (F^[j] z + 1)‖ else 0) :=
    Finset.sum_filter _ _
  -- ## 7. the logarithmic factor is at least `7`
  have hlogM : 6 ≤ Real.log (2 + M) := by
    have h2M : (1026 : ℝ) ≤ 2 + M := by
      have h2 : ((2 : ℝ) ^ 10) = 1024 := by norm_num
      linarith [hM]
    have hexp6 : Real.exp 6 ≤ 1026 := by
      have h1 : Real.exp 6 = (Real.exp 1) ^ 6 := by
        rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      have h2 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
      have h3 : (Real.exp 1) ^ 6 ≤ (2.7182818286 : ℝ) ^ 6 :=
        pow_le_pow_left₀ (Real.exp_pos 1).le (le_of_lt h2) 6
      have h4 : (2.7182818286 : ℝ) ^ 6 ≤ 1026 := by norm_num
      rw [h1]
      exact le_trans h3 h4
    rw [Real.le_log_iff_exp_le (by linarith : (0 : ℝ) < 2 + M)]
    exact le_trans hexp6 h2M
  have hlogz : 0 ≤ Real.log (2 + ‖z‖) :=
    Real.log_nonneg (by have h := norm_nonneg z; linarith)
  have hK : 1 + 1 / rr ≤ 1 + Ξ + 1 / Ξ + 1 / rr := by
    have h1 : 0 < 1 / Ξ := one_div_pos.mpr hΞ
    linarith
  have hlog7 : (7 : ℝ) ≤ 1 + Real.log (2 + M) + Real.log (2 + ‖z‖) := by linarith
  rw [hLHS]
  calc (∑ j ∈ Finset.range n,
        (if 1 ≤ (α * F^[j] z).im then ‖F (F^[j] z) - (F^[j] z + 1)‖ else 0))
      ≤ 2 ^ 18 * (1 + 1 / rr) * (‖α‖ * (∑ j ∈ Finset.range n,
          (if 1 ≤ (α * F^[j] z).im then Real.exp (-(2 * Real.pi * (α * F^[j] z).im))
            else 0))) := hstep2
    _ ≤ 2 ^ 18 * (1 + 1 / rr) * 2 ^ 6 :=
        mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = 2 ^ 24 * (1 + 1 / rr) := by ring
    _ ≤ 2 ^ 28 * (1 + Ξ + 1 / Ξ + 1 / rr) := by
        have h1 : (2 : ℝ) ^ 24 ≤ 2 ^ 28 := by norm_num
        calc 2 ^ 24 * (1 + 1 / rr) ≤ 2 ^ 28 * (1 + 1 / rr) :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
          _ ≤ 2 ^ 28 * (1 + Ξ + 1 / Ξ + 1 / rr) :=
              mul_le_mul_of_nonneg_left hK (by norm_num)
    _ ≤ 2 ^ 28 * (1 + Ξ + 1 / Ξ + 1 / rr)
          * (1 + Real.log (2 + M) + Real.log (2 + ‖z‖)) := by
        have h1 : (1 : ℝ) ≤ 1 + Real.log (2 + M) + Real.log (2 + ‖z‖) := by linarith
        calc 2 ^ 28 * (1 + Ξ + 1 / Ξ + 1 / rr)
            = 2 ^ 28 * (1 + Ξ + 1 / Ξ + 1 / rr) * 1 := by ring
          _ ≤ 2 ^ 28 * (1 + Ξ + 1 / Ξ + 1 / rr)
                * (1 + Real.log (2 + M) + Real.log (2 + ‖z‖)) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)

end

end Work.Pert.GateDriftRate
