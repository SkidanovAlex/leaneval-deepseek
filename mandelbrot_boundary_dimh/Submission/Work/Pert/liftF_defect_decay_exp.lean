import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup
import Submission.Work.Pert.liftF_sub_translation_le_cont
import Submission.Work.Pert.tauC_upper_decay
import Submission.Work.Pert.diffAt_linear_bound

/-!
# PERT · `Work.Pert.liftF_defect_decay_exp`

Quantitative *exponential* decay of the near-translation defect of the lift `F_f = liftF u σ α` at
the **upper end** of the lower gate `Qm Ξ α` (Shishikura (A.1.7)(ii), (4.2)):

  `∃ M κ Y > 0, ∀ z ∈ Qm Ξ α, Y ≤ z.im → ‖liftF u σ α z - (z + 1)‖ ≤ M exp (-(κ z.im))`.

This is the exponential form of `Work.Pert.liftF_defect_decay_upper` (which states the weaker
`C₀ / ‖z‖` bound); the extra gain keeps the defect comparable with `‖τ_f z‖`, which decays at
exactly the same rate.

The argument is the standard three-step route, under the minimal analytic hypotheses on the germ
`u` (differentiable on `ball 0 rr`, `1/2 ≤ ‖u‖ ≤ 2` there):

* `Work.Pert.tauC_upper_decay` — `‖τ_f z‖ ≤ M exp (-(κ z.im))` on the gate, `κ > 0`;
* `Work.Pert.liftF_sub_translation_le_cont` —
  `‖liftF u σ α z - (z+1)‖ ≤ K (‖u (τ_f z) - u 0‖ + ‖τ_f z‖)` for `‖τ_f z‖` small
  (only `ContinuousAt u 0` is used);
* `Work.Pert.diffAt_linear_bound` — the linearisation of `u` at `0` turns `‖u (τ_f z) - u 0‖`
  into `O(‖τ_f z‖)`, so the defect is `O(exp (-(κ z.im)))`.

The hypothesis `hτQ` (the gate image under `τ_f` lies in `ball 0 rr`) is not needed here: `u 0 ≠ 0`
follows from `1/2 ≤ ‖u 0‖` and `hdiff` gives differentiability, hence continuity, of `u` at `0`.
-/

set_option linter.unusedVariables false

namespace Work.Pert

theorem liftF_defect_decay_exp {u : ℂ → ℂ} {σ α : ℂ} {Ξ rr : ℝ}
    (hΞ : 0 < Ξ) (hrr : 0 < rr) (hσ : σ ≠ 0) (hα0 : α ≠ 0) (hα64 : ‖α‖ ≤ 1 / 64)
    (hα : MandelDim.InF1 α)
    (hdiff : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr))
    (hu : ∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hτQ : ∀ z ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α z ∈ Metric.ball (0 : ℂ) rr) :
    ∃ M κ Y : ℝ, 0 < M ∧ 0 < κ ∧ ∀ z ∈ Work.Pert.Qm Ξ α, Y ≤ z.im →
      ‖Work.Pert.liftF u σ α z - (z + 1)‖ ≤ M * Real.exp (-(κ * z.im)) := by
  have h0mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) rr := by
    rw [Metric.mem_ball, dist_eq_norm]; simpa using hrr
  have hu0 : u 0 ≠ 0 := by
    have h := (hu 0 h0mem).1
    intro hz
    rw [hz, norm_zero] at h
    norm_num at h
  have hd0 : DifferentiableAt ℂ u 0 :=
    hdiff.differentiableAt (Metric.isOpen_ball.mem_nhds h0mem)
  have hcont : ContinuousAt u 0 := hd0.continuousAt
  obtain ⟨ε, K, hε, hK, hbnd⟩ :=
    Work.Pert.liftF_sub_translation_le_cont (u := u) (σ := σ) (α := α) hcont hu0 hnorm hα0 hα64
  obtain ⟨M, κ, Y₀, hM, hκ, hdec⟩ := Work.Pert.tauC_upper_decay (σ := σ) (α := α) hΞ hα hσ
  obtain ⟨C, ρ, hC, hρ, hloc⟩ := Work.Pert.diffAt_linear_bound hd0
  set s : ℝ := min ε (min ρ 1) with hsdef
  have hs : 0 < s := lt_min hε (lt_min hρ one_pos)
  have hsε : s ≤ ε := min_le_left _ _
  have hsρ : s ≤ ρ := le_trans (min_le_right _ _) (min_le_left _ _)
  refine ⟨K * (C + 1) * M, κ,
    max (max Y₀ 0 + 1) (Real.log (M / s) / κ + 1), by positivity, hκ, ?_⟩
  intro z hz hy
  have hY : max Y₀ 0 + 1 ≤ z.im := le_trans (le_max_left _ _) hy
  have hY₀ : Y₀ < z.im := by
    have := le_max_left Y₀ (0 : ℝ); linarith
  have hypos : 0 < z.im := by
    have := le_max_right Y₀ (0 : ℝ); linarith
  -- `M exp (-(κ z.im)) < s ≤ min ε ρ`: the threshold that makes both the local estimate `hbnd`
  -- and the linearisation `hloc` of `u` at `0` available at `τ_f z`
  have hlog : Real.log (M / s) < κ * z.im := by
    have h1 : Real.log (M / s) / κ + 1 ≤ z.im := le_trans (le_max_right _ _) hy
    have h2 : Real.log (M / s) + κ ≤ κ * z.im := by
      have h3 := mul_le_mul_of_nonneg_left h1 (le_of_lt hκ)
      have h4 : κ * (Real.log (M / s) / κ + 1) = Real.log (M / s) + κ := by
        rw [mul_add, mul_one]
        congr 1
        rw [mul_comm]; exact div_mul_cancel₀ _ (ne_of_gt hκ)
      linarith [h3, h4.symm.le, h4.le]
    linarith
  have hMs : 0 < M / s := div_pos hM hs
  have hexp_lt : M * Real.exp (-(κ * z.im)) < s := by
    have h2 : M / s < Real.exp (κ * z.im) := (Real.log_lt_iff_lt_exp hMs).mp hlog
    have h3 : M < s * Real.exp (κ * z.im) := by
      have := (div_lt_iff₀ hs).mp h2
      linarith [this]
    have h4 := mul_lt_mul_of_pos_right h3 (Real.exp_pos (-(κ * z.im)))
    have h5 : s * Real.exp (κ * z.im) * Real.exp (-(κ * z.im)) = s := by
      rw [Real.exp_neg, mul_assoc, mul_inv_cancel₀ (ne_of_gt (Real.exp_pos _)), mul_one]
    linarith [h4, h5.le, h5.ge]
  set τ : ℂ := Work.Pert.tauC σ α z with hτ
  have hτs : ‖τ‖ < s := by
    rw [hτ]
    exact lt_of_le_of_lt (hdec z hz hY₀) hexp_lt
  have hτρ : ‖τ‖ ≤ ρ := le_of_lt (lt_of_lt_of_le hτs hsρ)
  have hτε : ‖τ‖ ≤ ε := le_of_lt (lt_of_lt_of_le hτs hsε)
  have hb := hbnd z (by rw [← hτ]; exact hτε)
  rw [← hτ] at hb
  have hl : ‖u τ - u 0‖ ≤ C * ‖τ‖ := by
    have h := hloc τ (by simpa using hτρ)
    simpa using h
  calc ‖Work.Pert.liftF u σ α z - (z + 1)‖
      ≤ K * (‖u τ - u 0‖ + ‖τ‖) := hb
    _ ≤ K * (C * ‖τ‖ + ‖τ‖) := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hK)
          linarith [hl]
    _ = K * (C + 1) * ‖τ‖ := by ring
    _ ≤ K * (C + 1) * (M * Real.exp (-(κ * z.im))) := by
          apply mul_le_mul_of_nonneg_left (hdec z hz hY₀)
          positivity
    _ = K * (C + 1) * M * Real.exp (-(κ * z.im)) := by ring

end Work.Pert
