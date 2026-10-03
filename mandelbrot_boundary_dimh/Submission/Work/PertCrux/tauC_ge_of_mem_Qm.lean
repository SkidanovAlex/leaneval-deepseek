import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.closedBall_subset_Qm
import Submission.Work.Pert.tools

/-!
# PERT · `Work.PertCrux.tauC_ge_of_mem_Qm`

The lower gate `Qm Ξ α` contains a point at which the perturbed coordinate `τ_f` is *large*,
namely `≥ 1/(16Ξ)`.

`τ_f w = σ / (1 - exp (-2πi α w))`, so `‖τ_f w‖` is large exactly when `exp (-2πi α w)` is close
to `1`, i.e. when `α w` is close to an integer.  The hypotheses pin the multiplier `σ` through
the normal-form relation `1 - σ u₀ = exp (2πi α)` and the bound `1/2 ≤ ‖u₀‖ ≤ 2`:

* `‖2πi α‖ ≤ 1/2` gives `‖exp (2πi α) - 1‖ ≥ π‖α‖` (order-two Taylor), hence
  `‖σ‖ ≥ π‖α‖/2`;
* the scale separation `8πΞ‖α‖ ≤ 1/2` keeps `‖4πΞα‖ ≤ 1/4`, so `‖exp (4πΞα) - 1‖ ≤ 8πΞ‖α‖`.

The explicit witness is `z = 2Ξ i`: then `-2πi α z = 4πΞ α`, so

  `1/(16Ξ) · ‖1 - exp (4πΞα)‖ ≤ 1/(16Ξ) · 8πΞ‖α‖ = π‖α‖/2 ≤ ‖σ‖ = ‖τ_f z‖ · ‖1 - exp (4πΞα)‖`,

which is the claim (the denominator is non-zero because `α ≠ 0`).  Membership `z ∈ Qm Ξ α` needs
only `Ξ > 0` and `Ξ < Re (1/α)` (`Work.Pert.mem_Qm_iff`): the first gate inequality is
`Re (1/α) - Ξ + |2Ξ + Im (1/α)| > 0`, the second `|2Ξ| - Ξ = Ξ > 0`.
-/

namespace Work.PertCrux

open MandelDim Complex

noncomputable section

theorem tauC_ge_of_mem_Qm {σ α u₀ : ℂ} {Ξ : ℝ} (hΞ : 0 < Ξ) (hα : α ≠ 0)
    (h1 : 2 * Real.pi * ‖α‖ ≤ 1 / 2) (h2 : 8 * Real.pi * ‖α‖ * Ξ ≤ 1 / 2)
    (hRe : Ξ < (1 / α).re) (hu₀lo : 1 / 2 ≤ ‖u₀‖) (hu₀hi : ‖u₀‖ ≤ 2)
    (hnorm : 1 - σ * u₀ = Complex.exp (2 * Real.pi * Complex.I * α)) :
    ∃ z ∈ Work.Pert.Qm Ξ α, 1 / (16 * Ξ) ≤ ‖Work.Pert.tauC σ α z‖ := by
  refine ⟨((2 * Ξ : ℝ) : ℂ) * Complex.I, ?_, ?_⟩
  · -- membership in the lower gate
    rw [Work.Pert.mem_Qm_iff]
    constructor
    · have him : (0 : ℝ) ≤ |(((2 * Ξ : ℝ) : ℂ) * Complex.I).im + (1 / α).im| := abs_nonneg _
      have hre : (((2 * Ξ : ℝ) : ℂ) * Complex.I).re = 0 := by simp
      rw [hre]
      linarith [hRe, him]
    · have hre : (((2 * Ξ : ℝ) : ℂ) * Complex.I).re = 0 := by simp
      have him : |(((2 * Ξ : ℝ) : ℂ) * Complex.I).im| = 2 * Ξ := by
        rw [show (((2 * Ξ : ℝ) : ℂ) * Complex.I).im = 2 * Ξ from by simp]
        exact abs_of_pos (by linarith)
      rw [hre, him]
      linarith
  · -- `‖τ_f‖ ≥ 1/(16Ξ)` at `z = 2Ξi`
    -- the order-two Taylor bounds `‖exp x - 1‖ ≥ ‖x‖/2` (lower) and
    -- `‖exp x - 1‖ ≤ 2‖x‖` (upper, `Complex.norm_exp_sub_one_le`) for `‖x‖ ≤ 1/2`
    have hlow : ∀ x : ℂ, ‖x‖ ≤ 1 / 2 → ‖x‖ / 2 ≤ ‖Complex.exp x - 1‖ := by
      intro x hx
      have hx1 : ‖x‖ ≤ 1 := by linarith
      have h1' : ‖Complex.exp x - 1 - x‖ ≤ ‖x‖ ^ 2 := Complex.norm_exp_sub_one_sub_id_le hx1
      have h3 : (Complex.exp x - 1) - (Complex.exp x - 1 - x) = x := by ring
      have hle := norm_sub_le (Complex.exp x - 1) (Complex.exp x - 1 - x)
      rw [h3] at hle
      nlinarith [hle, h1', norm_nonneg x, hx, sq_nonneg ‖x‖]
    -- the argument of the exponential at the witness
    have harg : -(2 * Real.pi * Complex.I * α * (((2 * Ξ : ℝ) : ℂ) * Complex.I))
        = 4 * Real.pi * Ξ * α := by
      calc -(2 * Real.pi * Complex.I * α * (((2 * Ξ : ℝ) : ℂ) * Complex.I))
          = -(2 * Real.pi * (((2 * Ξ : ℝ) : ℂ)) * α * (Complex.I * Complex.I)) := by ring
        _ = -(2 * Real.pi * (((2 * Ξ : ℝ) : ℂ)) * α * (-1)) := by rw [Complex.I_mul_I]
        _ = 4 * Real.pi * Ξ * α := by push_cast; ring
    have hz : Work.Pert.tauC σ α (((2 * Ξ : ℝ) : ℂ) * Complex.I)
        = σ / (1 - Complex.exp (4 * Real.pi * Ξ * α)) := by
      simp only [Work.Pert.tauC]
      rw [harg]
    rw [hz, norm_div]
    -- norm of the relevant exponent
    have hwnorm : ‖(4 * Real.pi * Ξ * α : ℂ)‖ = 4 * Real.pi * Ξ * ‖α‖ := by
      rw [norm_mul, norm_mul, norm_mul]
      simp [abs_of_pos Real.pi_pos, abs_of_pos hΞ]
    -- the denominator is non-zero (used to invert the division)
    have hden_pos : 0 < ‖1 - Complex.exp (4 * Real.pi * Ξ * α)‖ := by
      have hwle : ‖(4 * Real.pi * Ξ * α : ℂ)‖ ≤ 1 / 2 := by rw [hwnorm]; linarith
      have h := hlow _ hwle
      have hwpos : 0 < ‖(4 * Real.pi * Ξ * α : ℂ)‖ := by rw [hwnorm]; positivity
      rw [norm_sub_rev]
      linarith
    -- the lower bound on the multiplier `σ`
    have hσu : σ * u₀ = 1 - Complex.exp (2 * Real.pi * Complex.I * α) := by
      linear_combination -hnorm
    have hu0pos : 0 < ‖u₀‖ := by linarith
    have h2pinorm : ‖(2 * Real.pi * Complex.I * α : ℂ)‖ = 2 * Real.pi * ‖α‖ := by
      rw [norm_mul, norm_mul, norm_mul]
      simp [abs_of_pos Real.pi_pos]
    have hσ_lb : Real.pi * ‖α‖ / 2 ≤ ‖σ‖ := by
      have hlow2 : ‖(2 * Real.pi * Complex.I * α : ℂ)‖ / 2
          ≤ ‖Complex.exp (2 * Real.pi * Complex.I * α) - 1‖ := by
        apply hlow; rw [h2pinorm]; exact h1
      have hnormσu : ‖σ‖ * ‖u₀‖ = ‖1 - Complex.exp (2 * Real.pi * Complex.I * α)‖ := by
        rw [← norm_mul, hσu]
      have key : Real.pi * ‖α‖ ≤ ‖σ‖ * ‖u₀‖ := by
        rw [hnormσu, norm_sub_rev]
        have : Real.pi * ‖α‖ = ‖(2 * Real.pi * Complex.I * α : ℂ)‖ / 2 := by
          rw [h2pinorm]; ring
        linarith [hlow2]
      have key2 : Real.pi * ‖α‖ / ‖u₀‖ ≤ ‖σ‖ := by
        rw [div_le_iff₀ hu0pos]
        linarith [key]
      have key3 : Real.pi * ‖α‖ / 2 ≤ Real.pi * ‖α‖ / ‖u₀‖ :=
        div_le_div_of_nonneg_left (by positivity) hu0pos hu₀hi
      linarith
    rw [le_div_iff₀ hden_pos]
    -- upper bound on the denominator
    have hden_ub : ‖1 - Complex.exp (4 * Real.pi * Ξ * α)‖ ≤ 8 * Real.pi * Ξ * ‖α‖ := by
      have hwle1 : ‖(4 * Real.pi * Ξ * α : ℂ)‖ ≤ 1 := by rw [hwnorm]; linarith
      have h := Complex.norm_exp_sub_one_le (x := (4 * Real.pi * Ξ * α : ℂ)) hwle1
      rw [norm_sub_rev]
      calc ‖Complex.exp (4 * Real.pi * Ξ * α) - 1‖ ≤ 2 * ‖(4 * Real.pi * Ξ * α : ℂ)‖ := h
        _ = 8 * Real.pi * Ξ * ‖α‖ := by rw [hwnorm]; ring
    calc 1 / (16 * Ξ) * ‖1 - Complex.exp (4 * Real.pi * Ξ * α)‖
        ≤ 1 / (16 * Ξ) * (8 * Real.pi * Ξ * ‖α‖) := by
          apply mul_le_mul_of_nonneg_left hden_ub; positivity
      _ = Real.pi * ‖α‖ / 2 := by field_simp; ring
      _ ≤ ‖σ‖ := hσ_lb

end

end Work.PertCrux
