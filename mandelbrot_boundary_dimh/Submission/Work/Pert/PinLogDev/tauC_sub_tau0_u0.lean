import Mathlib
import Submission.Work.Pert.PinLogDev.PinAux2
import Submission.Work.Pert.PinLogDev.tauC_sub_tau0_alpha

namespace Work.Pert.PinLogDev

open Complex

noncomputable section

/-!
# `Work.Pert.PinLogDev.tauC_sub_tau0_u0`

The chart comparison `τ_f` vs `τ₀ = -1/w` in the *normalised* form actually produced by the
parabolic perturbation: the perturbation datum enters through `u0 = u 0` only, via
`σ * u0 = 1 - exp (2πiα)` (equivalently `1 - σ u0 = exp (2πiα)`) and `‖u0 - 1‖ ≤ 1/2`.

Write `σ₁ = 1 - exp (2πiα)`.  Then `σ = σ₁ / u0`, so

  `τ_σ(w) - τ_σ₁(w) = (1/u0 - 1) · τ_σ₁(w)`,

and `‖1/u0 - 1‖ ≤ 2‖u0 - 1‖` because `‖u0 - 1‖ ≤ 1/2` gives `‖u0‖ ≥ 1/2`.  The uniform
comparison `tauC_sub_tau0_alpha` at `c = 1/2` (relative lattice regime
`(1/2)‖αw‖ ≤ dist(αw, ℤ)`) gives `‖τ_σ₁(w) - τ₀(w)‖ ≤ C₁‖α‖`, whence
`‖τ_σ₁(w)‖ ≤ C₁‖α‖ + 1/‖w‖`.  Combining,

`‖τ_σ(w) - τ₀(w)‖ ≤ 2‖u0-1‖(C₁‖α‖ + 1/‖w‖) + C₁‖α‖ ≤ (2C₁+2)(‖α‖ + ‖u0-1‖/‖w‖)`,

using `2‖u0-1‖ ≤ 1` to absorb the cross term `2C₁‖u0-1‖‖α‖` into `C₁‖α‖`.
-/

theorem tauC_sub_tau0_u0 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {σ α u0 w : ℂ},
      σ * u0 = 1 - Complex.exp (2 * Real.pi * Complex.I * α) → α ≠ 0 →
      1 ≤ ‖w‖ → ‖α‖ * ‖w‖ ≤ 2 → ‖u0 - 1‖ ≤ 1 / 2 →
      (1 / 2) * (‖α‖ * ‖w‖) ≤ (⨅ k : ℤ, dist (α * w) (k : ℂ)) →
      ‖Work.Pert.tauC σ α w - MandelDim.tau0 w‖ ≤ C * (‖α‖ + ‖u0 - 1‖ / ‖w‖) := by
  obtain ⟨C₁, hC₁, h₁⟩ := tauC_sub_tau0_alpha (c := 1 / 2) (by norm_num) (by norm_num)
  refine ⟨2 * C₁ + 2, by linarith, ?_⟩
  intro σ α u0 w hσ hα hw hαw hu0 hlat
  set σ₁ : ℂ := 1 - Complex.exp (2 * Real.pi * Complex.I * α) with hσ₁def
  -- ## `u0` is bounded away from `0`
  have hu0n : (1 : ℝ) / 2 ≤ ‖u0‖ := by
    have h := abs_norm_sub_norm_le u0 (1 : ℂ)
    rw [norm_one] at h
    have h2 : -(‖u0 - 1‖) ≤ ‖u0‖ - 1 := (abs_le.mp h).1
    linarith
  have hu0pos : 0 < ‖u0‖ := by linarith
  have hu0ne : u0 ≠ 0 := norm_pos_iff.mp hu0pos
  -- ## `σ = σ₁ / u0`, hence `τ_σ = (1/u0) · τ_σ₁`
  have hσ₁' : σ₁ = σ * u0 := hσ.symm
  have hτ₁ : Work.Pert.tauC σ₁ α w = u0 * Work.Pert.tauC σ α w := by
    rw [hσ₁']
    exact tauC_mul_u0 (fun _ => u0) σ α w
  have hτ : Work.Pert.tauC σ α w = (1 / u0) * Work.Pert.tauC σ₁ α w := by
    rw [hτ₁, one_div, ← mul_assoc, inv_mul_cancel₀ hu0ne, one_mul]
  have hkey : Work.Pert.tauC σ α w - Work.Pert.tauC σ₁ α w
      = (1 / u0 - 1) * Work.Pert.tauC σ₁ α w := by
    rw [hτ]; ring
  -- ## `‖1/u0 - 1‖ ≤ 2‖u0 - 1‖`
  have hδ : ‖1 / u0 - 1‖ ≤ 2 * ‖u0 - 1‖ := by
    have he : 1 / u0 - 1 = (1 - u0) / u0 := by rw [div_sub_one hu0ne]
    rw [he, norm_div,
      show ‖(1 : ℂ) - u0‖ = ‖u0 - 1‖ from by
        rw [show (1 : ℂ) - u0 = -(u0 - 1) by ring, norm_neg]]
    calc ‖u0 - 1‖ / ‖u0‖ ≤ ‖u0 - 1‖ / (1 / 2) :=
          div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) hu0n
      _ = 2 * ‖u0 - 1‖ := by ring
  have hb2 : ‖Work.Pert.tauC σ α w - Work.Pert.tauC σ₁ α w‖
      ≤ 2 * ‖u0 - 1‖ * ‖Work.Pert.tauC σ₁ α w‖ := by
    rw [hkey, norm_mul]
    exact mul_le_mul_of_nonneg_right hδ (norm_nonneg _)
  -- ## the uniform comparison of `τ_σ₁` with `τ₀`
  have hb1 : ‖Work.Pert.tauC σ₁ α w - MandelDim.tau0 w‖ ≤ C₁ * ‖α‖ :=
    h₁ (σ := σ₁) (α := α) (w := w) rfl hα (by linarith) hαw hlat
  have hτ0 : ‖MandelDim.tau0 w‖ = 1 / ‖w‖ := by
    rw [MandelDim.tau0, norm_div, norm_neg, norm_one]
  have hb1' : ‖Work.Pert.tauC σ₁ α w‖ ≤ C₁ * ‖α‖ + 1 / ‖w‖ := by
    calc ‖Work.Pert.tauC σ₁ α w‖
        = ‖(Work.Pert.tauC σ₁ α w - MandelDim.tau0 w) + MandelDim.tau0 w‖ := by
          rw [sub_add_cancel]
      _ ≤ ‖Work.Pert.tauC σ₁ α w - MandelDim.tau0 w‖ + ‖MandelDim.tau0 w‖ := norm_add_le _ _
      _ ≤ C₁ * ‖α‖ + 1 / ‖w‖ := by rw [hτ0]; linarith
  -- ## assembly
  have hfin : 2 * ‖u0 - 1‖ * ‖Work.Pert.tauC σ₁ α w‖ + C₁ * ‖α‖
      ≤ (2 * C₁ + 2) * (‖α‖ + ‖u0 - 1‖ / ‖w‖) := by
    have hstep : 2 * ‖u0 - 1‖ * ‖Work.Pert.tauC σ₁ α w‖
        ≤ 2 * ‖u0 - 1‖ * (C₁ * ‖α‖ + 1 / ‖w‖) :=
      mul_le_mul_of_nonneg_left hb1' (by positivity)
    have h2u : 2 * ‖u0 - 1‖ ≤ 1 := by linarith
    have hCA : 0 ≤ C₁ * ‖α‖ := mul_nonneg hC₁ (norm_nonneg α)
    have hsmall : 2 * ‖u0 - 1‖ * (C₁ * ‖α‖) ≤ C₁ * ‖α‖ := by
      simpa using mul_le_mul_of_nonneg_right h2u hCA
    have hsplit : 2 * ‖u0 - 1‖ * (C₁ * ‖α‖ + 1 / ‖w‖)
        = 2 * ‖u0 - 1‖ * (C₁ * ‖α‖) + 2 * ‖u0 - 1‖ * (1 / ‖w‖) := by ring
    have hdiv : 2 * ‖u0 - 1‖ * (1 / ‖w‖) = 2 * (‖u0 - 1‖ / ‖w‖) := by ring
    rw [hsplit, hdiv] at hstep
    have hα0 : 0 ≤ ‖α‖ := norm_nonneg α
    have hq0 : 0 ≤ ‖u0 - 1‖ / ‖w‖ := div_nonneg (norm_nonneg _) (norm_nonneg _)
    nlinarith [hstep, hsmall, hα0, hq0, hC₁]
  calc ‖Work.Pert.tauC σ α w - MandelDim.tau0 w‖
      = ‖(Work.Pert.tauC σ α w - Work.Pert.tauC σ₁ α w)
          + (Work.Pert.tauC σ₁ α w - MandelDim.tau0 w)‖ := by
        rw [show (Work.Pert.tauC σ α w - Work.Pert.tauC σ₁ α w)
              + (Work.Pert.tauC σ₁ α w - MandelDim.tau0 w)
            = Work.Pert.tauC σ α w - MandelDim.tau0 w from by ring]
    _ ≤ ‖Work.Pert.tauC σ α w - Work.Pert.tauC σ₁ α w‖
          + ‖Work.Pert.tauC σ₁ α w - MandelDim.tau0 w‖ := norm_add_le _ _
    _ ≤ 2 * ‖u0 - 1‖ * ‖Work.Pert.tauC σ₁ α w‖ + C₁ * ‖α‖ := add_le_add hb2 hb1
    _ ≤ (2 * C₁ + 2) * (‖α‖ + ‖u0 - 1‖ / ‖w‖) := hfin

end

end Work.Pert.PinLogDev
