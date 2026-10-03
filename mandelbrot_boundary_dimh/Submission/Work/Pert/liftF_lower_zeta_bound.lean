import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup
import Submission.Work.Analysis.ZetaLocal.zeta_local_bound
import Submission.Work.Analysis.ZetaLocal.zeta_sigma_prelim

/-!
# PERT · `Work.Pert.liftF_lower_zeta_bound`

The **lower end of the lower gate**: the perturbed coordinate `τ_f` takes the value `σ` (the
second fixed point of `f z = z + z (z - σ) u z`) at `w = ∞`, and `sfun u σ α z → σ u σ/(1 + σ u σ)`
there, so that `1 - sfun → 1/(1 + σ u σ) = 1/f'(σ)`.  This module produces the two facts the
assembly of `PertData` needs about that limit:

* `f'(σ) = 1 + σ u σ` is nonzero and lies in the right half plane (so that its principal logarithm
  is defined and `ρ = -log (f'(σ))/(2πiα) ≈ 1`, cf. `Work.Pert.liftF_lower_rho_close`);
* on the neighbourhood `‖τ_f z - σ‖ ≤ ε` of the fibre `τ_f = σ` one has
  `Re (1 - sfun) > 0`, `1 - sfun ≠ 0` and `‖(1 - sfun)(1 + σ u σ) - 1‖ ≤ K ‖τ_f z - σ‖`, i.e.
  `1 - sfun` is `1/(1 + σuσ)` to first order: the local form in which the perturbed Fatou
  coordinate is compared with the unperturbed one near `σ`.

The two estimates are delegated:

* `Work.Analysis.ZetaLocal.zeta_sigma_prelim` — the numerical handles on `σ` obtained from the
  normalisation `1 - σ u 0 = exp (2πiα)`, the boundedness `1/2 ≤ ‖u‖ ≤ 2` and the Lipschitz
  hypothesis, with `hsmall : (2π + 32C)‖α‖ ≤ 1/128` as the only smallness input;
* `Work.Analysis.ZetaLocal.zeta_local_bound` — the purely local estimate, using
  `1 - σ u τ/(1 + τ u τ) = (1 + (τ - σ) u τ)/(1 + τ u τ)` and
  `(1 - σuτ/(1+τuτ))(1 + σuσ) - 1 = σ((uσ - uτ) + uσ uτ (τ - σ))/(1 + τuτ)`.

This file contains the assembly: `ε = min (r - ‖σ‖) (1/64)` and `K = C + 5`.

Note (name resolution only, statement unchanged): the imaginary unit is written as the bare `I`,
which is `Complex.I`; `open Complex` below is what makes it resolve under `autoImplicit = false`
(as used by `lake build`), exactly as in `Work.Pert.liftF_sub_translation_le`.
-/

open Complex

namespace Work.Pert

theorem liftF_lower_zeta_bound {u : ℂ → ℂ} {σ α : ℂ} {r C : ℝ}
    (hr : 0 < r) (hC : 0 ≤ C)
    (hu2 : ∀ z ∈ Metric.ball 0 r, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (huL : ∀ z ∈ Metric.ball 0 r, ∀ w ∈ Metric.ball 0 r, ‖u z - u w‖ ≤ C * ‖z - w‖)
    (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * I * α))
    (hσr : ‖σ‖ < r) (hαne : α ≠ 0)
    (hsmall : (2 * Real.pi + 32 * C) * ‖α‖ ≤ 1 / 128) :
    0 < (1 + σ * u σ).re ∧ 1 + σ * u σ ≠ 0 ∧
    ∃ ε K : ℝ, 0 < ε ∧ 0 < K ∧ ε ≤ r - ‖σ‖ ∧
      ∀ z : ℂ, ‖Work.Pert.tauC σ α z - σ‖ ≤ ε →
        0 < (1 - Work.Pert.sfun u σ α z).re ∧
        (1 - Work.Pert.sfun u σ α z) ≠ 0 ∧
        ‖(1 - Work.Pert.sfun u σ α z) * (1 + σ * u σ) - 1‖
          ≤ K * ‖Work.Pert.tauC σ α z - σ‖ := by
  obtain ⟨hσ32, hCσ, hDre, hDnorm, hDim, _⟩ :=
    Work.Analysis.ZetaLocal.zeta_sigma_prelim (u := u) (σ := σ) (α := α) (r := r) (C := C)
      hr hC hu2 huL hnorm hσr hαne hsmall
  have hDre0 : 0 < (1 + σ * u σ).re := lt_of_lt_of_le (by norm_num) hDre
  have hDne : 1 + σ * u σ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hDnorm
    norm_num at hDnorm
  refine ⟨hDre0, hDne, ?_⟩
  refine ⟨min ((r - ‖σ‖) / 2) (1 / 64), C + 5, ?_, ?_, ?_, ?_⟩
  · exact lt_min (by linarith) (by norm_num)
  · linarith
  · -- `min ((r - ‖σ‖)/2) (1/64) ≤ r - ‖σ‖` because `‖σ‖ < r`
    linarith [hσr, min_le_left ((r - ‖σ‖) / 2) (1 / 64)]
  · intro z hz
    set τ : ℂ := Work.Pert.tauC σ α z with hτdef
    have hτε : ‖τ - σ‖ ≤ min ((r - ‖σ‖) / 2) (1 / 64) := by rw [hτdef]; exact hz
    have hτεhalf : ‖τ - σ‖ ≤ (r - ‖σ‖) / 2 := le_trans hτε (min_le_left _ _)
    have hτε64 : ‖τ - σ‖ ≤ 1 / 64 := le_trans hτε (min_le_right _ _)
    have hτmem : τ ∈ Metric.ball 0 r := by
      rw [Metric.mem_ball, dist_zero_right]
      have h2 : ‖τ‖ ≤ ‖σ‖ + ‖τ - σ‖ := by
        have h3 : σ + (τ - σ) = τ := by ring
        have h4 := norm_add_le σ (τ - σ : ℂ)
        rw [h3] at h4
        exact h4
      linarith
    have hσmem : σ ∈ Metric.ball 0 r := by
      rw [Metric.mem_ball, dist_zero_right]; exact hσr
    have huσ2 : ‖u σ‖ ≤ 2 := (hu2 σ hσmem).2
    have huτ2 : ‖u τ‖ ≤ 2 := (hu2 τ hτmem).2
    have hLip : ‖u σ - u τ‖ ≤ C * ‖σ - τ‖ := huL σ hσmem τ hτmem
    have hloc := Work.Analysis.ZetaLocal.zeta_local_bound (u := u) (σ := σ) (τ := τ) (C := C)
      hC huσ2 huτ2 hLip hτε64 hCσ hσ32 hDnorm hDre hDim
    have hsfun : Work.Pert.sfun u σ α z = σ * u τ / (1 + τ * u τ) := by
      rw [Work.Pert.sfun, hτdef]
    rw [hsfun]
    exact hloc

end Work.Pert
