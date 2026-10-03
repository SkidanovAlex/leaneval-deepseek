import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Basic
import Submission.Work.Pert.liftF_defect_le_tauC
import Submission.Work.Pert.tauC_upper_decay

/-!
# PERT · `Work.Pert.liftF_inv_defect_le_exp`

At the **upper end of the lower gate** `Qm Ξ α` the lift `F_f = liftF u σ α` of the perturbed
Fatou coordinate is a near-translation with an *exponentially small* defect
(`Work.Pert.tauC_upper_decay` for `‖τ_f z‖` together with `Work.Pert.liftF_defect_le_tauC`),
and consequently the reciprocal defect of `F_f(z) - z` is exponentially small as well:

    ‖(F_f z - z)⁻¹ - 1‖ ≤ C · exp (-(κ · z.im)) .

Indeed with `d z := F_f z - (z + 1)` we have `F_f z - z = 1 + d z`, so

    (1 + d)⁻¹ - 1 = -d / (1 + d),

and the near-translation hypothesis `‖d‖ ≤ 1/32` gives the *uniform* lower bound `‖1 + d‖ ≥ 31/32`,
i.e. `‖(1+d)⁻¹ - 1‖ ≤ (32/31) ‖d‖`.  Combined with `‖d z‖ ≤ C₀ ‖τ_f z‖ ≤ C₀ M exp (-(κ z.im))`
this yields the claim with `C = (32/31) C₀ M`.

The hypotheses `hΞ`, `hrr`, `hσ`, `hnorm`, `hu`, `hu2`, `hτQ` are exactly those consumed by the two
estimates above; `hInF1` and `hα64` supply the geometry (`α ≠ 0`, `|α.im| < α.re`).
-/

namespace Work.Pert

open Complex

theorem liftF_inv_defect_le_exp {Ξ rr : ℝ} {α σ : ℂ} {u : ℂ → ℂ}
    (hΞ : 0 < Ξ) (hrr : 0 < rr) (hInF1 : MandelDim.InF1 α) (hα64 : ‖α‖ ≤ 1 / 64)
    (hσ : σ ≠ 0) (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr))
    (hu2 : ∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (hτQ : ∀ z ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α z ∈ Metric.ball (0 : ℂ) rr)
    (hNT : ∀ z ∈ Work.Pert.Qm Ξ α, ‖Work.Pert.liftF u σ α z - (z + 1)‖ ≤ 1 / 32) :
    ∃ C κ Y : ℝ, 0 < C ∧ 0 < κ ∧ ∀ z ∈ Work.Pert.Qm Ξ α, Y < z.im →
      ‖(Work.Pert.liftF u σ α z - z)⁻¹ - 1‖ ≤ C * Real.exp (-(κ * z.im)) := by
  -- `InF1 α` gives `α.re > |α.im| ≥ 0`, hence `α ≠ 0`
  have hαne : α ≠ 0 := by
    intro h0
    subst h0
    simp only [MandelDim.InF1, Complex.zero_re, Complex.zero_im, abs_zero] at hInF1
    exact absurd hInF1 (lt_irrefl 0)
  -- the defect is bounded by `τ_f`
  obtain ⟨C₀, hC₀pos, hC₀⟩ :=
    liftF_defect_le_tauC (u := u) (σ := σ) (α := α) (Ξ := Ξ) (Rm := rr)
      hΞ hαne hσ hrr hInF1 hα64 hnorm hu hu2 hτQ hNT
  -- and `τ_f` decays exponentially at the upper end of the gate
  obtain ⟨M, κ, Y, hMpos, hκpos, hdec⟩ :=
    tauC_upper_decay (σ := σ) (α := α) (ξ := Ξ) hΞ hInF1 hσ
  refine ⟨(32 / 31) * (C₀ * M), κ, Y, by positivity, hκpos, ?_⟩
  intro z hz hY
  set d := Work.Pert.liftF u σ α z - (z + 1) with hd
  -- the defect is uniformly small, whence `1 + d` is uniformly bounded below
  have hd32 : ‖d‖ ≤ 1 / 32 := hNT z hz
  have hden : (31 / 32 : ℝ) ≤ ‖1 + d‖ := by
    have h : ‖(1 + d) - d‖ ≤ ‖1 + d‖ + ‖d‖ := norm_sub_le _ _
    rw [add_sub_cancel_right] at h
    simp only [norm_one] at h
    linarith
  have hne : 1 + d ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hden
    norm_num at hden
  have hdeq : Work.Pert.liftF u σ α z - z = 1 + d := by rw [hd]; ring
  -- the reciprocal defect is `-d / (1 + d)`
  have hmain : (Work.Pert.liftF u σ α z - z)⁻¹ - 1 = -d / (1 + d) := by
    rw [hdeq]
    field_simp
    ring
  have hbound : ‖d‖ / ‖1 + d‖ ≤ (32 / 31) * ‖d‖ := by
    rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 31 / 32) hden)]
    have h1 : (1 : ℝ) ≤ (32 / 31) * ‖1 + d‖ := by
      have hh := mul_le_mul_of_nonneg_left hden (by norm_num : (0 : ℝ) ≤ 32 / 31)
      have he : (32 / 31) * (31 / 32) = (1 : ℝ) := by norm_num
      linarith
    calc ‖d‖ = ‖d‖ * 1 := (mul_one _).symm
      _ ≤ ‖d‖ * ((32 / 31) * ‖1 + d‖) := mul_le_mul_of_nonneg_left h1 (norm_nonneg d)
      _ = (32 / 31) * ‖d‖ * ‖1 + d‖ := by ring
  have hdM : ‖d‖ ≤ C₀ * (M * Real.exp (-(κ * z.im))) := by
    calc ‖d‖ = ‖Work.Pert.liftF u σ α z - (z + 1)‖ := by rw [hd]
      _ ≤ C₀ * ‖Work.Pert.tauC σ α z‖ := hC₀ z hz
      _ ≤ C₀ * (M * Real.exp (-(κ * z.im))) :=
            mul_le_mul_of_nonneg_left (hdec z hz hY) (le_of_lt hC₀pos)
  calc ‖(Work.Pert.liftF u σ α z - z)⁻¹ - 1‖
      = ‖d‖ / ‖1 + d‖ := by rw [hmain, norm_div, norm_neg]
    _ ≤ (32 / 31) * ‖d‖ := hbound
    _ ≤ (32 / 31) * (C₀ * (M * Real.exp (-(κ * z.im)))) :=
          mul_le_mul_of_nonneg_left hdM (by norm_num)
    _ = (32 / 31) * (C₀ * M) * Real.exp (-(κ * z.im)) := by ring

end Work.Pert
