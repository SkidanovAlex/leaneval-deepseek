import Mathlib
import Submission.Work.CRad.deps
import Submission.Work.CRad.cauchy_coeff_decay_ball

open scoped NNReal

/-
# Geometric decay of the companion coefficients `dₙ(a)` on the cusp disc

The `ρ`-extension `g(z) := F(ρ_a − z)` of the companion product `H(a,·) − η_a·A(a,·)`
(`F` being the even descent of `G_0` from `beukersG0_descends_sq_onBall`, the
brick-A4 output) is holomorphic on the whole disc `‖z‖ < R0² − ρ_a` with
`R0² = 2√(a²−1) − 1` (`beukers_apéry_g_differentiableOn_cuspDisc`), and its Taylor
series at `0` is the `d`-series `Σ (vₙ(a) − η_a·uₙ(a)) zⁿ`
(`beukers_apéry_g_hasFPowerSeriesAt`).  Cauchy's estimate at any interior radius
`r < R0² − ρ_a = 2√(a²−1) − 1 − ρ_a` therefore gives the geometric decay
`‖dₙ(a)‖ ≤ C·(1/r)ⁿ`.
-/

namespace Work.CRad

open Submission.CDT

theorem d_decay_cuspDisc (a : ℝ) (ha : 3 ≤ a) {r : ℝ} (hr0 : 0 < r)
    (hr : r < 2 * Real.sqrt (a ^ 2 - 1) - 1 - Submission.CDT.beukersRho a) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ‖(Submission.CDT.beukersD a n : ℂ)‖ ≤ C * (1 / r) ^ n := by
  classical
  -- the descent radius `R0` with `R0² = 2√(a²−1) − 1`, and the brick-A4 descent
  let R0 : ℝ≥0 := beukersR0sharp a
  have hR0posNN : 0 < R0 := by
    dsimp [R0, beukersR0sharp]
    apply Real.sqrt_pos_of_pos
    have hsq : 0 ≤ a ^ 2 - 1 := by nlinarith [sq_nonneg a]
    have h8 : 8 ≤ a ^ 2 - 1 := by nlinarith
    have hs := Real.sqrt_le_sqrt (by exact_mod_cast h8)
    have hq : (1 / 2 : ℝ) ^ 2 < 8 := by norm_num
    have hlt := Real.sqrt_lt_sqrt (by positivity : 0 ≤ (1 / 2 : ℝ) ^ 2) hq
    have hA : Real.sqrt ((1 / 2 : ℝ) ^ 2) = 1 / 2 := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))]
    have h12 : (1 / 2 : ℝ) < Real.sqrt 8 := by simpa [hA] using hlt
    have hsqrt : Real.sqrt 8 ≤ Real.sqrt (a ^ 2 - 1) := hs
    nlinarith
  have hR0big_ρ : beukersRho a < (R0 : ℝ) ^ 2 := by
    rw [beukersR0sharp_sq a ha]
    have h2 : beukersRho a + 2 < 2 * Real.sqrt (a ^ 2 - 1) :=
      beukers_rho_add_two_lt_two_sqrt a ha
    nlinarith
  rcases beukersG0_descends_sq_onBall a ha R0 hR0posNN (beukersR0sharp_lt_Ru a ha) with
    ⟨F, q, hF, hF0, hFdesc⟩
  -- the hypothesis is exactly `r < R0² − ρ_a`
  have hRd : (R0 : ℝ) ^ 2 - beukersRho a = 2 * Real.sqrt (a ^ 2 - 1) - 1 - beukersRho a := by
    rw [beukersR0sharp_sq a ha]
  have hrRd : r < (R0 : ℝ) ^ 2 - beukersRho a := by rw [hRd]; exact hr
  -- an intermediate radius `r < r' < R0² − ρ_a`
  let r' : ℝ := (r + ((R0 : ℝ) ^ 2 - beukersRho a)) / 2
  have hrr' : r < r' := by dsimp [r']; linarith
  have hr'd : r' < (R0 : ℝ) ^ 2 - beukersRho a := by dsimp [r']; linarith
  have hdball : DifferentiableOn ℂ (beukersApéryRhoExt a F) (Metric.ball (0 : ℂ) r') :=
    beukers_apéry_g_differentiableOn_cuspDisc a ha hR0big_ρ hF r' hr'd
  -- the Taylor series of `g` at `0` is the `d`-series
  have hp : HasFPowerSeriesAt (beukersApéryRhoExt a F)
      (FormalMultilinearSeries.ofScalars ℂ (fun n => (beukersD a n : ℂ))) 0 := by
    have h := beukers_apéry_g_hasFPowerSeriesAt a ha hR0big_ρ hF hFdesc
    simpa [beukersD] using h
  have hc : ∀ n : ℕ, (FormalMultilinearSeries.ofScalars ℂ (fun n => (beukersD a n : ℂ))) n
      (fun _ : Fin n => (1 : ℂ)) = (beukersD a n : ℂ) := by
    intro n
    simp [FormalMultilinearSeries.ofScalars]
  -- Cauchy's estimate at the interior radius `r`
  exact cauchy_coeff_decay_ball hr0 hrr' hdball hp hc

end Work.CRad
