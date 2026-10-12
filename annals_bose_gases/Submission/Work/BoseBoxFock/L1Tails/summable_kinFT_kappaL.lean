import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.L1Tails.DefsC
import Submission.Work.BoseFixB1S.kineticCrux.kinFT_decay_scale
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.L1Tails

open MeasureTheory
open scoped BigOperators Real

/-- Elementary convexity bound: `(1 + t)^4 ≤ 8 (1 + t^4)` for `t ≥ 0`
(two applications of `(a+b)^2 ≤ 2(a^2+b^2)`). -/
private lemma one_add_pow_four_le_eight (t : ℝ) (ht : 0 ≤ t) : (1 + t) ^ 4 ≤ 8 * (1 + t ^ 4) := by
  have h2 : (1 + t) ^ 2 ≤ 2 * (1 + t ^ 2) := by nlinarith [sq_nonneg (1 - t)]
  have h4 : (1 + t) ^ 4 = ((1 + t) ^ 2) ^ 2 := by ring
  rw [h4]
  have h5 : ((1 + t) ^ 2) ^ 2 ≤ (2 * (1 + t ^ 2)) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
  have h6 : (2 * (1 + t ^ 2)) ^ 2 ≤ 8 * (1 + t ^ 4) := by nlinarith [sq_nonneg (1 - t ^ 2)]
  linarith

/-- `‖kappaL ℓ n‖ = (2π/ℓ)‖latVec n‖`: the lattice momentum is `ℓ⁻¹ • vec n` and
`vec n = (2π) • latVec n`. -/
private lemma norm_kappaL_eq_two_pi_div_mul (ℓ : ℝ) (hℓ : 0 < ℓ) (n : Fin 3 → ℤ) :
    ‖Work.BoseBoxFock.kappaL ℓ n‖ =
      (2 * Real.pi / ℓ) * ‖Work.BoseBoxFock.latVec n‖ := by
  have hvec : Work.BoseB4.vec n = (2 * Real.pi) • Work.BoseBoxFock.latVec n := by
    ext i
    simp [Work.BoseB4.vec, Work.BoseBoxFock.latVec_apply]
  rw [show Work.BoseBoxFock.kappaL ℓ n = ℓ⁻¹ • Work.BoseB4.vec n from rfl, hvec, smul_smul,
    norm_smul, norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr hℓ.le),
    Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  ring

/-- The `p`-convention Fourier transform is bounded by the `L¹` norm. -/
private lemma norm_kinFT_le_integral_norm (Φ : EuclideanSpace ℝ (Fin 3) → ℂ)
    (p : EuclideanSpace ℝ (Fin 3)) :
    ‖Submission.BoseGases.kinFT Φ p‖ ≤ ∫ x, ‖Φ x‖ := by
  calc ‖Submission.BoseGases.kinFT Φ p‖
      = ‖∫ y, Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * Φ y‖ := rfl
    _ ≤ ∫ y, ‖Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * Φ y‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ y, ‖Φ y‖ := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards with y
        rw [norm_mul, Complex.norm_exp]
        have hre : (-(Complex.I * (inner ℝ p y : ℂ))).re = 0 := by
          simp [Complex.mul_re, Complex.neg_re, Complex.I_re, Complex.I_im]
        rw [hre, Real.exp_zero, one_mul]

/-- ℓ¹-summability of the lattice samples `kinFT Φ (κ_n)` of a smooth compactly supported `Φ`.
Route: `Work.BoseFixB1S.kineticCrux.kinFT_decay_core` at `N = 4` gives
`‖p‖^4 * ‖kinFT Φ p‖ ≤ ∫ x, ‖iteratedFDeriv ℝ 4 Φ x‖ =: B`, and `‖kinFT Φ p‖ ≤ ∫ x, ‖Φ x‖ =: A`
directly, so `‖kinFT Φ p‖ ≤ C (1+‖p‖)^{-4}` with `C` depending on `A,B`; with
`‖kappaL ℓ n‖ = (2π/ℓ)‖latVec n‖` this follows from
`Work.BoseBoxFock.summable_one_add_norm_latVec_pow_inv (N := 4)`. -/
theorem summable_kinFT_kappaL {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hc : HasCompactSupport Φ) :
    Summable (fun n : Fin 3 → ℤ =>
      ‖Submission.BoseGases.kinFT Φ (Work.BoseBoxFock.kappaL ℓ n)‖) := by
  have hAl : 0 ≤ ∫ x, ‖Φ x‖ := MeasureTheory.integral_nonneg (fun x => norm_nonneg _)
  have hBl : 0 ≤ ∫ x, ‖iteratedFDeriv ℝ 4 Φ x‖ :=
    MeasureTheory.integral_nonneg (fun x => norm_nonneg _)
  -- the two pointwise estimates of the Fourier transform
  have hA : ∀ p, ‖Submission.BoseGases.kinFT Φ p‖ ≤ ∫ x, ‖Φ x‖ :=
    fun p => norm_kinFT_le_integral_norm Φ p
  have hB : ∀ p, ‖p‖ ^ 4 * ‖Submission.BoseGases.kinFT Φ p‖ ≤
      ∫ x, ‖iteratedFDeriv ℝ 4 Φ x‖ :=
    fun p => Work.BoseFixB1S.kineticCrux.kinFT_decay_core 4 Φ hΦ hc p
  -- hence `(1+‖p‖)^4 ‖kinFT Φ p‖` is bounded
  obtain ⟨C0, hC0nn, hpt⟩ : ∃ C0 : ℝ, 0 ≤ C0 ∧
      ∀ p : EuclideanSpace ℝ (Fin 3),
        (1 + ‖p‖) ^ 4 * ‖Submission.BoseGases.kinFT Φ p‖ ≤ C0 := by
    refine ⟨8 * (∫ x, ‖Φ x‖) + 8 * (∫ x, ‖iteratedFDeriv ℝ 4 Φ x‖), by linarith, ?_⟩
    intro p
    have hkey := one_add_pow_four_le_eight ‖p‖ (norm_nonneg p)
    have hk : 0 ≤ ‖Submission.BoseGases.kinFT Φ p‖ := norm_nonneg _
    have step : (1 + ‖p‖) ^ 4 * ‖Submission.BoseGases.kinFT Φ p‖
        ≤ 8 * (1 + ‖p‖ ^ 4) * ‖Submission.BoseGases.kinFT Φ p‖ :=
      mul_le_mul_of_nonneg_right hkey hk
    have hexp : 8 * (1 + ‖p‖ ^ 4) * ‖Submission.BoseGases.kinFT Φ p‖
        = 8 * ‖Submission.BoseGases.kinFT Φ p‖
          + 8 * (‖p‖ ^ 4 * ‖Submission.BoseGases.kinFT Φ p‖) := by ring
    rw [hexp] at step
    linarith [hA p, hB p]
  -- consequently `‖kinFT Φ p‖ ≤ C0 (1+‖p‖)^{-4}`
  have hpb : ∀ p, ‖Submission.BoseGases.kinFT Φ p‖ ≤ C0 * ((1 + ‖p‖) ^ 4)⁻¹ := by
    intro p
    have hp4 : 0 < (1 + ‖p‖) ^ 4 := by positivity
    have hcancel : ((1 + ‖p‖) ^ 4)⁻¹ * ((1 + ‖p‖) ^ 4 * ‖Submission.BoseGases.kinFT Φ p‖)
        = ‖Submission.BoseGases.kinFT Φ p‖ := by
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hp4), one_mul]
    calc ‖Submission.BoseGases.kinFT Φ p‖
        = ((1 + ‖p‖) ^ 4)⁻¹ * ((1 + ‖p‖) ^ 4 * ‖Submission.BoseGases.kinFT Φ p‖) :=
          hcancel.symm
      _ ≤ ((1 + ‖p‖) ^ 4)⁻¹ * C0 :=
          mul_le_mul_of_nonneg_left (hpt p) (inv_nonneg.mpr hp4.le)
      _ = C0 * ((1 + ‖p‖) ^ 4)⁻¹ := by ring
  -- the comparison of the lattice norms
  set α : ℝ := 2 * Real.pi / ℓ with hαdef
  have hαpos : 0 < α := by rw [hαdef]; positivity
  set m : ℝ := min α 1 with hmdef
  have hmpos : 0 < m := by rw [hmdef]; exact lt_min hαpos one_pos
  have hm1 : m ≤ 1 := by rw [hmdef]; exact min_le_right _ _
  have hmα : m ≤ α := by rw [hmdef]; exact min_le_left _ _
  have hmul : ∀ t : ℝ, 0 ≤ t → m * (1 + t) ≤ 1 + α * t := by
    intro t ht
    calc m * (1 + t) = m + m * t := by ring
      _ ≤ 1 + α * t := add_le_add hm1 (mul_le_mul_of_nonneg_right hmα ht)
  have hnorm : ∀ n : Fin 3 → ℤ,
      ‖Work.BoseBoxFock.kappaL ℓ n‖ = α * ‖Work.BoseBoxFock.latVec n‖ := by
    intro n
    rw [hαdef]
    exact norm_kappaL_eq_two_pi_div_mul ℓ hℓ n
  -- and the inverse comparison
  have hinv : ∀ n : Fin 3 → ℤ,
      ((1 + ‖Work.BoseBoxFock.kappaL ℓ n‖) ^ 4)⁻¹
        ≤ (m ^ 4)⁻¹ * ((1 + ‖Work.BoseBoxFock.latVec n‖) ^ 4)⁻¹ := by
    intro n
    rw [hnorm n]
    have ht : 0 ≤ ‖Work.BoseBoxFock.latVec n‖ := norm_nonneg _
    have hle : m * (1 + ‖Work.BoseBoxFock.latVec n‖)
        ≤ 1 + α * ‖Work.BoseBoxFock.latVec n‖ := hmul _ ht
    have hmp : 0 < m * (1 + ‖Work.BoseBoxFock.latVec n‖) := mul_pos hmpos (by linarith)
    have h1 : 0 < (1 + α * ‖Work.BoseBoxFock.latVec n‖) ^ 4 := by positivity
    have h2 : 0 < m ^ 4 * (1 + ‖Work.BoseBoxFock.latVec n‖) ^ 4 := by positivity
    have hpow : m ^ 4 * (1 + ‖Work.BoseBoxFock.latVec n‖) ^ 4
        ≤ (1 + α * ‖Work.BoseBoxFock.latVec n‖) ^ 4 := by
      have h := pow_le_pow_left₀ hmp.le hle 4
      rwa [mul_pow] at h
    have h3 := (inv_le_inv₀ h1 h2).mpr hpow
    rwa [mul_inv] at h3
  -- summability of the majorant
  have hsum : Summable (fun n : Fin 3 → ℤ =>
      ((1 + ‖Work.BoseBoxFock.latVec n‖) ^ 4)⁻¹) :=
    Work.BoseBoxFock.summable_one_add_norm_latVec_pow_inv (N := 4) le_rfl
  have hmaj : Summable (fun n : Fin 3 → ℤ =>
      C0 * (m ^ 4)⁻¹ * ((1 + ‖Work.BoseBoxFock.latVec n‖) ^ 4)⁻¹) :=
    hsum.mul_left (C0 * (m ^ 4)⁻¹)
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hmaj
  calc ‖Submission.BoseGases.kinFT Φ (Work.BoseBoxFock.kappaL ℓ n)‖
      ≤ C0 * ((1 + ‖Work.BoseBoxFock.kappaL ℓ n‖) ^ 4)⁻¹ := hpb _
    _ ≤ C0 * ((m ^ 4)⁻¹ * ((1 + ‖Work.BoseBoxFock.latVec n‖) ^ 4)⁻¹) :=
        mul_le_mul_of_nonneg_left (hinv n) hC0nn
    _ = C0 * (m ^ 4)⁻¹ * ((1 + ‖Work.BoseBoxFock.latVec n‖) ^ 4)⁻¹ := by ring

end Work.BoseBoxFock.L1Tails
