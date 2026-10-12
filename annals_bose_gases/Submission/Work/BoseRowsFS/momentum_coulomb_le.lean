import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB7AK.C3Q.I2_integral_bound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section
open MeasureTheory

namespace Work.BoseRowsFS

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-- **Momentum-space Coulomb energy of an even a.e.-nonnegative kernel `W` dominated a.e. by `c·g₀`**: at most `c²` times the Newton energy `∫g₀ω` of `g₀`. `I2coul W = ∫⁻ z ∂(volume×volume), ofReal (W z.1 * W z.2 / ‖z.1-z.2‖)` is the corpus's double lintegral (`Work.BoseB7AK.C3Q.I2coul`), and `(2π)⁻³∫p, Ŵ(p)²/(2‖p‖²) = (1/8π)(I2coul W).toReal` for integrable, a.e. nonnegative, even `W` (`Work.BoseB7AK.C3Q.chat_sq_div_eq_coulomb_toReal`); monotonicity (`I2coul_mono_ae_mul`) gives `I2coul W ≤ ofReal(c·c)·I2coul g₀`, and `I2coul g₀ = ofReal (8π ∫g₀ω)` (`Work.BoseB7AK.C3Q.lintegral_double_eq_ofReal_newton` + `Submission.BoseGases.scattering_newton_representation`). -/
theorem momentum_coulomb_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R ℓ c : ℝ}
    (hR : 0 < R) (hℓ : 0 < ℓ) (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) (h : Work.UBB.ScatSol v)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) (hc : 0 ≤ c)
    {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hW : MeasureTheory.Integrable W)
    (hW0 : ∀ᵐ x, 0 ≤ W x) (hWe : ∀ x, W (-x) = W x)
    (hle : ∀ᵐ x, W x ≤ c * Submission.BoseGases.g0 v h x) :
    ((2 * Real.pi) ^ 3)⁻¹
        * (∫ k, (Work.BoseFixR.chat W k) ^ 2 / (2 * ‖k‖ ^ 2))
      ≤ c ^ 2 * (∫ x, Submission.BoseGases.g0 v h x * Classical.choose h x) := by
  obtain ⟨hrad, hw⟩ := Classical.choose_spec h
  set g : EuclideanSpace ℝ (Fin 3) → ℝ := Submission.BoseGases.g0 v h with hg
  set ω : EuclideanSpace ℝ (Fin 3) → ℝ := Classical.choose h with hω
  -- the a.e. facts about `g₀` (and `ω`)
  have hgI : MeasureTheory.Integrable g := by
    simpa only [hg] using Submission.BoseGases.g0_integrable hR hv_supp h
  have hgsupp : ∀ x, R ≤ ‖x‖ → g x = 0 := by
    intro x hx
    simpa only [hg] using Submission.BoseGases.g0_zero_of_norm_ge hv_supp hx h
  have hg0 : ∀ᵐ x, 0 ≤ g x := by
    simpa only [hg] using Submission.BoseGases.g0_nonneg_ae hR hv_nonneg hvrad hv_supp h
  have hgωI : MeasureTheory.Integrable (fun x => g x * ω x) := by
    simpa only [hg, hω] using Submission.BoseGases.g0w0_integrable hR hv_nonneg hvrad hv_supp h
  have hgω0 : ∀ᵐ x, 0 ≤ g x * ω x := by
    simpa only [hg, hω, Work.BoseB7AK.W1rows.W1omegaNum, Submission.BoseGases.g0] using
      Work.BoseB7AK.W1rows.W1omegaNum_nonneg_ae hR hv_nonneg hvrad hv_supp h
  have hrep : ∀ᵐ x, ω x = (1 / (8 * Real.pi)) * ∫ y, g y * ‖x - y‖⁻¹ := by
    have h0 := Submission.BoseGases.scattering_newton_representation (v := v)
      (w := Classical.choose h) (R := R) hR hvrad hv_supp hrad hw
    simpa only [hω, hg, Submission.BoseGases.g0] using h0
  have hI0 : 0 ≤ ∫ x, g x * ω x := integral_nonneg_of_ae hgω0
  -- the value of the double lintegral at `g₀` and monotonicity
  have hgval : Work.BoseB7AK.C3Q.I2coul g
      = ENNReal.ofReal (8 * Real.pi * ∫ x, g x * ω x) := by
    rw [Work.BoseB7AK.C3Q.I2coul_iterated hgI.aestronglyMeasurable]
    exact Work.BoseB7AK.C3Q.lintegral_double_eq_ofReal_newton hgI hg0 hgsupp hR.le
      hgωI hgω0 hrep
  have hmono : Work.BoseB7AK.C3Q.I2coul W ≤ ENNReal.ofReal (c * c)
      * Work.BoseB7AK.C3Q.I2coul g :=
    Work.BoseB7AK.C3Q.I2coul_mono_ae_mul hc hW.aestronglyMeasurable
      hgI.aestronglyMeasurable hW0 hg0 hle
  have hcc : 0 ≤ c * c := mul_self_nonneg c
  have h8I : 0 ≤ (8 : ℝ) * Real.pi * ∫ x, g x * ω x :=
    mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hI0
  -- the double lintegral of `W` is dominated by `ofReal (c²·8π∫g₀ω)`
  have hYle : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y / ‖x - y‖))
      ≤ ENNReal.ofReal (c * c * (8 * Real.pi * ∫ x, g x * ω x)) := by
    calc (∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y / ‖x - y‖))
        = Work.BoseB7AK.C3Q.I2coul W :=
          (Work.BoseB7AK.C3Q.I2coul_iterated hW.aestronglyMeasurable).symm
      _ ≤ ENNReal.ofReal (c * c) * Work.BoseB7AK.C3Q.I2coul g := hmono
      _ = ENNReal.ofReal (c * c) * ENNReal.ofReal (8 * Real.pi * ∫ x, g x * ω x) := by
          rw [hgval]
      _ = ENNReal.ofReal (c * c * (8 * Real.pi * ∫ x, g x * ω x)) :=
          (ENNReal.ofReal_mul hcc).symm
  have hYto : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y / ‖x - y‖)).toReal
      ≤ c * c * (8 * Real.pi * ∫ x, g x * ω x) := by
    have hfin := ENNReal.toReal_mono ENNReal.ofReal_ne_top hYle
    rwa [ENNReal.toReal_ofReal (mul_nonneg hcc h8I)] at hfin
  -- Fourier–Coulomb identity and the scalar arithmetic
  rw [Work.BoseB7AK.C3Q.chat_sq_div_eq_coulomb_toReal hW hW0 hWe]
  refine le_trans (mul_le_mul_of_nonneg_left hYto (by positivity)) (le_of_eq ?_)
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

end Work.BoseRowsFS
