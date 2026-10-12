import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.L1Tails.latPerC_fourierCoeff
import Submission.Work.BoseBoxFock.L1Tails.latPerC_hasSum_fourier
import Submission.Work.BoseBoxFock.L1Tails.summable_kinFT_kappaL
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

open MeasureTheory Filter
open scoped BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- Expansion of the pairing of an `L¹` weight `W` against the periodisation `latPerC ℓ Φ` of a
smooth compactly supported `Φ`: the lattice Fourier series of `latPerC ℓ Φ` is absolutely and
uniformly convergent, so the pairing is the lattice sum of the Fourier coefficients.
(`Work.BoseBoxFock.L1Tails.latPerC_hasSum_fourier` gives, for every `z`,
`HasSum (fun n => (ℓ³)⁻¹ * kinFT Φ (κ_n) * exp(I ⟪κ_n, z⟫)) (latPerC ℓ Φ z)`; the coefficient
identity is `Work.BoseBoxFock.L1Tails.latPerC_fourierCoeff` and the ℓ¹-summability of the samples is
`Work.BoseBoxFock.L1Tails.summable_kinFT_kappaL`.  Integrate termwise with
`MeasureTheory.hasSum_integral_of_summable_integral_norm`, dominating by `Σ_n ‖(ℓ³)⁻¹ kinFT Φ (κ_n)‖ * ‖W‖`.) -/
theorem latPerCWeightIntegral {ℓ : ℝ} (hℓ : 0 < ℓ)
    {W : EuclideanSpace ℝ (Fin 3) → ℂ} (hW : MeasureTheory.Integrable W)
    {Φ : EuclideanSpace ℝ (Fin 3) → ℂ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hΦs : HasCompactSupport Φ) :
    ∫ z, W z * Work.BoseBoxFock.L1Tails.latPerC ℓ Φ z
      = ∑' n : Fin 3 → ℤ,
          (∫ z, W z * Complex.exp (Complex.I *
              ((inner ℝ (Work.BoseBoxFock.kappaL ℓ n) z : ℝ) : ℂ)))
            * ((ℓ ^ 3)⁻¹ * Submission.BoseGases.kinFT Φ (Work.BoseBoxFock.kappaL ℓ n)) := by
  classical
  -- ## a radius outside which `Φ` vanishes, and a bound for `Φ`
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ x : E3, R < ‖x‖ → Φ x = 0 := by
    obtain ⟨ρ, hρ⟩ := hΦs.isBounded.subset_closedBall (0 : E3)
    refine ⟨ρ, fun x hx => image_eq_zero_of_notMem_tsupport fun hmem => ?_⟩
    have h1 := hρ hmem
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h1
    linarith
  obtain ⟨CΦ, hCΦ⟩ : ∃ C : ℝ, ∀ x : E3, ‖Φ x‖ ≤ C := by
    obtain ⟨ρ, hρ⟩ := hΦs.isBounded.subset_closedBall (0 : E3)
    obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : E3) ρ).exists_bound_of_continuousOn
      hΦ.continuous.continuousOn
    refine ⟨max B 0, fun x => ?_⟩
    by_cases hx : x ∈ Metric.closedBall (0 : E3) ρ
    · exact le_trans (hB x hx) (le_max_left _ _)
    · have h0 : Φ x = 0 := image_eq_zero_of_notMem_tsupport fun hmem => hx (hρ hmem)
      rw [h0, norm_zero]
      exact le_max_right _ _
  -- ## the two inputs of the lattice Fourier expansion
  have hsumm : Summable (fun n : Fin 3 → ℤ =>
      ‖Submission.BoseGases.kinFT Φ (Work.BoseBoxFock.kappaL ℓ n)‖) :=
    Work.BoseBoxFock.L1Tails.summable_kinFT_kappaL hℓ hΦ hΦs
  have hcoeff : ∀ n : Fin 3 → ℤ,
      (∫ z in Work.BoseBoxFock.LatFourier.latCell ℓ,
          Work.BoseBoxFock.L1Tails.latPerC ℓ Φ z
            * Complex.exp (-(Complex.I * ((inner ℝ (Work.BoseBoxFock.kappaL ℓ n) z : ℝ) : ℂ))))
        = Submission.BoseGases.kinFT Φ (Work.BoseBoxFock.kappaL ℓ n) :=
    fun n => Work.BoseBoxFock.L1Tails.latPerC_fourierCoeff hℓ
      hΦ.continuous.aestronglyMeasurable ⟨CΦ, hCΦ⟩ hR n
  have hHS : ∀ z : E3, HasSum (fun n : Fin 3 → ℤ =>
      (ℓ ^ 3)⁻¹ * Submission.BoseGases.kinFT Φ (Work.BoseBoxFock.kappaL ℓ n)
        * Complex.exp (Complex.I * ((inner ℝ (Work.BoseBoxFock.kappaL ℓ n) z : ℝ) : ℂ)))
      (Work.BoseBoxFock.L1Tails.latPerC ℓ Φ z) :=
    fun z => Work.BoseBoxFock.L1Tails.latPerC_hasSum_fourier hℓ hΦ hΦs hsumm hcoeff z
  -- ## the summand family and its elementary properties
  let χ : (Fin 3 → ℤ) → E3 → ℂ := fun n z =>
    Complex.exp (Complex.I * ((inner ℝ (Work.BoseBoxFock.kappaL ℓ n) z : ℝ) : ℂ))
  let f : (Fin 3 → ℤ) → E3 → ℂ := fun n z =>
    W z * (((ℓ ^ 3)⁻¹ * Submission.BoseGases.kinFT Φ (Work.BoseBoxFock.kappaL ℓ n)) * χ n z)
  have hχnorm : ∀ n z, ‖χ n z‖ = 1 := by
    intro n z
    show ‖Complex.exp (Complex.I * ((inner ℝ (Work.BoseBoxFock.kappaL ℓ n) z : ℝ) : ℂ))‖ = 1
    rw [mul_comm Complex.I _, Complex.norm_exp_ofReal_mul_I]
  have hχcont : ∀ n, Continuous (χ n) := by
    intro n
    show Continuous (fun z : E3 => Complex.exp (Complex.I *
      ((inner ℝ (Work.BoseBoxFock.kappaL ℓ n) z : ℝ) : ℂ)))
    exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
      (continuous_const.inner continuous_id)))
  -- ## pointwise summation of the series against `W`
  have hpoint : ∀ z : E3, (∑' n : Fin 3 → ℤ, f n z)
      = W z * Work.BoseBoxFock.L1Tails.latPerC ℓ Φ z := by
    intro z
    have h1 := (hHS z).mul_left (W z)
    rw [← h1.tsum_eq]
  have hInt : (∫ z, ∑' n : Fin 3 → ℤ, f n z)
      = ∫ z, W z * Work.BoseBoxFock.L1Tails.latPerC ℓ Φ z :=
    integral_congr_ae (Eventually.of_forall hpoint)
  -- ## the norm of the summands and the domination of the lattice series
  have hnormint : ∀ n : Fin 3 → ℤ,
      (∫ z, ‖f n z‖)
        = ‖(ℓ ^ 3)⁻¹ * Submission.BoseGases.kinFT Φ (Work.BoseBoxFock.kappaL ℓ n)‖
          * (∫ z, ‖W z‖) := by
    intro n
    rw [show (fun z => ‖f n z‖) = fun z =>
        ‖(ℓ ^ 3)⁻¹ * Submission.BoseGases.kinFT Φ (Work.BoseBoxFock.kappaL ℓ n)‖ * ‖W z‖ from
      funext fun z => by
        show ‖W z * (((ℓ ^ 3)⁻¹ * Submission.BoseGases.kinFT Φ (Work.BoseBoxFock.kappaL ℓ n))
          * χ n z)‖ = ‖(ℓ ^ 3)⁻¹ * Submission.BoseGases.kinFT Φ (Work.BoseBoxFock.kappaL ℓ n)‖
            * ‖W z‖
        rw [norm_mul, norm_mul, hχnorm n z, mul_one, mul_comm]]
    rw [integral_const_mul]
  have hfint : ∀ n : Fin 3 → ℤ, Integrable (f n) volume := by
    intro n
    have hmaj : Integrable (fun z : E3 =>
        ‖(ℓ ^ 3)⁻¹ * Submission.BoseGases.kinFT Φ (Work.BoseBoxFock.kappaL ℓ n)‖ * ‖W z‖)
        volume := hW.norm.const_mul _
    refine Integrable.mono' hmaj ?_ ?_
    · exact hW.aestronglyMeasurable.mul ((continuous_const.mul (hχcont n)).aestronglyMeasurable)
    · filter_upwards with z
      show ‖W z * (((ℓ ^ 3)⁻¹ * Submission.BoseGases.kinFT Φ (Work.BoseBoxFock.kappaL ℓ n))
        * χ n z)‖ ≤ ‖(ℓ ^ 3)⁻¹ * Submission.BoseGases.kinFT Φ (Work.BoseBoxFock.kappaL ℓ n)‖
          * ‖W z‖
      rw [norm_mul, norm_mul, hχnorm n z, mul_one, mul_comm]
  have hbs : Summable (fun n : Fin 3 → ℤ =>
      ‖(ℓ ^ 3)⁻¹ * Submission.BoseGases.kinFT Φ (Work.BoseBoxFock.kappaL ℓ n)‖) := by
    refine (hsumm.mul_left ‖(ℓ ^ 3)⁻¹‖).congr (fun n => ?_)
    rw [norm_mul]
    simp
  have hfsumm : Summable (fun n : Fin 3 → ℤ => ∫ z, ‖f n z‖) := by
    refine (hbs.mul_right (∫ z, ‖W z‖)).congr (fun n => ?_)
    exact (hnormint n).symm
  -- ## termwise integration
  have hmain := MeasureTheory.hasSum_integral_of_summable_integral_norm hfint hfsumm
  have hval : ∀ n : Fin 3 → ℤ,
      (∫ z, f n z) = (∫ z, W z * Complex.exp (Complex.I *
          ((inner ℝ (Work.BoseBoxFock.kappaL ℓ n) z : ℝ) : ℂ)))
        * ((ℓ ^ 3)⁻¹ * Submission.BoseGases.kinFT Φ (Work.BoseBoxFock.kappaL ℓ n)) := by
    intro n
    rw [show (fun z => f n z) = fun z => (W z * Complex.exp (Complex.I *
          ((inner ℝ (Work.BoseBoxFock.kappaL ℓ n) z : ℝ) : ℂ)))
        * ((ℓ ^ 3)⁻¹ * Submission.BoseGases.kinFT Φ (Work.BoseBoxFock.kappaL ℓ n)) from
      funext fun z => by
        show W z * (((ℓ ^ 3)⁻¹ * Submission.BoseGases.kinFT Φ (Work.BoseBoxFock.kappaL ℓ n))
          * χ n z) = (W z * Complex.exp (Complex.I *
            ((inner ℝ (Work.BoseBoxFock.kappaL ℓ n) z : ℝ) : ℂ)))
          * ((ℓ ^ 3)⁻¹ * Submission.BoseGases.kinFT Φ (Work.BoseBoxFock.kappaL ℓ n))
        ring]
    rw [integral_mul_const]
  calc ∫ z, W z * Work.BoseBoxFock.L1Tails.latPerC ℓ Φ z
      = ∫ z, ∑' n : Fin 3 → ℤ, f n z := hInt.symm
    _ = ∑' n : Fin 3 → ℤ, ∫ z, f n z := hmain.tsum_eq.symm
    _ = ∑' n : Fin 3 → ℤ, (∫ z, W z * Complex.exp (Complex.I *
          ((inner ℝ (Work.BoseBoxFock.kappaL ℓ n) z : ℝ) : ℂ)))
        * ((ℓ ^ 3)⁻¹ * Submission.BoseGases.kinFT Φ (Work.BoseBoxFock.kappaL ℓ n)) :=
        tsum_congr hval

end Work.BoseBoxFock.PCFU
