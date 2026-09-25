import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Convolution

namespace Commons.Analysis.Fourier

open MeasureTheory
open scoped ENNReal

/-- Weighted Cauchy--Schwarz in `ℝ≥0∞`, squared form: for ae-measurable `a b`,
`(∫ a * b) ^ 2 ≤ (∫ a) * (∫ a * b ^ 2)`. -/
private lemma sq_lintegral_mul_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {a b : α → ℝ≥0∞} (ha : AEMeasurable a μ) (hb : AEMeasurable b μ) :
    (∫⁻ y, a y * b y ∂μ) ^ (2:ℝ) ≤
      (∫⁻ y, a y ∂μ) * (∫⁻ y, a y * b y ^ (2:ℝ) ∂μ) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
      (ha.pow_const (1/2 : ℝ)) ((ha.pow_const (1/2 : ℝ)).mul hb)
  simp only [Pi.mul_apply] at h
  have hA : ∫⁻ y, a y ^ (1/2:ℝ) * (a y ^ (1/2:ℝ) * b y) ∂μ = ∫⁻ y, a y * b y ∂μ := by
    apply lintegral_congr; intro y
    have h1 : a y ^ (1/2:ℝ) * a y ^ (1/2:ℝ) = a y := by
      rw [← ENNReal.rpow_add_of_nonneg (1/2) (1/2) (by norm_num) (by norm_num),
        show (1/2:ℝ) + 1/2 = 1 by norm_num, ENNReal.rpow_one]
    rw [← mul_assoc, h1]
  have hB : ∫⁻ y, (a y ^ (1/2:ℝ)) ^ (2:ℝ) ∂μ = ∫⁻ y, a y ∂μ := by
    apply lintegral_congr; intro y
    rw [← ENNReal.rpow_mul, show (1/2:ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]
  have hC : ∫⁻ y, (a y ^ (1/2:ℝ) * b y) ^ (2:ℝ) ∂μ = ∫⁻ y, a y * b y ^ (2:ℝ) ∂μ := by
    apply lintegral_congr; intro y
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    rw [← ENNReal.rpow_mul, show (1/2:ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]
  have h' : ∫⁻ y, a y * b y ∂μ ≤ (∫⁻ y, a y ∂μ) ^ (1/2:ℝ) *
      (∫⁻ y, a y * b y ^ (2:ℝ) ∂μ) ^ (1/2:ℝ) := by
    rw [← hA, ← hB, ← hC]
    exact h
  calc (∫⁻ y, a y * b y ∂μ) ^ (2:ℝ)
      ≤ ((∫⁻ y, a y ∂μ) ^ (1/2:ℝ) * (∫⁻ y, a y * b y ^ (2:ℝ) ∂μ) ^ (1/2:ℝ)) ^ (2:ℝ) :=
        ENNReal.rpow_le_rpow h' (by norm_num)
    _ = (∫⁻ y, a y ∂μ) * (∫⁻ y, a y * b y ^ (2:ℝ) ∂μ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]
        congr 1
        · rw [← ENNReal.rpow_mul, show (1/2:ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]
        · rw [← ENNReal.rpow_mul, show (1/2:ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]

theorem memLp_convolution_one_two {σ h : ℝ → ℂ}
    (hσ : MeasureTheory.MemLp σ 1 (MeasureTheory.volume)) :
    ∀ (hh : MeasureTheory.MemLp h 2 (MeasureTheory.volume)),
      MeasureTheory.MemLp (fun x : ℝ => ∫ y : ℝ, σ y * h (x - y)) 2 (MeasureTheory.volume) ∧
      ∫⁻ x : ℝ, ‖∫ y : ℝ, σ y * h (x - y)‖ₑ ^ (2:ℝ) ≤
        (∫⁻ y : ℝ, ‖σ y‖ₑ) ^ 2 * ∫⁻ x : ℝ, ‖h x‖ₑ ^ (2:ℝ) := by
  intro hh
  set F : ℝ → ℂ := fun x : ℝ => ∫ y : ℝ, σ y * h (x - y) with hFdef
  set S : ℝ≥0∞ := ∫⁻ y : ℝ, ‖σ y‖ₑ with hSdef
  set C : ℝ≥0∞ := ∫⁻ x : ℝ, ‖h x‖ₑ ^ (2:ℝ) with hCdef
  have hσm : AEMeasurable σ volume := hσ.aemeasurable
  have hhm : AEMeasurable h volume := hh.aemeasurable
  -- measurability of the convolution
  have hF_meas : AEStronglyMeasurable F volume := by
    have hG : AEStronglyMeasurable (fun p : ℝ × ℝ => σ p.2 * h (p.1 - p.2)) (volume.prod volume) :=
      hσ.aestronglyMeasurable.convolution_integrand (L := ContinuousLinearMap.mul ℂ ℂ)
        hh.aestronglyMeasurable
    have h := hG.integral_prod_right' (ν := volume)
    simpa [hFdef, ContinuousLinearMap.mul_apply'] using h
  -- pointwise bound of the convolution by the `lintegral`
  have hFA : ∀ x : ℝ, ‖F x‖ₑ ≤ ∫⁻ y : ℝ, ‖σ y‖ₑ * ‖h (x - y)‖ₑ := by
    intro x
    have h := enorm_integral_le_lintegral_enorm (μ := volume) (fun y : ℝ => σ y * h (x - y))
    simp only [enorm_mul] at h
    simpa [hFdef] using h
  have hσ_ae : AEMeasurable (fun y : ℝ => ‖σ y‖ₑ) volume := hσm.enorm
  have hh_shift : ∀ x : ℝ, AEMeasurable (fun y : ℝ => ‖h (x - y)‖ₑ) volume := by
    intro x
    exact (hhm.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_left_of_right_invariant volume x)).enorm
  have hh_shiftR : ∀ y : ℝ, AEMeasurable (fun x : ℝ => ‖h (x - y)‖ₑ) volume := by
    intro y
    have h1 : AEMeasurable (fun x : ℝ => h (x - y)) volume := by
      have h2 := hhm.comp_quasiMeasurePreserving
        (measurePreserving_add_right volume (-y)).quasiMeasurePreserving
      exact h2
    exact h1.enorm
  -- Cauchy-Schwarz step, for every `x`
  have hstep1 : ∀ x : ℝ, (∫⁻ y : ℝ, ‖σ y‖ₑ * ‖h (x - y)‖ₑ) ^ (2:ℝ) ≤
      S * ∫⁻ y : ℝ, ‖σ y‖ₑ * ‖h (x - y)‖ₑ ^ (2:ℝ) := by
    intro x
    have h := sq_lintegral_mul_le hσ_ae (hh_shift x)
    simpa [hSdef] using h
  -- measurability of the double-integrand and of the inner integral
  have hK_meas : AEMeasurable (fun z : ℝ × ℝ => ‖σ z.2‖ₑ * ‖h (z.1 - z.2)‖ₑ ^ (2:ℝ))
      (volume.prod volume) := by
    have h1 : AEMeasurable (fun z : ℝ × ℝ => ‖σ z.2‖ₑ) (volume.prod volume) :=
      hσ_ae.comp_snd
    have h2 : AEMeasurable (fun z : ℝ × ℝ => ‖h (z.1 - z.2)‖ₑ ^ (2:ℝ)) (volume.prod volume) := by
      have hsub : AEMeasurable (fun z : ℝ × ℝ => h (z.1 - z.2)) (volume.prod volume) :=
        hhm.comp_quasiMeasurePreserving
          (quasiMeasurePreserving_sub_of_right_invariant volume volume)
      exact (hsub.enorm).pow_const (2:ℝ)
    exact h1.mul h2
  have hT_meas : AEMeasurable (fun x : ℝ => ∫⁻ y : ℝ, ‖σ y‖ₑ * ‖h (x - y)‖ₑ ^ (2:ℝ)) volume := by
    have h := hK_meas.lintegral_prod_right' (ν := volume)
    simpa [Function.uncurry] using h
  have hstep2 : ∫⁻ x : ℝ, (∫⁻ y : ℝ, ‖σ y‖ₑ * ‖h (x - y)‖ₑ) ^ (2:ℝ) ≤
      S * ∫⁻ x : ℝ, (∫⁻ y : ℝ, ‖σ y‖ₑ * ‖h (x - y)‖ₑ ^ (2:ℝ)) := by
    calc ∫⁻ x : ℝ, (∫⁻ y : ℝ, ‖σ y‖ₑ * ‖h (x - y)‖ₑ) ^ (2:ℝ)
        ≤ ∫⁻ x : ℝ, S * (∫⁻ y : ℝ, ‖σ y‖ₑ * ‖h (x - y)‖ₑ ^ (2:ℝ)) :=
          lintegral_mono (fun x => hstep1 x)
      _ = S * ∫⁻ x : ℝ, (∫⁻ y : ℝ, ‖σ y‖ₑ * ‖h (x - y)‖ₑ ^ (2:ℝ)) :=
          lintegral_const_mul'' S hT_meas
  -- Tonelli plus translation invariance
  have hstep3 : ∫⁻ x : ℝ, (∫⁻ y : ℝ, ‖σ y‖ₑ * ‖h (x - y)‖ₑ ^ (2:ℝ)) = S * C := by
    have hK : AEMeasurable (Function.uncurry fun x y : ℝ => ‖σ y‖ₑ * ‖h (x - y)‖ₑ ^ (2:ℝ))
        (volume.prod volume) := hK_meas
    rw [lintegral_lintegral_swap hK]
    have hinner : ∀ y : ℝ, ∫⁻ x : ℝ, ‖σ y‖ₑ * ‖h (x - y)‖ₑ ^ (2:ℝ) = ‖σ y‖ₑ * C := by
      intro y
      rw [hCdef, lintegral_const_mul'' (‖σ y‖ₑ) ((hh_shiftR y).pow_const (2:ℝ))]
      congr 1
      exact lintegral_sub_right_eq_self (fun x : ℝ => ‖h x‖ₑ ^ (2:ℝ)) y
    simp_rw [hinner]
    rw [lintegral_mul_const'' C hσ_ae, hSdef]
  have hbound : ∫⁻ x : ℝ, ‖F x‖ₑ ^ (2:ℝ) ≤ S ^ 2 * C := by
    calc ∫⁻ x : ℝ, ‖F x‖ₑ ^ (2:ℝ)
        ≤ ∫⁻ x : ℝ, (∫⁻ y : ℝ, ‖σ y‖ₑ * ‖h (x - y)‖ₑ) ^ (2:ℝ) :=
          lintegral_mono (fun x => ENNReal.rpow_le_rpow (hFA x) (by norm_num))
      _ ≤ S * ∫⁻ x : ℝ, (∫⁻ y : ℝ, ‖σ y‖ₑ * ‖h (x - y)‖ₑ ^ (2:ℝ)) := hstep2
      _ = S * (S * C) := by rw [hstep3]
      _ = S ^ 2 * C := by rw [pow_two, mul_assoc]
  -- both factors are finite, hence so is the `L²` seminorm of the convolution
  have hSlt : S < ⊤ := by
    have h := hσ.eLpNorm_lt_top
    rw [eLpNorm_one_eq_lintegral_enorm hσ.aestronglyMeasurable] at h
    simpa [hSdef] using h
  have hClt : C < ⊤ := by
    have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := (2:ℝ≥0∞))
      (by norm_num) (by norm_num) hh.eLpNorm_lt_top
    simpa [hCdef] using h
  have hF2lt : eLpNorm F 2 volume < ⊤ := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2:ℝ≥0∞)) (by norm_num) (by norm_num) hF_meas]
    simp only [ENNReal.toReal_ofNat]
    have hle : (∫⁻ x : ℝ, ‖F x‖ₑ ^ (2:ℝ)) ^ (1/2:ℝ) ≤ (S ^ 2 * C) ^ (1/2:ℝ) :=
      ENNReal.rpow_le_rpow (by simpa [hSdef, hCdef] using hbound) (by norm_num)
    refine lt_of_le_of_lt hle ?_
    rw [ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0:ℝ) < 1/2), pow_two]
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top hSlt hSlt) hClt
  refine ⟨hF2lt, ?_⟩
  simpa [hFdef, hSdef, hCdef] using hbound

end Commons.Analysis.Fourier