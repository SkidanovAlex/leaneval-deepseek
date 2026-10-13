import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.cs_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.FTS.EllipticEst.remov

open MeasureTheory Set

/-! ## Elementary angular facts on `Iθ = [0,π/2]` -/

/-- `θ ↦ sin(2θ)^a` is a.e. strongly measurable on `Iθ`, for *every* real exponent `a`
(the instance `MeasurablePow ℝ ℝ` supplies measurability of `rpow` in the base). -/
private lemma aesm_sin_two_rpow (a : ℝ) :
    AEStronglyMeasurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ a)
      (volume.restrict Work.Spaces.Iθ) :=
  ((Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const a).aestronglyMeasurable

/-- `sin(2θ) ≥ 0` on `Iθ`. -/
private lemma sin_two_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) := by
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])

/-- A vanishing `sin(2θ)` kills any non-zero power of it. -/
private lemma sin_two_rpow_eq_zero {θ a : ℝ} (h : Real.sin (2 * θ) = 0) (ha : a ≠ 0) :
    (Real.sin (2 * θ)) ^ a = 0 := by
  rw [h, Real.zero_rpow ha]

/-- At `sin(2θ) = 0` the angular weight `sinθcos²θ` vanishes as well. -/
private lemma sinCos2_eq_zero_of_sin_two_eq_zero {θ : ℝ} (h : Real.sin (2 * θ) = 0) :
    Work.Elliptic.sinCos2 θ = 0 := by
  have h2 : Real.sin (2 * θ) = 2 * Real.sin θ * Real.cos θ := Real.sin_two_mul θ
  rw [h] at h2
  rcases mul_eq_zero.mp h2.symm with h3 | h3
  · have hs : Real.sin θ = 0 := by linarith
    simp only [Work.Elliptic.sinCos2, hs, zero_mul]
  · simp only [Work.Elliptic.sinCos2, h3]
    ring

/-- `sinθcos²θ ≥ 0` on `Iθ`. -/
private lemma sinCos2_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.Elliptic.sinCos2 θ := by
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  have h1 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have h2 : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hθ.2⟩
  simp only [Work.Elliptic.sinCos2]
  exact mul_nonneg h1 (pow_nonneg h2 2)

/-- `sinθcos²θ ≤ 1` on `Iθ`. -/
private lemma sinCos2_le_one {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Elliptic.sinCos2 θ ≤ 1 := by
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  have h2 : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hθ.2⟩
  have hsq : Real.cos θ ^ 2 ≤ 1 := by nlinarith [Real.cos_le_one θ, h2]
  simp only [Work.Elliptic.sinCos2]
  have h := mul_le_mul (Real.sin_le_one θ) hsq (pow_nonneg h2 2) (by norm_num : (0 : ℝ) ≤ 1)
  simpa using h

/-! ## The slice Cauchy–Schwarz bound -/

/-- **Slice Cauchy–Schwarz for the angular moment `∫_Iθ |f|·sinθcos²θ`.**

With `u = |f|·sin(2θ)^{-η/2}` and `v = sinθcos²θ·sin(2θ)^{η/2}` (both non-negative on `Iθ`),
the product `u·v` equals `|f|·sinθcos²θ` while `u² = f²·sin(2θ)^{-η}` and
`v² = sin²θcos⁴θ·sin(2θ)^η ≤ 1`, whose integral over `Iθ` is at most `π/2 = |Iθ|`.
Cauchy–Schwarz `(∫u v)² ≤ (∫u²)(∫v²)` (Mathlib's `L²` version `Work.Spaces.cs_integral`) then
gives the claim. -/
theorem sliceAbsSinCos2CS {f : ℝ → ℝ}
    (haesm : MeasureTheory.AEStronglyMeasurable f (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (h2 : MeasureTheory.Integrable
      (fun θ : ℝ => f θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    (∫ θ in Work.Spaces.Iθ, |f θ| * Work.Elliptic.sinCos2 θ)
      ≤ Real.sqrt (Real.pi / 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ,
            f θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hη : 0 < Work.Spaces.eta := Work.Spaces.eta_pos
  -- the two Cauchy–Schwarz factors
  set u : ℝ → ℝ := fun θ => |f θ| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)) with hu
  set v : ℝ → ℝ :=
    fun θ => Work.Elliptic.sinCos2 θ * (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hv
  -- ## measurability
  have hfabs : AEStronglyMeasurable (fun θ : ℝ => |f θ|) (volume.restrict Work.Spaces.Iθ) := by
    simpa only [Real.norm_eq_abs] using haesm.norm
  have hu_aesm : AEStronglyMeasurable u (volume.restrict Work.Spaces.Iθ) := by
    rw [hu]
    exact hfabs.mul (aesm_sin_two_rpow _)
  have hsc_cont : Continuous fun θ : ℝ => Work.Elliptic.sinCos2 θ := by
    simp only [Work.Elliptic.sinCos2]
    fun_prop
  have hv_aesm : AEStronglyMeasurable v (volume.restrict Work.Spaces.Iθ) := by
    rw [hv]
    exact hsc_cont.aestronglyMeasurable.mul (aesm_sin_two_rpow _)
  -- ## the pointwise identities
  have hu2_eq : ∀ θ ∈ Work.Spaces.Iθ,
      (u θ) ^ 2 = f θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    intro θ hθ
    rw [hu]
    simp only
    rcases eq_or_lt_of_le (sin_two_nonneg hθ) with hzero' | hpos
    · have hzero : Real.sin (2 * θ) = 0 := hzero'.symm
      have h1 : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)) = 0 :=
        sin_two_rpow_eq_zero hzero (by linarith)
      have h2' : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) = 0 :=
        sin_two_rpow_eq_zero hzero (by linarith)
      rw [h1, h2']
      ring
    · have hpow : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))
          = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
        rw [← Real.rpow_add hpos]
        congr 1
        ring
      calc (|f θ| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) ^ 2
          = |f θ| ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) := by
            rw [mul_pow]; ring
        _ = f θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by rw [sq_abs, hpow]
  have hv2_eq : ∀ θ ∈ Work.Spaces.Iθ,
      (v θ) ^ 2
        = (Work.Elliptic.sinCos2 θ) ^ 2 * (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
    intro θ hθ
    rw [hv]
    simp only
    rcases eq_or_lt_of_le (sin_two_nonneg hθ) with hzero' | hpos
    · have hzero : Real.sin (2 * θ) = 0 := hzero'.symm
      have h1 : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 0 :=
        sin_two_rpow_eq_zero hzero (by linarith)
      have h2' : (Real.sin (2 * θ)) ^ (Work.Spaces.eta) = 0 :=
        sin_two_rpow_eq_zero hzero (by linarith)
      rw [h1, h2']
      ring
    · have hpow : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
            * (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
          = (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
        rw [← Real.rpow_add hpos]
        congr 1
        ring
      calc (Work.Elliptic.sinCos2 θ * (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
          = (Work.Elliptic.sinCos2 θ) ^ 2 * ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
              * (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) := by rw [mul_pow]; ring
        _ = (Work.Elliptic.sinCos2 θ) ^ 2 * (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
            rw [hpow]
  have huv_eq : (∫ θ in Work.Spaces.Iθ, u θ * v θ)
      = ∫ θ in Work.Spaces.Iθ, |f θ| * Work.Elliptic.sinCos2 θ := by
    refine MeasureTheory.setIntegral_congr_fun hIθ (fun θ hθ => ?_)
    rw [hu, hv]
    simp only
    rcases eq_or_lt_of_le (sin_two_nonneg hθ) with hzero' | hpos
    · have hzero : Real.sin (2 * θ) = 0 := hzero'.symm
      have h1 : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)) = 0 :=
        sin_two_rpow_eq_zero hzero (by linarith)
      have h2' : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 0 :=
        sin_two_rpow_eq_zero hzero (by linarith)
      rw [h1, h2', sinCos2_eq_zero_of_sin_two_eq_zero hzero]
      ring
    · have hkey : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))
            * (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 1 := by
        rw [← Real.rpow_add hpos]
        rw [show (-(Work.Spaces.eta / 2) + Work.Spaces.eta / 2) = 0 by ring, Real.rpow_zero]
      calc (|f θ| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)))
              * (Work.Elliptic.sinCos2 θ * (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
          = (|f θ| * Work.Elliptic.sinCos2 θ)
              * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))
                * (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) := by ring
        _ = |f θ| * Work.Elliptic.sinCos2 θ := by rw [hkey, mul_one]
  -- ## integrability of the two factors
  have hu2_int : Integrable (fun θ : ℝ => (u θ) ^ 2) (volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.IntegrableOn.congr_fun h2 (fun θ hθ => (hu2_eq θ hθ).symm) hIθ
  have hsin_cont : Continuous fun θ : ℝ => Real.sin (2 * θ) := by fun_prop
  have hv2_cont : Continuous fun θ : ℝ =>
      (Work.Elliptic.sinCos2 θ) ^ 2 * (Real.sin (2 * θ)) ^ (Work.Spaces.eta) :=
    (hsc_cont.pow 2).mul ((Real.continuous_rpow_const hη.le).comp hsin_cont)
  have hv2_int : Integrable (fun θ : ℝ => (v θ) ^ 2) (volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.IntegrableOn.congr_fun
      (ContinuousOn.integrableOn_compact (K := Work.Spaces.Iθ) isCompact_Icc
        hv2_cont.continuousOn)
      (fun θ hθ => (hv2_eq θ hθ).symm) hIθ
  have hu_memLp : MemLp u 2 (volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hu_aesm).mpr hu2_int
  have hv_memLp : MemLp v 2 (volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hv_aesm).mpr hv2_int
  -- ## Cauchy–Schwarz
  have hcs := Work.Spaces.cs_integral (u := u) (v := v) (s := Work.Spaces.Iθ) hu_memLp hv_memLp
  -- ## the bound on `∫ v²`
  have hv2_le_one : ∀ θ ∈ Work.Spaces.Iθ, (v θ) ^ 2 ≤ 1 := by
    intro θ hθ
    rw [hv2_eq θ hθ]
    have hsin0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg hθ
    have hpow1 : (Real.sin (2 * θ)) ^ (Work.Spaces.eta) ≤ 1 :=
      Real.rpow_le_one hsin0 (Real.sin_le_one _) hη.le
    have hsc2 : (Work.Elliptic.sinCos2 θ) ^ 2 ≤ 1 := by
      nlinarith [sinCos2_nonneg hθ, sinCos2_le_one hθ]
    have h := mul_le_mul hsc2 hpow1 (Real.rpow_nonneg hsin0 _) (by norm_num : (0 : ℝ) ≤ 1)
    simpa using h
  have hone : (∫ θ in Work.Spaces.Iθ, (1 : ℝ)) = Real.pi / 2 := by
    rw [MeasureTheory.setIntegral_const]
    simp only [smul_eq_mul, mul_one, Work.Spaces.Iθ]
    rw [Real.volume_real_Icc_of_le (by positivity)]
    ring
  have hv2_le : (∫ θ in Work.Spaces.Iθ, (v θ) ^ 2) ≤ Real.pi / 2 := by
    have hone_int : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict Work.Spaces.Iθ) :=
      ContinuousOn.integrableOn_compact (K := Work.Spaces.Iθ) isCompact_Icc
        continuous_const.continuousOn
    have hae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), (v θ) ^ 2 ≤ 1 :=
      (MeasureTheory.ae_restrict_iff' hIθ).mpr
        (Filter.Eventually.of_forall fun θ hθ => hv2_le_one θ hθ)
    have h := MeasureTheory.integral_mono_ae hv2_int hone_int hae
    rwa [hone] at h
  -- ## non-negativity of the three integrals
  have hC_nonneg : 0 ≤ ∫ θ in Work.Spaces.Iθ, u θ * v θ :=
    MeasureTheory.setIntegral_nonneg_ae hIθ (Filter.Eventually.of_forall fun θ hθ =>
      mul_nonneg (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (sin_two_nonneg hθ) _))
        (mul_nonneg (sinCos2_nonneg hθ) (Real.rpow_nonneg (sin_two_nonneg hθ) _)))
  have hA : 0 ≤ ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 :=
    MeasureTheory.integral_nonneg fun θ => sq_nonneg _
  have hB : 0 ≤ ∫ θ in Work.Spaces.Iθ, (v θ) ^ 2 :=
    MeasureTheory.integral_nonneg fun θ => sq_nonneg _
  have hu2_int_eq : (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)
      = ∫ θ in Work.Spaces.Iθ, f θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    MeasureTheory.setIntegral_congr_fun hIθ (fun θ hθ => hu2_eq θ hθ)
  have hAB : 0 ≤ (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2) * (∫ θ in Work.Spaces.Iθ, (v θ) ^ 2) :=
    mul_nonneg hA hB
  -- ## assembly
  calc (∫ θ in Work.Spaces.Iθ, |f θ| * Work.Elliptic.sinCos2 θ)
      = ∫ θ in Work.Spaces.Iθ, u θ * v θ := huv_eq.symm
    _ ≤ Real.sqrt ((∫ θ in Work.Spaces.Iθ, (u θ) ^ 2) * (∫ θ in Work.Spaces.Iθ, (v θ) ^ 2)) :=
        (Real.le_sqrt hC_nonneg hAB).mpr hcs
    _ = Real.sqrt (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, (v θ) ^ 2) := Real.sqrt_mul hA _
    _ ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2) * Real.sqrt (Real.pi / 2) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hv2_le) (Real.sqrt_nonneg _)
    _ = Real.sqrt (Real.pi / 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ,
              f θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
        rw [hu2_int_eq]; ring

end Work.FTS.EllipticEst.remov
