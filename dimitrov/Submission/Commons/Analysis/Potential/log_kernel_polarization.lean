import Mathlib
import Submission.Commons.Analysis.Potential.gauss_kernel_cs
import Submission.Commons.Analysis.Potential.log_div_eq_integral_exp

namespace Commons.Analysis.Potential

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The Gaussian "cross energy" of a measure `ρ` on `ℂ × ℂ` at scale `t` and outer radius `R`:
`∫∫ exp (-(t/R²)‖x-y‖²)`. -/
def gaussE (ρ : Measure (ℂ × ℂ)) (R t : ℝ) : ENNReal :=
  ∫⁻ z, ENNReal.ofReal (Real.exp (-(t / R ^ 2) * ‖z.1 - z.2‖ ^ 2)) ∂ρ

/-- The "difference energy" of a measure `ρ` on `ℂ × ℂ`:
`∫∫ (exp (-(t/R²)‖x-y‖²) - exp (-t))`. -/
def diffE (ρ : Measure (ℂ × ℂ)) (R t : ℝ) : ENNReal :=
  ∫⁻ z, ENNReal.ofReal (Real.exp (-(t * ‖z.1 - z.2‖ ^ 2 / R ^ 2)) - Real.exp (-t)) ∂ρ

/-- Pointwise: for `x ≠ 0` with `‖x‖ ≤ R`, `ofReal (2 log (R/‖x‖))` equals the Lebesgue
integral (over `(0,∞)`) of `ofReal (t⁻¹ (e^{-t‖x‖²/R²} - e^{-t}))`. -/
lemma ofReal_two_log_eq {R : ℝ} (hR : 0 < R) {x : ℂ} (hx : x ≠ 0) (hxR : ‖x‖ ≤ R) :
    ENNReal.ofReal (2 * Real.log (R / ‖x‖)) =
      ∫⁻ t in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (t⁻¹ * (Real.exp (-(t * ‖x‖ ^ 2 / R ^ 2)) - Real.exp (-t))) := by
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  rw [log_div_eq_integral_exp R hR hx]
  refine MeasureTheory.ofReal_integral_eq_lintegral_ofReal ?_ ?_
  · have ha : 0 < ‖x‖ ^ 2 / R ^ 2 := by positivity
    have h := integrableOn_inv_mul_exp_neg_sub_exp_neg (a := ‖x‖ ^ 2 / R ^ 2) (b := 1) ha one_pos
    refine h.congr ?_
    filter_upwards with t
    have e1 : -(t * ‖x‖ ^ 2 / R ^ 2) = -((‖x‖ ^ 2 / R ^ 2) * t) := by ring
    have e2 : (-t : ℝ) = -(1 * t) := by ring
    rw [e1, e2]
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have htpos : 0 < t := ht
    have hle : t * ‖x‖ ^ 2 / R ^ 2 ≤ t := by
      have h2 : ‖x‖ ^ 2 ≤ R ^ 2 := by nlinarith [hxR, norm_nonneg x, hR]
      have h1 : ‖x‖ ^ 2 / R ^ 2 ≤ 1 := by
        rw [div_le_one (by positivity)]; exact h2
      have hmul := mul_le_mul_of_nonneg_left h1 htpos.le
      rw [mul_one] at hmul
      calc t * ‖x‖ ^ 2 / R ^ 2 = t * (‖x‖ ^ 2 / R ^ 2) := by ring
        _ ≤ t := hmul
    have hexp : Real.exp (-t) ≤ Real.exp (-(t * ‖x‖ ^ 2 / R ^ 2)) :=
      Real.exp_le_exp.mpr (by linarith [hle])
    have hnn : 0 ≤ Real.exp (-(t * ‖x‖ ^ 2 / R ^ 2)) - Real.exp (-t) := by linarith
    positivity

/-- Pull the constant `t⁻¹` out of the `lintegral` against `ρ` (for `t > 0`). -/
lemma lintegral_ofReal_mul_sub (ρ : Measure (ℂ × ℂ)) (R t : ℝ) (ht : 0 < t) :
    (∫⁻ z, ENNReal.ofReal
        (t⁻¹ * (Real.exp (-(t * ‖z.1 - z.2‖ ^ 2 / R ^ 2)) - Real.exp (-t))) ∂ρ)
      = ENNReal.ofReal t⁻¹ *
          (∫⁻ z, ENNReal.ofReal
            (Real.exp (-(t * ‖z.1 - z.2‖ ^ 2 / R ^ 2)) - Real.exp (-t)) ∂ρ) := by
  simp_rw [ENNReal.ofReal_mul (inv_nonneg.mpr ht.le)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- Frullani/Laplace representation, integrated: the whole `2 log` energy of a measure `ρ`
on `ℂ × ℂ` (with a.e. bounded diameter and no diagonal mass) is the `(0,∞)`-integral of `t⁻¹`
times the difference energy. -/
lemma log_kernel_eq_integral_gauss (R : ℝ) (hR : 0 < R) (ρ : Measure (ℂ × ℂ)) [SFinite ρ]
    (hdiam : ∀ᵐ z ∂ρ, ‖z.1 - z.2‖ ≤ R) (hne : ∀ᵐ z ∂ρ, z.1 ≠ z.2) :
    2 * (∫⁻ z, ENNReal.ofReal (Real.log (R / ‖z.1 - z.2‖)) ∂ρ)
      = ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal t⁻¹ * diffE ρ R t := by
  change 2 * (∫⁻ z, ENNReal.ofReal (Real.log (R / ‖z.1 - z.2‖)) ∂ρ)
      = ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal t⁻¹ *
          (∫⁻ z, ENNReal.ofReal
            (Real.exp (-(t * ‖z.1 - z.2‖ ^ 2 / R ^ 2)) - Real.exp (-t)) ∂ρ)
  have hnn : ∀ᵐ z ∂ρ, 0 ≤ Real.log (R / ‖z.1 - z.2‖) := by
    filter_upwards [hdiam] with z hz
    rcases eq_or_lt_of_le (norm_nonneg (z.1 - z.2)) with h0 | hpos
    · rw [← h0, div_zero, Real.log_zero]
    · exact Real.log_nonneg ((one_le_div hpos).mpr hz)
  have hA' : (∫⁻ z, (2 : ENNReal) * ENNReal.ofReal (Real.log (R / ‖z.1 - z.2‖)) ∂ρ)
      = 2 * (∫⁻ z, ENNReal.ofReal (Real.log (R / ‖z.1 - z.2‖)) ∂ρ) :=
    lintegral_const_mul' 2 _ (by norm_num)
  have hA'' : (∫⁻ z, (2 : ENNReal) * ENNReal.ofReal (Real.log (R / ‖z.1 - z.2‖)) ∂ρ)
      = ∫⁻ z, ENNReal.ofReal (2 * Real.log (R / ‖z.1 - z.2‖)) ∂ρ := by
    apply lintegral_congr_ae
    filter_upwards [hnn] with z hz
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  have hA : 2 * (∫⁻ z, ENNReal.ofReal (Real.log (R / ‖z.1 - z.2‖)) ∂ρ)
      = ∫⁻ z, ENNReal.ofReal (2 * Real.log (R / ‖z.1 - z.2‖)) ∂ρ := hA'.symm.trans hA''
  have hB : (∫⁻ z, ENNReal.ofReal (2 * Real.log (R / ‖z.1 - z.2‖)) ∂ρ)
      = ∫⁻ z, (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal
          (t⁻¹ * (Real.exp (-(t * ‖z.1 - z.2‖ ^ 2 / R ^ 2)) - Real.exp (-t)))) ∂ρ := by
    apply lintegral_congr_ae
    filter_upwards [hdiam, hne] with z hzR hzne
    exact ofReal_two_log_eq hR (sub_ne_zero.mpr hzne) hzR
  have hC : (∫⁻ z, (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal
          (t⁻¹ * (Real.exp (-(t * ‖z.1 - z.2‖ ^ 2 / R ^ 2)) - Real.exp (-t)))) ∂ρ)
      = ∫⁻ t in Set.Ioi (0 : ℝ), (∫⁻ z, ENNReal.ofReal
          (t⁻¹ * (Real.exp (-(t * ‖z.1 - z.2‖ ^ 2 / R ^ 2)) - Real.exp (-t))) ∂ρ) ∂volume := by
    refine lintegral_lintegral_swap ?_
    fun_prop
  have hD : (∫⁻ t in Set.Ioi (0 : ℝ), (∫⁻ z, ENNReal.ofReal
          (t⁻¹ * (Real.exp (-(t * ‖z.1 - z.2‖ ^ 2 / R ^ 2)) - Real.exp (-t))) ∂ρ) ∂volume)
      = ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal t⁻¹ *
            (∫⁻ z, ENNReal.ofReal
              (Real.exp (-(t * ‖z.1 - z.2‖ ^ 2 / R ^ 2)) - Real.exp (-t)) ∂ρ) ∂volume := by
    apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact lintegral_ofReal_mul_sub ρ R t ht
  rw [hA, hB, hC, hD]

/-- The difference energy splits as the Gaussian cross energy minus the constant `exp (-t)`
(when `ρ` is a probability measure with a.e. bounded diameter). -/
lemma diffE_eq (ρ : Measure (ℂ × ℂ)) (hρ : ρ Set.univ = 1) {R t : ℝ} (hR : 0 < R) (ht : 0 < t)
    (hdiam : ∀ᵐ z ∂ρ, ‖z.1 - z.2‖ ≤ R) :
    diffE ρ R t = gaussE ρ R t - ENNReal.ofReal (Real.exp (-t)) := by
  change (∫⁻ z, ENNReal.ofReal (Real.exp (-(t * ‖z.1 - z.2‖ ^ 2 / R ^ 2)) - Real.exp (-t)) ∂ρ)
      = (∫⁻ z, ENNReal.ofReal (Real.exp (-(t / R ^ 2) * ‖z.1 - z.2‖ ^ 2)) ∂ρ)
          - ENNReal.ofReal (Real.exp (-t))
  have hpt : ∀ᵐ z ∂ρ, ENNReal.ofReal (Real.exp (-(t * ‖z.1 - z.2‖ ^ 2 / R ^ 2)) - Real.exp (-t))
      = ENNReal.ofReal (Real.exp (-(t / R ^ 2) * ‖z.1 - z.2‖ ^ 2)) - ENNReal.ofReal (Real.exp (-t)) := by
    filter_upwards [hdiam] with z hz
    rw [ENNReal.ofReal_sub _ (Real.exp_pos _).le]
    congr 1
    congr 1
    ring_nf
  rw [lintegral_congr_ae hpt]
  have hR2 : (0 : ℝ) < R ^ 2 := pow_pos hR 2
  have hle : (fun _ : ℂ × ℂ => ENNReal.ofReal (Real.exp (-t))) ≤ᵐ[ρ]
      (fun z : ℂ × ℂ => ENNReal.ofReal (Real.exp (-(t / R ^ 2) * ‖z.1 - z.2‖ ^ 2))) := by
    filter_upwards [hdiam] with z hz
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hz2 : ‖z.1 - z.2‖ ^ 2 ≤ R ^ 2 := by
      nlinarith [hz, norm_nonneg (z.1 - z.2), hR2]
    have hle2 : (t / R ^ 2) * ‖z.1 - z.2‖ ^ 2 ≤ t := by
      calc (t / R ^ 2) * ‖z.1 - z.2‖ ^ 2 ≤ (t / R ^ 2) * R ^ 2 :=
            mul_le_mul_of_nonneg_left hz2 (by positivity)
        _ = t := by rw [div_mul_cancel₀ t (ne_of_gt hR2)]
    linarith
  have hg_fin : (∫⁻ z, ENNReal.ofReal (Real.exp (-t)) ∂ρ) ≠ ∞ := by
    rw [lintegral_const, hρ, mul_one]; exact ENNReal.ofReal_ne_top
  rw [MeasureTheory.lintegral_sub measurable_const hg_fin hle]
  congr 1
  rw [lintegral_const, hρ, mul_one]

/-- Pure `ℝ≥0∞` arithmetic: from `2C ≤ X + Y` deduce `2(C - c) ≤ (X - c) + (Y - c)`. -/
lemma two_tsub_le (X Y C c : ENNReal) (hc : c ≠ ∞) (h : 2 * C ≤ X + Y) :
    2 * (C - c) ≤ (X - c) + (Y - c) := by
  rw [ENNReal.mul_sub (a := 2) (b := C) (c := c) (fun _ _ => by norm_num)]
  have h1 : 2 * C - 2 * c ≤ (X + Y) - 2 * c := tsub_le_tsub_right h (2 * c)
  refine le_trans h1 ?_
  have hX : X ≤ (X - c) + c := by
    have := le_add_tsub (a := X) (b := c); rwa [add_comm] at this
  have hY : Y ≤ (Y - c) + c := by
    have := le_add_tsub (a := Y) (b := c); rwa [add_comm] at this
  have hsum : X + Y ≤ (X - c) + (Y - c) + 2 * c := by
    calc X + Y ≤ ((X - c) + c) + ((Y - c) + c) := add_le_add hX hY
      _ = (X - c) + (Y - c) + 2 * c := by ring
  calc (X + Y) - 2 * c ≤ ((X - c) + (Y - c) + 2 * c) - 2 * c :=
        tsub_le_tsub_right hsum (2 * c)
    _ = (X - c) + (Y - c) := by
        rw [ENNReal.add_sub_cancel_right (ENNReal.mul_ne_top (by norm_num) hc)]

/-- Polarization of the difference energy, obtained from `gauss_kernel_cs`. -/
lemma two_diffE_le (μ ν : Measure ℂ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {R t : ℝ} (hR : 0 < R) (ht : 0 < t)
    (hdμμ : ∀ᵐ z ∂(μ.prod μ), ‖z.1 - z.2‖ ≤ R)
    (hdνν : ∀ᵐ z ∂(ν.prod ν), ‖z.1 - z.2‖ ≤ R)
    (hdμν : ∀ᵐ z ∂(μ.prod ν), ‖z.1 - z.2‖ ≤ R) :
    2 * diffE (μ.prod ν) R t ≤ diffE (μ.prod μ) R t + diffE (ν.prod ν) R t := by
  have hμν1 : (μ.prod ν) Set.univ = 1 := by
    rw [← Set.univ_prod_univ, Measure.prod_prod]; simp [measure_univ]
  have hμμ1 : (μ.prod μ) Set.univ = 1 := by
    rw [← Set.univ_prod_univ, Measure.prod_prod]; simp [measure_univ]
  have hνν1 : (ν.prod ν) Set.univ = 1 := by
    rw [← Set.univ_prod_univ, Measure.prod_prod]; simp [measure_univ]
  rw [diffE_eq (μ.prod ν) hμν1 hR ht hdμν,
      diffE_eq (μ.prod μ) hμμ1 hR ht hdμμ,
      diffE_eq (ν.prod ν) hνν1 hR ht hdνν]
  exact two_tsub_le _ _ _ _ ENNReal.ofReal_ne_top (gauss_kernel_cs μ ν (by positivity))

theorem log_kernel_polarization (μ ν : MeasureTheory.Measure ℂ) [MeasureTheory.IsProbabilityMeasure μ] [MeasureTheory.IsProbabilityMeasure ν] [MeasureTheory.NullSingletonClass μ] [MeasureTheory.NullSingletonClass ν] {R : ℝ} (hR : 0 < R) (hμ : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, ‖x - y‖ ≤ R) (hν : ∀ᵐ x ∂ν, ∀ᵐ y ∂ν, ‖x - y‖ ≤ R) (hμν : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, ‖x - y‖ ≤ R) :
    2 * MeasureTheory.lintegral (μ.prod ν) (fun z : ℂ × ℂ => ENNReal.ofReal (Real.log (R / ‖z.1 - z.2‖))) ≤ MeasureTheory.lintegral (μ.prod μ) (fun z : ℂ × ℂ => ENNReal.ofReal (Real.log (R / ‖z.1 - z.2‖))) + MeasureTheory.lintegral (ν.prod ν) (fun z : ℂ × ℂ => ENNReal.ofReal (Real.log (R / ‖z.1 - z.2‖))) := by
  have hf : Measurable (fun z : ℂ × ℂ => ‖z.1 - z.2‖) := by fun_prop
  have hp : MeasurableSet {z : ℂ × ℂ | ‖z.1 - z.2‖ ≤ R} := measurableSet_Iic.preimage hf
  have hdμν : ∀ᵐ z ∂(μ.prod ν), ‖z.1 - z.2‖ ≤ R :=
    (Measure.ae_prod_iff_ae_ae (p := fun z : ℂ × ℂ => ‖z.1 - z.2‖ ≤ R) hp).mpr hμν
  have hdμμ : ∀ᵐ z ∂(μ.prod μ), ‖z.1 - z.2‖ ≤ R :=
    (Measure.ae_prod_iff_ae_ae (p := fun z : ℂ × ℂ => ‖z.1 - z.2‖ ≤ R) hp).mpr hμ
  have hdνν : ∀ᵐ z ∂(ν.prod ν), ‖z.1 - z.2‖ ≤ R :=
    (Measure.ae_prod_iff_ae_ae (p := fun z : ℂ × ℂ => ‖z.1 - z.2‖ ≤ R) hp).mpr hν
  have hdiag : MeasurableSet {z : ℂ × ℂ | z.1 = z.2} :=
    (isClosed_eq continuous_fst continuous_snd).measurableSet
  have hpne : MeasurableSet {z : ℂ × ℂ | z.1 ≠ z.2} := hdiag.compl
  have hne_aeν : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, x ≠ y := by
    apply ae_of_all
    intro x
    rw [ae_iff]
    have hset : {y : ℂ | ¬(x ≠ y)} = {x} := by
      ext y
      simp only [Set.mem_ofPred_eq, not_not, Set.mem_singleton_iff]
      exact eq_comm
    rw [hset]
    exact measure_singleton x
  have hne_aeμ : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, x ≠ y := by
    apply ae_of_all
    intro x
    rw [ae_iff]
    have hset : {y : ℂ | ¬(x ≠ y)} = {x} := by
      ext y
      simp only [Set.mem_ofPred_eq, not_not, Set.mem_singleton_iff]
      exact eq_comm
    rw [hset]
    exact measure_singleton x
  have hne_aeν' : ∀ᵐ x ∂ν, ∀ᵐ y ∂ν, x ≠ y := by
    apply ae_of_all
    intro x
    rw [ae_iff]
    have hset : {y : ℂ | ¬(x ≠ y)} = {x} := by
      ext y
      simp only [Set.mem_ofPred_eq, not_not, Set.mem_singleton_iff]
      exact eq_comm
    rw [hset]
    exact measure_singleton x
  have hneμν : ∀ᵐ z ∂(μ.prod ν), z.1 ≠ z.2 :=
    (Measure.ae_prod_iff_ae_ae (p := fun z : ℂ × ℂ => z.1 ≠ z.2) hpne).mpr hne_aeν
  have hneμμ : ∀ᵐ z ∂(μ.prod μ), z.1 ≠ z.2 :=
    (Measure.ae_prod_iff_ae_ae (p := fun z : ℂ × ℂ => z.1 ≠ z.2) hpne).mpr hne_aeμ
  have hneνν : ∀ᵐ z ∂(ν.prod ν), z.1 ≠ z.2 :=
    (Measure.ae_prod_iff_ae_ae (p := fun z : ℂ × ℂ => z.1 ≠ z.2) hpne).mpr hne_aeν'
  have hLμν := log_kernel_eq_integral_gauss R hR (μ.prod ν) hdμν hneμν
  have hLμμ := log_kernel_eq_integral_gauss R hR (μ.prod μ) hdμμ hneμμ
  have hLνν := log_kernel_eq_integral_gauss R hR (ν.prod ν) hdνν hneνν
  have hmeas : ∀ (ρ : Measure (ℂ × ℂ)) [SFinite ρ], Measurable (fun t : ℝ => ENNReal.ofReal t⁻¹ * diffE ρ R t) := by
    intro ρ _
    refine Measurable.mul (ENNReal.measurable_ofReal.comp measurable_inv) ?_
    change Measurable (fun t : ℝ => ∫⁻ z, ENNReal.ofReal
      (Real.exp (-(t * ‖z.1 - z.2‖ ^ 2 / R ^ 2)) - Real.exp (-t)) ∂ρ)
    exact Measurable.lintegral_prod_right (by fun_prop)
  have key : 2 * (2 * (∫⁻ z, ENNReal.ofReal (Real.log (R / ‖z.1 - z.2‖)) ∂(μ.prod ν)))
      ≤ 2 * ((∫⁻ z, ENNReal.ofReal (Real.log (R / ‖z.1 - z.2‖)) ∂(μ.prod μ))
          + (∫⁻ z, ENNReal.ofReal (Real.log (R / ‖z.1 - z.2‖)) ∂(ν.prod ν))) := by
    rw [mul_add, hLμν, hLμμ, hLνν]
    have h2 : 2 * (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal t⁻¹ * diffE (μ.prod ν) R t)
        = ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal t⁻¹ * (2 * diffE (μ.prod ν) R t) := by
      rw [← lintegral_const_mul' 2 (fun t => ENNReal.ofReal t⁻¹ * diffE (μ.prod ν) R t) (by norm_num)]
      apply lintegral_congr; intro t; ring
    rw [h2]
    have hBC : (∫⁻ t in Set.Ioi (0 : ℝ),
          ENNReal.ofReal t⁻¹ * (diffE (μ.prod μ) R t + diffE (ν.prod ν) R t))
        = (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal t⁻¹ * diffE (μ.prod μ) R t)
          + (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal t⁻¹ * diffE (ν.prod ν) R t) := by
      simp_rw [mul_add]
      rw [lintegral_add_left (hmeas (μ.prod μ))]
    rw [← hBC]
    apply lintegral_mono_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact mul_le_mul_right (two_diffE_le μ ν hR ht hdμμ hdνν hdμν) _
  exact (ENNReal.mul_le_mul_iff_right (by norm_num : (2 : ENNReal) ≠ 0)
    (by norm_num : (2 : ENNReal) ≠ ∞)).mp key

end

end Commons.Analysis.Potential
