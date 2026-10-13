import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.cs_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

open MeasureTheory Set Filter
open scoped Real

set_option maxHeartbeats 1000000

/-- `cos⁶ t ≤ sin(2t)^{2-γ}` on the open right quarter of the slice, for `1 ≤ γ ≤ 3/2`.

`sin(2t) = 2 sin t cos t ≥ cos t` because `sin t ≥ sin (π/4) ≥ 1/2`, and for
`0 < cos t ≤ 1` and `2-γ ≤ 6` the `rpow` is monotone decreasing in the exponent. -/
private lemma sbg_cos_six_le_sigma (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) {t : ℝ}
    (ht : t ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2)) :
    (Real.cos t) ^ 6 ≤ Real.rpow (Real.sin (2 * t)) (2 - γ) := by
  have ht1 : Real.pi / 4 < t := ht.1
  have ht2 : t < Real.pi / 2 := ht.2
  have hcpos : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ht2⟩
  have hc1 : Real.cos t ≤ 1 := Real.cos_le_one t
  have hsint : (1 : ℝ) / 2 ≤ Real.sin t := by
    have h1 : Real.sin (Real.pi / 6) ≤ Real.sin t :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
        (by linarith [ht2]) (by linarith [ht1, Real.pi_pos])
    rw [Real.sin_pi_div_six] at h1
    linarith
  have hsin2 : Real.cos t ≤ Real.sin (2 * t) := by
    rw [Real.sin_two_mul]
    nlinarith [hcpos, hsint]
  calc (Real.cos t) ^ 6 = Real.rpow (Real.cos t) (6 : ℝ) :=
        (Real.rpow_natCast (Real.cos t) 6).symm
    _ ≤ Real.rpow (Real.cos t) (2 - γ) :=
        Real.rpow_le_rpow_of_exponent_ge hcpos hc1 (by linarith)
    _ ≤ Real.rpow (Real.sin (2 * t)) (2 - γ) :=
        Real.rpow_le_rpow hcpos.le hsin2 (by linarith)

/-- The pointwise AM–GM (Young) inequality behind the integrability of `cos³·|g'|`:
`cos³t·|g' t| ≤ ½ (g' t)²σ + ½ cos⁶t/σ` whenever `σ = sin(2t)^{2-γ} > 0`.

Put `a = √σ·|g' t|` and `b = cos³t/√σ`; then `a·b = cos³t·|g' t|` (commutativity of `ℝ`
handles `cos t < 0`), `a² = (g' t)²σ`, `b² = cos⁶t/σ`, and `2ab ≤ a²+b²`. -/
private lemma sbg_amgm (γ : ℝ) {g : ℝ → ℝ} {t : ℝ}
    (hσ : 0 < Real.rpow (Real.sin (2 * t)) (2 - γ)) :
    (Real.cos t) ^ 3 * |deriv g t|
      ≤ (1 / 2) * ((deriv g t) ^ 2 * Real.rpow (Real.sin (2 * t)) (2 - γ))
        + (1 / 2) * ((Real.cos t) ^ 6 / Real.rpow (Real.sin (2 * t)) (2 - γ)) := by
  set a : ℝ := Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)) * |deriv g t| with ha
  set b : ℝ := (Real.cos t) ^ 3 / Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)) with hb
  have hs : Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hσ)
  have hsq : (Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ))) ^ 2
      = Real.rpow (Real.sin (2 * t)) (2 - γ) := Real.sq_sqrt hσ.le
  have hab : a * b = (Real.cos t) ^ 3 * |deriv g t| := by
    rw [ha, hb]; field_simp
  have ha2 : a ^ 2 = (deriv g t) ^ 2 * Real.rpow (Real.sin (2 * t)) (2 - γ) := by
    rw [ha, mul_pow, hsq, sq_abs]; ring
  have hb2 : b ^ 2 = (Real.cos t) ^ 6 / Real.rpow (Real.sin (2 * t)) (2 - γ) := by
    rw [hb, div_pow, hsq]; ring
  have h2ab : 2 * (a * b) ≤ a ^ 2 + b ^ 2 := by nlinarith [sq_nonneg (a - b)]
  rw [hab, ha2, hb2] at h2ab
  linarith

/-- Weighted Cauchy–Schwarz on the right half of the slice: the `g'`-part of the tail.

For `ν ∈ [π/4, π/2)`, `deriv g` a.e.-strongly-measurable and `(g')²σ` integrable on `(ν, π/2)`
(`σ = sin(2t)^{2-γ}`, `1 ≤ γ ≤ 3/2`), the function `cos³|g'|` is integrable there and

  `∫_{Ioo ν (π/2)} cos³t · |g' t| ≤ √(Cw · ∫_{Ioo ν (π/2)} (g')²σ) · (π/2-ν)^{(5+γ)/2}`

whenever `∫_{Ioo ν (π/2)} cos⁶/σ ≤ Cw (π/2-ν)^{5+γ}`.

Proof: write `cos³|g'| = (√σ·|g'|)·(cos³/√σ)` (σ > 0 on the open interval) and apply
Cauchy–Schwarz; `∫(√σ g')² = ∫σ(g')²` and `∫(cos³/√σ)² = ∫cos⁶/σ`.  Integrability of
`cos³|g'|` follows from the pointwise AM–GM bound `cos³|g'| ≤ (g')²σ/2 + (cos⁶/σ)/2` together
with the boundedness of `cos⁶/σ` on `[ν, π/2]`.  NOTE: `cos⁶/σ` is *unconditionally* integrable
on `(ν, π/2)` for `ν > 0` — do not try to extract its `MemLp` from `hI6` (a non-integrable
nonneg function has Bochner integral `0` in Mathlib). -/
theorem slice_bd_tail_gprime (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) {g : ℝ → ℝ} {Cw ν : ℝ}
    (hCw : 0 ≤ Cw) (hν : ν ∈ Set.Ico (Real.pi / 4) (Real.pi / 2))
    (hGm : MeasureTheory.AEStronglyMeasurable (deriv g)
      (MeasureTheory.volume.restrict (Set.Ioo ν (Real.pi / 2))))
    (hG : MeasureTheory.IntegrableOn
      (fun t => (deriv g t) ^ 2 * Real.rpow (Real.sin (2 * t)) (2 - γ))
      (Set.Ioo ν (Real.pi / 2)))
    (hI6 : (∫ t in ν..(Real.pi / 2),
        (Real.cos t) ^ 6 / Real.rpow (Real.sin (2 * t)) (2 - γ))
        ≤ Cw * (Real.pi / 2 - ν) ^ (5 + γ)) :
    (MeasureTheory.IntegrableOn (fun t => (Real.cos t) ^ 3 * |deriv g t|)
        (Set.Ioo ν (Real.pi / 2)))
      ∧ (∫ t in Set.Ioo ν (Real.pi / 2), (Real.cos t) ^ 3 * |deriv g t|
          ≤ Real.sqrt (Cw * (∫ t in Set.Ioo ν (Real.pi / 2),
                (deriv g t) ^ 2 * Real.rpow (Real.sin (2 * t)) (2 - γ)))
            * (Real.pi / 2 - ν) ^ ((5 + γ) / 2)) := by
  set I : Set ℝ := Set.Ioo ν (Real.pi / 2) with hIdef
  have hne : ν < Real.pi / 2 := hν.2
  have hν4 : Real.pi / 4 ≤ ν := hν.1
  have hdpos : 0 < Real.pi / 2 - ν := by linarith
  have hmeasI : MeasurableSet I := by rw [hIdef]; exact measurableSet_Ioo
  have hvol : volume I ≠ ⊤ := by
    rw [hIdef, Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  -- hypothesis transport to the abbreviated set `I`
  have hGmI : AEStronglyMeasurable (deriv g) (volume.restrict I) := by
    simpa only [hIdef] using hGm
  have hGI : IntegrableOn
      (fun t => (deriv g t) ^ 2 * Real.rpow (Real.sin (2 * t)) (2 - γ)) I := by
    simpa only [hIdef] using hG
  have hGm_abs : AEStronglyMeasurable (fun t => |deriv g t|) (volume.restrict I) := by
    simpa only [Real.norm_eq_abs] using hGmI.norm
  -- elementary weight facts on `I`
  have hσpos : ∀ t ∈ I, 0 < Real.rpow (Real.sin (2 * t)) (2 - γ) := by
    intro t ht
    rw [hIdef] at ht
    have hsin : 0 < Real.sin (2 * t) := by
      apply Real.sin_pos_of_mem_Ioo
      exact ⟨by linarith [hν4, ht.1, Real.pi_pos], by linarith [ht.2, Real.pi_pos]⟩
    exact Real.rpow_pos_of_pos hsin _
  have hσnn : ∀ t ∈ I, 0 ≤ Real.rpow (Real.sin (2 * t)) (2 - γ) :=
    fun t ht => (hσpos t ht).le
  have hcos_pos : ∀ t ∈ I, 0 < Real.cos t := by
    intro t ht
    rw [hIdef] at ht
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [hν4, ht.1, Real.pi_pos], ht.2⟩
  have hI_sub : ∀ t ∈ I, t ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2) := by
    intro t ht
    rw [hIdef] at ht
    exact ⟨lt_of_le_of_lt hν4 ht.1, ht.2⟩
  have hdiv_le_one : ∀ t ∈ I,
      (Real.cos t) ^ 6 / Real.rpow (Real.sin (2 * t)) (2 - γ) ≤ 1 := by
    intro t ht
    have hpos := hσpos t ht
    have h6 := sbg_cos_six_le_sigma γ hγ1 hγ2 (hI_sub t ht)
    calc (Real.cos t) ^ 6 / Real.rpow (Real.sin (2 * t)) (2 - γ)
        ≤ Real.rpow (Real.sin (2 * t)) (2 - γ) / Real.rpow (Real.sin (2 * t)) (2 - γ) :=
          div_le_div_of_nonneg_right h6 hpos.le
      _ = 1 := div_self hpos.ne'
  -- the Cauchy–Schwarz pair
  have hσcont : Continuous (fun t : ℝ => Real.rpow (Real.sin (2 * t)) (2 - γ)) :=
    (Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 2 - γ)).comp
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))
  set F : ℝ → ℝ :=
    fun t => Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)) * |deriv g t| with hFdef
  set Hc : ℝ → ℝ :=
    fun t => (Real.cos t) ^ 3 / Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)) with hHdef
  have hF_aesm : AEStronglyMeasurable F (volume.restrict I) := by
    rw [hFdef]
    exact ((Real.continuous_sqrt.comp hσcont).aestronglyMeasurable).mul hGm_abs
  have hHc_aesm : AEStronglyMeasurable Hc (volume.restrict I) := by
    rw [hHdef]
    simp only [div_eq_mul_inv]
    exact (((Real.continuous_cos.pow 3).measurable).mul
      (((Real.continuous_sqrt.comp hσcont).measurable).inv)).aestronglyMeasurable
  -- pointwise identities on `I`
  have hF2 : ∀ t ∈ I, F t ^ 2
      = (deriv g t) ^ 2 * Real.rpow (Real.sin (2 * t)) (2 - γ) := by
    intro t ht
    have h := hσnn t ht
    simp only [hFdef]
    rw [mul_pow, Real.sq_sqrt h, sq_abs]
    ring
  have hH2 : ∀ t ∈ I, Hc t ^ 2
      = (Real.cos t) ^ 6 / Real.rpow (Real.sin (2 * t)) (2 - γ) := by
    intro t ht
    have h := hσnn t ht
    simp only [hHdef]
    rw [div_pow, Real.sq_sqrt h]
    ring
  have hFH : ∀ t ∈ I, F t * Hc t = (Real.cos t) ^ 3 * |deriv g t| := by
    intro t ht
    have hs : Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (hσpos t ht))
    simp only [hFdef, hHdef]
    field_simp
  -- integrability of the two Cauchy–Schwarz factors
  have hH2i : Integrable
      (fun t => (Real.cos t) ^ 6 / Real.rpow (Real.sin (2 * t)) (2 - γ))
      (volume.restrict I) := by
    have hconst : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict I) :=
      integrableOn_const (s := I) (μ := volume) hvol
    refine Integrable.mono' hconst ?_ ?_
    · simp only [div_eq_mul_inv]
      exact (((Real.continuous_cos.pow 6).measurable).mul
        (hσcont.measurable.inv)).aestronglyMeasurable
    · filter_upwards [self_mem_ae_restrict hmeasI] with t ht
      have hnn : 0 ≤ (Real.cos t) ^ 6 / Real.rpow (Real.sin (2 * t)) (2 - γ) :=
        div_nonneg (pow_nonneg (hcos_pos t ht).le 6) (hσnn t ht)
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact hdiv_le_one t ht
  have hF2i : Integrable (fun t => F t ^ 2) (volume.restrict I) :=
    hGI.congr (by
      filter_upwards [self_mem_ae_restrict hmeasI] with t ht
      exact (hF2 t ht).symm)
  have hH2i' : Integrable (fun t => Hc t ^ 2) (volume.restrict I) :=
    hH2i.congr (by
      filter_upwards [self_mem_ae_restrict hmeasI] with t ht
      exact (hH2 t ht).symm)
  -- Cauchy–Schwarz
  have hFmem : MemLp F 2 (volume.restrict I) :=
    (memLp_two_iff_integrable_sq hF_aesm).mpr hF2i
  have hHmem : MemLp Hc 2 (volume.restrict I) :=
    (memLp_two_iff_integrable_sq hHc_aesm).mpr hH2i'
  have hcs := Work.Spaces.cs_integral (s := I) hFmem hHmem
  have hW : (∫ x in I, F x * Hc x) = ∫ x in I, (Real.cos x) ^ 3 * |deriv g x| :=
    setIntegral_congr_fun hmeasI (fun t ht => hFH t ht)
  have hX : (∫ x in I, F x ^ 2)
      = ∫ x in I, (deriv g x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 - γ) :=
    setIntegral_congr_fun hmeasI (fun t ht => hF2 t ht)
  have hY : (∫ x in I, Hc x ^ 2)
      = ∫ x in I, (Real.cos x) ^ 6 / Real.rpow (Real.sin (2 * x)) (2 - γ) :=
    setIntegral_congr_fun hmeasI (fun t ht => hH2 t ht)
  -- the bound on the second factor coming from `hI6`
  have hI6I : (∫ t in I, (Real.cos t) ^ 6 / Real.rpow (Real.sin (2 * t)) (2 - γ))
      ≤ Cw * (Real.pi / 2 - ν) ^ (5 + γ) := by
    have h1 : (∫ t in ν..(Real.pi / 2),
          (Real.cos t) ^ 6 / Real.rpow (Real.sin (2 * t)) (2 - γ))
        = ∫ t in I, (Real.cos t) ^ 6 / Real.rpow (Real.sin (2 * t)) (2 - γ) := by
      rw [intervalIntegral.integral_of_le hne.le, MeasureTheory.integral_Ioc_eq_integral_Ioo,
        ← hIdef]
    rw [h1] at hI6
    exact hI6
  have hX0 : 0 ≤ ∫ x in I, (deriv g x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 - γ) :=
    setIntegral_nonneg hmeasI (fun t ht => mul_nonneg (sq_nonneg _) (hσnn t ht))
  have hW0 : 0 ≤ ∫ x in I, (Real.cos x) ^ 3 * |deriv g x| :=
    setIntegral_nonneg hmeasI
      (fun t ht => mul_nonneg (pow_nonneg (hcos_pos t ht).le 3) (abs_nonneg _))
  -- the squared Cauchy–Schwarz bound
  have hstep : (∫ x in I, (Real.cos x) ^ 3 * |deriv g x|) ^ 2
      ≤ (∫ x in I, (deriv g x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 - γ))
        * (Cw * (Real.pi / 2 - ν) ^ (5 + γ)) := by
    calc (∫ x in I, (Real.cos x) ^ 3 * |deriv g x|) ^ 2
        = (∫ x in I, F x * Hc x) ^ 2 := by rw [hW]
      _ ≤ (∫ x in I, F x ^ 2) * (∫ x in I, Hc x ^ 2) := hcs
      _ = (∫ x in I, (deriv g x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 - γ))
            * (∫ x in I, (Real.cos x) ^ 6 / Real.rpow (Real.sin (2 * x)) (2 - γ)) := by
          rw [hX, hY]
      _ ≤ (∫ x in I, (deriv g x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 - γ))
            * (Cw * (Real.pi / 2 - ν) ^ (5 + γ)) :=
          mul_le_mul_of_nonneg_left hI6I hX0
  -- the two conclusions
  have hsqrt_rpow : Real.sqrt ((Real.pi / 2 - ν) ^ (5 + γ))
      = (Real.pi / 2 - ν) ^ ((5 + γ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (hx := hdpos.le) (y := 5 + γ) (z := 1 / 2)]
    congr 1
    ring
  have hmain : (∫ x in I, (Real.cos x) ^ 3 * |deriv g x|)
      ≤ Real.sqrt (Cw * (∫ x in I, (deriv g x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 - γ)))
        * (Real.pi / 2 - ν) ^ ((5 + γ) / 2) := by
    calc (∫ x in I, (Real.cos x) ^ 3 * |deriv g x|)
        = Real.sqrt ((∫ x in I, (Real.cos x) ^ 3 * |deriv g x|) ^ 2) :=
          (Real.sqrt_sq hW0).symm
      _ ≤ Real.sqrt ((∫ x in I, (deriv g x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 - γ))
            * (Cw * (Real.pi / 2 - ν) ^ (5 + γ))) := Real.sqrt_le_sqrt hstep
      _ = Real.sqrt (Cw * (∫ x in I, (deriv g x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 - γ)))
            * (Real.pi / 2 - ν) ^ ((5 + γ) / 2) := by
          have e1 : Real.sqrt ((∫ x in I, (deriv g x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 - γ))
                * (Cw * (Real.pi / 2 - ν) ^ (5 + γ)))
              = Real.sqrt (∫ x in I, (deriv g x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 - γ))
                * Real.sqrt (Cw * (Real.pi / 2 - ν) ^ (5 + γ)) :=
            Real.sqrt_mul hX0 _
          have e2 : Real.sqrt (Cw * (Real.pi / 2 - ν) ^ (5 + γ))
              = Real.sqrt Cw * Real.sqrt ((Real.pi / 2 - ν) ^ (5 + γ)) :=
            Real.sqrt_mul hCw _
          have e3 : Real.sqrt (Cw * (∫ x in I, (deriv g x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 - γ)))
              = Real.sqrt Cw * Real.sqrt (∫ x in I, (deriv g x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 - γ)) :=
            Real.sqrt_mul hCw _
          rw [e1, e2, e3, hsqrt_rpow]
          ring
  have hint : IntegrableOn (fun t => (Real.cos t) ^ 3 * |deriv g t|) I := by
    have hdom : Integrable
        (fun t => (1 / 2) * ((deriv g t) ^ 2 * Real.rpow (Real.sin (2 * t)) (2 - γ))
          + (1 / 2) * ((Real.cos t) ^ 6 / Real.rpow (Real.sin (2 * t)) (2 - γ)))
        (volume.restrict I) :=
      (hGI.const_mul (1 / 2)).add (hH2i.const_mul (1 / 2))
    refine Integrable.mono' hdom ?_ ?_
    · exact ((Real.continuous_cos.pow 3).aestronglyMeasurable).mul hGm_abs
    · filter_upwards [self_mem_ae_restrict hmeasI] with t ht
      have hnn : 0 ≤ (Real.cos t) ^ 3 * |deriv g t| :=
        mul_nonneg (pow_nonneg (hcos_pos t ht).le 3) (abs_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact sbg_amgm γ (hσpos t ht)
  refine ⟨?_, ?_⟩
  · simpa only [hIdef] using hint
  · simpa only [hIdef] using hmain

end Work.FTS.EllipticEst.remov
