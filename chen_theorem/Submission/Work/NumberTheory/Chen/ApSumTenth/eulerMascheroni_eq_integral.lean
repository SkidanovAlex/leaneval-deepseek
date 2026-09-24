import Mathlib
import Submission.Commons.Analysis.SpecialFunctions.eulerIntegral_log_exp_neg

/-!
# The classical integral representation of the Euler--Mascheroni constant

We prove

`γ = ∫_0^1 (1 - e^{-t})/t dt - ∫_1^∞ e^{-t}/t dt`

from the (already available) identity `∫_0^∞ log t · e^{-t} dt = -γ`
(`Commons.Analysis.SpecialFunctions.eulerIntegral_log_exp_neg`) together with two
integrations by parts:

* on `(1, ∞)`: `∫_1^∞ e^{-t}/t dt = ∫_1^∞ log t · e^{-t} dt`;
* on `(0, 1]`: `∫_0^1 (1 - e^{-t})/t dt = -∫_0^1 log t · e^{-t} dt`,

the second obtained as a limit of the integration by parts on `[ε, 1]` as `ε → 0⁺`.
-/

namespace Work.NumberTheory.Chen.ApSumTenth

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

/-- The integrand whose integral on `(0,∞)` equals `-γ`. -/
private def F (t : ℝ) : ℝ := Real.log t * Real.exp (-t)

/-- Integrand of the compact piece in the integral representation of `γ`. -/
private def G0 (t : ℝ) : ℝ := (1 - Real.exp (-t)) / t

/-- Integrand of the tail piece in the integral representation of `γ`. -/
private def G1 (t : ℝ) : ℝ := Real.exp (-t) / t

/-- The sequence `ε n = 1/(n+1) ↓ 0` used to exhaust `(0,1]`. -/
private def eps (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

private lemma eps_pos (n : ℕ) : 0 < eps n := by
  simp only [eps]
  positivity

private lemma eps_le_one (n : ℕ) : eps n ≤ 1 := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  simp only [eps]
  rw [div_le_iff₀ hpos]
  linarith

private lemma eps_antitone : Antitone eps := by
  intro m n hmn
  simp only [eps]
  apply one_div_le_one_div_of_le
  · exact_mod_cast Nat.succ_pos m
  · exact_mod_cast Nat.succ_le_succ hmn

private lemma iUnion_eps_Ioc : (⋃ n, Ioc (eps n) (1 : ℝ)) = Ioc (0 : ℝ) 1 := by
  ext x
  rw [mem_iUnion]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨lt_of_lt_of_le (eps_pos n) hn.1.le, hn.2⟩
  · rintro ⟨hx0, hx1⟩
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / x : ℝ)
    refine ⟨n, ?_, hx1⟩
    simp only [eps]
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    have h1 : 1 / x < (n : ℝ) + 1 := by linarith [hn]
    have h2 : x * (1 / x) < x * ((n : ℝ) + 1) := mul_lt_mul_of_pos_left h1 hx0
    rw [mul_one_div_cancel (ne_of_gt hx0)] at h2
    linarith [h2]

/-- `(1 - e^{-x})/x → 1` as `x → 0⁺`. -/
private lemma tendsto_one_sub_exp_neg_div :
    Tendsto (fun x : ℝ => (1 - Real.exp (-x)) / x) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hg : Tendsto (fun x : ℝ => (Real.exp x - 1) / x) (𝓝[{0}ᶜ] (0 : ℝ)) (𝓝 1) := by
    have h := (Real.hasDerivAt_exp (0 : ℝ)).tendsto_slope
    rw [Real.exp_zero] at h
    convert h using 2
    simp [slope, div_eq_inv_mul]
  have hs : Tendsto (fun x : ℝ => (Real.exp x - 1) / x) (𝓝[>] (0 : ℝ)) (𝓝 1) :=
    hg.mono_left (nhdsWithin_mono 0 (fun x hx => ne_of_gt hx))
  have he : Tendsto (fun x : ℝ => Real.exp (-x)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h : Tendsto (fun x : ℝ => -x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using (continuous_neg.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    have hcomp : Tendsto (fun x : ℝ => Real.exp (-x)) (𝓝[>] (0 : ℝ)) (𝓝 (Real.exp 0)) :=
      (Real.continuous_exp.tendsto 0).comp h
    simpa using hcomp
  have hmul : Tendsto (fun x : ℝ => (Real.exp x - 1) / x * Real.exp (-x))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa using hs.mul he
  refine hmul.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : x ≠ 0 := ne_of_gt hx
  rw [Real.exp_neg]
  field_simp

/-- `(1 - e^{-x}) · log x → 0` as `x → 0⁺`. -/
private lemma tendsto_one_sub_exp_neg_mul_log :
    Tendsto (fun x : ℝ => (1 - Real.exp (-x)) * Real.log x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h1 := tendsto_one_sub_exp_neg_div
  have h2 : Tendsto (fun x : ℝ => x * Real.log x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa [Real.rpow_one, mul_comm] using
      tendsto_log_mul_rpow_nhdsGT_zero (show (0 : ℝ) < 1 by norm_num)
  have h3 : Tendsto (fun x : ℝ => (1 - Real.exp (-x)) / x * (x * Real.log x))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using h1.mul h2
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : x ≠ 0 := ne_of_gt hx
  field_simp

private lemma integrableOn_log_Ioc : IntegrableOn (fun t : ℝ => Real.log t) (Ioc (0 : ℝ) 1) := by
  have h := (intervalIntegrable_iff (f := fun t : ℝ => Real.log t) (a := (0 : ℝ)) (b := 1)
    (μ := volume)).mp intervalIntegral.intervalIntegrable_log'
  rwa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at h

private lemma integrableOn_F_Ioc : IntegrableOn F (Ioc (0 : ℝ) 1) := by
  refine Integrable.mono (μ := volume.restrict (Ioc (0 : ℝ) 1)) (g := fun t : ℝ => Real.log t)
    integrableOn_log_Ioc ?_ ?_
  · change AEStronglyMeasurable (fun t : ℝ => Real.log t * Real.exp (-t))
      (volume.restrict (Ioc (0 : ℝ) 1))
    exact (Real.measurable_log.mul
      (Real.continuous_exp.measurable.comp measurable_neg)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simp only [F]
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 : |Real.exp (-t)| ≤ 1 := by
      rw [abs_of_nonneg (Real.exp_nonneg _), Real.exp_le_one_iff]
      linarith [ht.1]
    calc |Real.log t| * |Real.exp (-t)| ≤ |Real.log t| * 1 :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = |Real.log t| := mul_one _

private lemma integrableOn_F_Ioi : IntegrableOn F (Ioi (1 : ℝ)) := by
  have hbase : IntegrableOn (fun t : ℝ => t * Real.exp (-t)) (Ioi (0 : ℝ)) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := (1 : ℝ)) (b := (1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num)
    simpa [Real.rpow_one, neg_one_mul] using h
  have h1 : IntegrableOn (fun t : ℝ => t * Real.exp (-t)) (Ioi (1 : ℝ)) :=
    hbase.mono_set (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))
  refine Integrable.mono (μ := volume.restrict (Ioi (1 : ℝ)))
    (g := fun t : ℝ => t * Real.exp (-t)) h1 ?_ ?_
  · change AEStronglyMeasurable (fun t : ℝ => Real.log t * Real.exp (-t))
      (volume.restrict (Ioi (1 : ℝ)))
    exact (Real.measurable_log.mul
      (Real.continuous_exp.measurable.comp measurable_neg)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : (1 : ℝ) < t := ht
    have ht0 : (0 : ℝ) ≤ t := le_of_lt (lt_trans one_pos ht1)
    simp only [F]
    simp only [norm_mul, Real.norm_eq_abs]
    have hlog : |Real.log t| ≤ |t| := by
      rw [abs_of_nonneg (Real.log_nonneg (le_of_lt ht1)), abs_of_nonneg ht0]
      exact Real.log_le_self ht0
    exact mul_le_mul_of_nonneg_right hlog (abs_nonneg _)

private lemma integrableOn_G0_Ioc : IntegrableOn G0 (Ioc (0 : ℝ) 1) := by
  refine IntegrableOn.of_bound ?_ ?_ 1 ?_
  · rw [Real.volume_Ioc]; simp
  · change AEStronglyMeasurable (fun t : ℝ => (1 - Real.exp (-t)) / t)
      (volume.restrict (Ioc (0 : ℝ) 1))
    exact (Measurable.div
      (measurable_const.sub (Real.continuous_exp.measurable.comp measurable_neg))
      measurable_id).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simp only [G0]
    rw [Real.norm_eq_abs, abs_div, abs_of_pos ht.1]
    have h1 : 0 ≤ 1 - Real.exp (-t) := by
      have := Real.exp_le_one_iff.mpr (by linarith [ht.1] : -t ≤ 0)
      linarith
    rw [abs_of_nonneg h1, div_le_one ht.1]
    have := Real.one_sub_le_exp_neg t
    linarith

private lemma integrableOn_G1_Ioi : IntegrableOn G1 (Ioi (1 : ℝ)) := by
  have hexp : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi (1 : ℝ)) := by
    have hbase : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi (0 : ℝ)) := by
      have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := (0 : ℝ)) (b := (1 : ℝ))
        (by norm_num) (by norm_num) (by norm_num)
      simpa [Real.rpow_zero, Real.rpow_one, neg_one_mul, one_mul] using h
    exact hbase.mono_set (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))
  refine Integrable.mono (μ := volume.restrict (Ioi (1 : ℝ)))
    (g := fun t : ℝ => Real.exp (-t)) hexp ?_ ?_
  · change AEStronglyMeasurable (fun t : ℝ => Real.exp (-t) / t) (volume.restrict (Ioi (1 : ℝ)))
    exact (Measurable.div (Real.continuous_exp.measurable.comp measurable_neg)
      measurable_id).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [G1]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_div]
    have ht0 : 0 < t := lt_trans one_pos ht
    rw [abs_of_pos ht0, abs_of_nonneg (Real.exp_nonneg _), div_le_iff₀ ht0]
    calc Real.exp (-t) = Real.exp (-t) * 1 := (mul_one _).symm
      _ ≤ Real.exp (-t) * t := mul_le_mul_of_nonneg_left (le_of_lt ht) (Real.exp_nonneg _)

/-- Integration by parts on `[ε n, 1]`, rearranged. -/
private lemma ibp_eps (n : ℕ) :
    ∫ t in (eps n)..1, F t
      = -((1 - Real.exp (-(eps n))) * Real.log (eps n)) - ∫ t in (eps n)..1, G0 t := by
  have hpos : 0 < eps n := eps_pos n
  have hle : eps n ≤ 1 := eps_le_one n
  have hu : ∀ x ∈ uIcc (eps n) 1,
      HasDerivAt (fun t : ℝ => 1 - Real.exp (-t)) (Real.exp (-x)) x := by
    intro x hx
    have h := (hasDerivAt_neg x).exp
    have h2 : HasDerivAt (fun t : ℝ => 1 - Real.exp (-t)) (0 - Real.exp (-x) * (-1)) x :=
      (hasDerivAt_const (x := x) (1 : ℝ)).sub h
    simpa using h2
  have hv : ∀ x ∈ uIcc (eps n) 1, HasDerivAt Real.log x⁻¹ x := by
    intro x hx
    have hx1 : eps n ≤ x := by rw [uIcc_of_le hle] at hx; exact hx.1
    exact Real.hasDerivAt_log (ne_of_gt (lt_of_lt_of_le hpos hx1))
  have hui : IntervalIntegrable (fun t : ℝ => Real.exp (-t)) volume (eps n) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hvi : IntervalIntegrable (fun t : ℝ => t⁻¹) volume (eps n) 1 := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    apply ContinuousAt.continuousWithinAt
    apply continuousAt_inv₀
    rw [uIcc_of_le hle] at ht
    exact ne_of_gt (lt_of_lt_of_le hpos ht.1)
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := eps n) (b := 1)
    (u := fun t : ℝ => 1 - Real.exp (-t)) (u' := fun t : ℝ => Real.exp (-t))
    (v := Real.log) (v' := fun t : ℝ => t⁻¹) hu hv hui hvi
  rw [Real.log_one, mul_zero] at h
  have h1 : ∫ t in (eps n)..1, (1 - Real.exp (-t)) * t⁻¹ = ∫ t in (eps n)..1, G0 t := by
    apply intervalIntegral.integral_congr
    intro t ht
    simp only [G0, div_eq_mul_inv]
  have h2 : ∫ t in (eps n)..1, Real.exp (-t) * Real.log t = ∫ t in (eps n)..1, F t := by
    apply intervalIntegral.integral_congr
    intro t ht
    simp only [F]
    ring
  rw [h1, h2] at h
  linarith [h]

/-- Step 1: the compact piece equals minus the corresponding `log` integral. -/
private lemma integral_Ioc_F :
    ∫ t in Ioc (0 : ℝ) 1, F t = - ∫ t in Ioc (0 : ℝ) 1, G0 t := by
  have hunion_eps : (⋃ n, Ioc (eps n) (1 : ℝ)) = Ioc (0 : ℝ) 1 := iUnion_eps_Ioc
  have hmono : Monotone (fun n => Ioc (eps n) (1 : ℝ)) := by
    intro m n hmn t ht
    exact ⟨lt_of_le_of_lt (eps_antitone hmn) ht.1, ht.2⟩
  have hLF : Tendsto (fun n => ∫ t in (eps n)..1, F t) atTop (𝓝 (∫ t in Ioc (0 : ℝ) 1, F t)) := by
    have hint : IntegrableOn F (⋃ n, Ioc (eps n) (1 : ℝ)) := by
      rw [hunion_eps]; exact integrableOn_F_Ioc
    have h := tendsto_setIntegral_of_monotone (f := F) (s := fun n => Ioc (eps n) (1 : ℝ))
      (fun n => measurableSet_Ioc) hmono hint
    rw [hunion_eps] at h
    refine h.congr' ?_
    filter_upwards with n
    exact (intervalIntegral.integral_of_le (eps_le_one n)).symm
  have hLG : Tendsto (fun n => ∫ t in (eps n)..1, G0 t) atTop (𝓝 (∫ t in Ioc (0 : ℝ) 1, G0 t)) := by
    have hint : IntegrableOn G0 (⋃ n, Ioc (eps n) (1 : ℝ)) := by
      rw [hunion_eps]; exact integrableOn_G0_Ioc
    have h := tendsto_setIntegral_of_monotone (f := G0) (s := fun n => Ioc (eps n) (1 : ℝ))
      (fun n => measurableSet_Ioc) hmono hint
    rw [hunion_eps] at h
    refine h.congr' ?_
    filter_upwards with n
    exact (intervalIntegral.integral_of_le (eps_le_one n)).symm
  have hB : Tendsto (fun n => (1 - Real.exp (-(eps n))) * Real.log (eps n)) atTop (𝓝 0) := by
    have heps : Tendsto eps atTop (𝓝[>] (0 : ℝ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · show Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0)
        exact tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      · exact Eventually.of_forall (fun n => eps_pos n)
    exact tendsto_one_sub_exp_neg_mul_log.comp heps
  have hcomb : Tendsto
      (fun n => -((1 - Real.exp (-(eps n))) * Real.log (eps n)) - ∫ t in (eps n)..1, G0 t)
      atTop (𝓝 (-0 - ∫ t in Ioc (0 : ℝ) 1, G0 t)) := hB.neg.sub hLG
  have hcombF : Tendsto (fun n => ∫ t in (eps n)..1, F t) atTop
      (𝓝 (-0 - ∫ t in Ioc (0 : ℝ) 1, G0 t)) := by
    refine hcomb.congr' ?_
    filter_upwards with n
    exact (ibp_eps n).symm
  have hEq : ∫ t in Ioc (0 : ℝ) 1, F t = -0 - ∫ t in Ioc (0 : ℝ) 1, G0 t :=
    tendsto_nhds_unique hLF hcombF
  linarith [hEq]

/-- Step 2: the tail piece equals the corresponding `log` integral. -/
private lemma integral_Ioi_F :
    ∫ t in Ioi (1 : ℝ), F t = ∫ t in Ioi (1 : ℝ), G1 t := by
  have hu : ∀ x ∈ Ioi (1 : ℝ),
      HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-x)) x := by
    intro x hx
    have h := (hasDerivAt_neg x).exp
    simpa only [mul_neg_one] using h
  have hv : ∀ x ∈ Ioi (1 : ℝ), HasDerivAt Real.log x⁻¹ x := by
    intro x hx
    exact Real.hasDerivAt_log (ne_of_gt (lt_trans one_pos hx))
  have huv' : IntegrableOn ((fun t : ℝ => Real.exp (-t)) * (fun t : ℝ => t⁻¹)) (Ioi (1 : ℝ)) := by
    refine integrableOn_G1_Ioi.congr_fun ?_ measurableSet_Ioi
    intro t ht
    simp only [Pi.mul_apply, G1, div_eq_mul_inv]
  have hu'v : IntegrableOn ((fun t : ℝ => -Real.exp (-t)) * (fun t : ℝ => Real.log t))
      (Ioi (1 : ℝ)) := by
    refine (integrableOn_F_Ioi.neg).congr_fun ?_ measurableSet_Ioi
    intro t ht
    simp only [Pi.mul_apply, Pi.neg_apply, F]
    ring
  have hzero : Tendsto ((fun t : ℝ => Real.exp (-t)) * (fun t : ℝ => Real.log t))
      (𝓝[>] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    have h1 : Tendsto (fun t : ℝ => Real.exp (-t)) (𝓝 (1 : ℝ)) (𝓝 (Real.exp (-1))) := by
      simpa only [Function.comp_def] using
        (Real.continuous_exp.continuousAt.comp (continuous_neg.continuousAt)).tendsto
    have h2 : Tendsto (fun t : ℝ => Real.log t) (𝓝 (1 : ℝ)) (𝓝 (Real.log 1)) :=
      (Real.continuousAt_log (by norm_num)).tendsto
    have h3 := h1.mul h2
    rw [Real.log_one, mul_zero] at h3
    exact h3.mono_left nhdsWithin_le_nhds
  have hinfty : Tendsto ((fun t : ℝ => Real.exp (-t)) * (fun t : ℝ => Real.log t))
      atTop (𝓝 (0 : ℝ)) := by
    have hexp : Tendsto (fun x : ℝ => x * Real.exp (-x)) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    refine squeeze_zero' ?_ ?_ hexp
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      simp only [Pi.mul_apply]
      exact mul_nonneg (Real.exp_nonneg _) (Real.log_nonneg hx)
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      simp only [Pi.mul_apply]
      calc Real.exp (-x) * Real.log x ≤ Real.exp (-x) * x :=
            mul_le_mul_of_nonneg_left (Real.log_le_self (by linarith)) (Real.exp_nonneg _)
        _ = x * Real.exp (-x) := by ring
  have h := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul (a := (1 : ℝ))
    (a' := (0 : ℝ)) (b' := (0 : ℝ))
    (u := fun t : ℝ => Real.exp (-t)) (u' := fun t : ℝ => -Real.exp (-t))
    (v := fun t : ℝ => Real.log t) (v' := fun t : ℝ => t⁻¹) hu hv huv' hu'v hzero hinfty
  have hG1 : ∫ x in Ioi (1 : ℝ), Real.exp (-x) * x⁻¹ = ∫ x in Ioi (1 : ℝ), G1 x := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp only [G1, div_eq_mul_inv]
  have hFneg : ∫ x in Ioi (1 : ℝ), (-Real.exp (-x)) * Real.log x = - ∫ x in Ioi (1 : ℝ), F x := by
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp only [F]
    ring
  have h' : ∫ x in Ioi (1 : ℝ), Real.exp (-x) * x⁻¹
      = 0 - 0 - ∫ x in Ioi (1 : ℝ), (-Real.exp (-x)) * Real.log x := h
  rw [hG1, hFneg] at h'
  linarith [h']

theorem eulerMascheroni_eq_integral :
    Real.eulerMascheroniConstant
      = (∫ t in Set.Ioc (0 : ℝ) 1, (1 - Real.exp (-t)) / t)
        - (∫ t in Set.Ioi (1 : ℝ), Real.exp (-t) / t) := by
  change Real.eulerMascheroniConstant
      = (∫ t in Set.Ioc (0 : ℝ) 1, G0 t) - (∫ t in Set.Ioi (1 : ℝ), G1 t)
  have hlog := Commons.Analysis.SpecialFunctions.eulerIntegral_log_exp_neg
  have hlogF : ∫ t in Ioi (0 : ℝ), F t = -Real.eulerMascheroniConstant := by
    simpa only [F] using hlog
  have hunion : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := by
    ext x; constructor
    · intro hx
      by_cases h : x ≤ 1
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr (lt_of_not_ge h)
    · rintro (h | h)
      · exact h.1
      · exact lt_trans one_pos (show (1 : ℝ) < x from h)
  have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioi 1) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact not_lt_of_ge hx.2 hx'
  have hsplit : ∫ t in Ioi (0 : ℝ), F t
      = (∫ t in Ioc 0 1, F t) + (∫ t in Ioi 1, F t) := by
    have h := MeasureTheory.setIntegral_union (μ := volume) (f := F)
      (s := Ioc (0 : ℝ) 1) (t := Ioi 1) hdisj measurableSet_Ioi
      integrableOn_F_Ioc integrableOn_F_Ioi
    rw [← hunion] at h
    simpa using h
  have hkey : -Real.eulerMascheroniConstant
      = - (∫ t in Ioc (0 : ℝ) 1, G0 t) + ∫ t in Ioi (1 : ℝ), G1 t := by
    calc -Real.eulerMascheroniConstant = ∫ t in Ioi (0 : ℝ), F t := hlogF.symm
      _ = (∫ t in Ioc 0 1, F t) + (∫ t in Ioi 1, F t) := hsplit
      _ = - (∫ t in Ioc (0 : ℝ) 1, G0 t) + ∫ t in Ioi (1 : ℝ), G1 t := by
            rw [integral_Ioc_F, integral_Ioi_F]
  have hfin : Real.eulerMascheroniConstant
      = (∫ t in Ioc (0 : ℝ) 1, G0 t) - ∫ t in Ioi (1 : ℝ), G1 t := by
    linarith [hkey]
  exact hfin

end

end Work.NumberTheory.Chen.ApSumTenth
