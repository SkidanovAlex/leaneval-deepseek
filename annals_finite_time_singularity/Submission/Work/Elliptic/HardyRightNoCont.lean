import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L2Space
import Submission.Work.Elliptic.HardyRightTonelliSwap
import Submission.Work.Spaces.cs_integral
import Submission.Work.Elliptic.integrableOn_tail_of_weighted
import Submission.Work.Elliptic.integral_Ioi_rpow_neg_three_halves

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Two private auxiliary lemmas -/

/-- **Weighted Hardy bound on a right tail.**  For `U` differentiable on `(1,∞)`, vanishing at
`+∞`, with `(t U'(t))²` integrable there, and every `z > 1`,
`U(z)² ≤ 2 z^{-1/2} ∫_z^∞ (t U'(t))² t^{-1/2} dt`.

This is the sharp weighted Hardy inequality on a tail: the proof is
`U(z) = -∫_z^∞ U'` (fundamental theorem of calculus on the half line) followed by
Cauchy–Schwarz applied to `U'(t) = (t U'(t) · t^{-1/4}) · t^{-3/4}` together with
`∫_z^∞ t^{-3/2} dt = 2 z^{-1/2}`. -/
private theorem hardy_right_tail_pw (U U' : ℝ → ℝ)
    (hderiv : ∀ z ∈ Set.Ioi (1:ℝ), HasDerivAt U (U' z) z)
    (htend : Filter.Tendsto U Filter.atTop (nhds 0))
    (hint : MeasureTheory.IntegrableOn (fun z : ℝ => (z * U' z) ^ 2) (Set.Ioi 1)) :
    ∀ z ∈ Set.Ioi (1:ℝ),
      MeasureTheory.IntegrableOn U' (Set.Ioi z) ∧
      (U z) ^ 2 ≤ 2 * z ^ (-(1/2:ℝ)) *
        ∫ t in Set.Ioi z, (t * U' t) ^ 2 * t ^ (-(1/2:ℝ)) := by
  intro z hz
  have hz1 : (1:ℝ) < z := hz
  have hzpos : (0:ℝ) < z := lt_trans one_pos hz1
  -- The weighted square `(t U' t)² t^{-1/2}` is integrable on `(1,∞)`: on `(1,∞)` the extra
  -- weight `t^{-1/2}` is at most `1`, so it is dominated by the integrable `(t U' t)²`.
  have hG1 : IntegrableOn (fun t : ℝ => (t * U' t) ^ 2 * t ^ (-(1/2:ℝ))) (Set.Ioi 1) := by
    have hAESM : AEStronglyMeasurable (fun t : ℝ => (t * U' t) ^ 2 * t ^ (-(1/2:ℝ)))
        (volume.restrict (Set.Ioi (1:ℝ))) := by
      have h1 : AEStronglyMeasurable (fun t : ℝ => (t * U' t) ^ 2)
          (volume.restrict (Set.Ioi (1:ℝ))) := hint.aestronglyMeasurable
      have h2 : AEStronglyMeasurable (fun t : ℝ => t ^ (-(1/2:ℝ)))
          (volume.restrict (Set.Ioi (1:ℝ))) :=
        (continuousOn_id.rpow_const
          (fun t ht => Or.inl (ne_of_gt (lt_trans one_pos (mem_Ioi.mp ht))))).aestronglyMeasurable
          measurableSet_Ioi
      exact h1.mul h2
    refine hint.mono' hAESM ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htp : (0:ℝ) < t := lt_trans one_pos (mem_Ioi.mp ht)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg htp.le _))]
    refine mul_le_of_le_one_right (sq_nonneg _) ?_
    have h := Real.rpow_le_rpow_of_exponent_le (le_of_lt (mem_Ioi.mp ht))
      (show (-(1/2:ℝ)) ≤ 0 by norm_num)
    rwa [Real.rpow_zero] at h
  have hGz : IntegrableOn (fun t : ℝ => (t * U' t) ^ 2 * t ^ (-(1/2:ℝ))) (Set.Ioi z) :=
    hG1.mono_set (Ioi_subset_Ioi hz1.le)
  -- `U'` agrees with `deriv U` on `(z,∞)`, hence is a.e. strongly measurable there.
  have hU'meas : AEStronglyMeasurable U' (volume.restrict (Set.Ioi z)) := by
    have hd : AEStronglyMeasurable (deriv U) (volume.restrict (Set.Ioi z)) :=
      (measurable_deriv U).aestronglyMeasurable
    refine hd.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (hderiv t (mem_Ioi.mpr (lt_trans hz1 (mem_Ioi.mp ht)))).deriv
  have hU'int : IntegrableOn U' (Set.Ioi z) :=
    integrableOn_tail_of_weighted z hzpos U' hU'meas hGz
  refine ⟨hU'int, ?_⟩
  -- Splitting `U'(t) = (t U'(t) · t^{-1/4}) · t^{-3/4}`.
  set u : ℝ → ℝ := fun t => (t * U' t) * t ^ (-(1/4:ℝ)) with hu
  set v : ℝ → ℝ := fun t => t ^ (-(3/4:ℝ)) with hv
  have hzmem : ∀ t ∈ Set.Ioi z, (0:ℝ) < t := fun t ht => lt_trans hzpos ht
  have hu_sq : ∀ t ∈ Set.Ioi z, u t ^ 2 = (t * U' t) ^ 2 * t ^ (-(1/2:ℝ)) := by
    intro t ht
    have htpos := hzmem t ht
    have hb : (t ^ (-(1/4:ℝ))) ^ 2 = t ^ (-(1/2:ℝ)) := by
      rw [pow_two, ← Real.rpow_add htpos]; norm_num
    simp only [hu, mul_pow, hb]
  have hv_sq : ∀ t ∈ Set.Ioi z, v t ^ 2 = t ^ (-(3/2:ℝ)) := by
    intro t ht
    have htpos := hzmem t ht
    simp only [hv]
    rw [pow_two, ← Real.rpow_add htpos]
    norm_num
  have huv : ∀ t ∈ Set.Ioi z, u t * v t = U' t := by
    intro t ht
    have htpos := hzmem t ht
    have hb : t ^ (-(1/4:ℝ)) * t ^ (-(3/4:ℝ)) = t⁻¹ := by
      rw [← Real.rpow_add htpos]; norm_num; rw [Real.rpow_neg_one]
    have htne : t ≠ 0 := ne_of_gt htpos
    simp only [hu, hv]
    rw [mul_assoc, hb]
    field_simp
  have hu_aesm : AEStronglyMeasurable u (volume.restrict (Set.Ioi z)) := by
    rw [hu]
    exact ((measurable_id.aestronglyMeasurable).mul hU'meas).mul
      ((continuousOn_id.rpow_const
        (fun t ht => Or.inl (ne_of_gt (hzmem t ht)))).aestronglyMeasurable measurableSet_Ioi)
  have hu_mem : MemLp u 2 (volume.restrict (Set.Ioi z)) := by
    rw [MeasureTheory.memLp_two_iff_integrable_sq hu_aesm]
    refine hGz.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (hu_sq t ht).symm
  have hv_aesm : AEStronglyMeasurable v (volume.restrict (Set.Ioi z)) := by
    rw [hv]
    exact (continuousOn_id.rpow_const
        (fun t ht => Or.inl (ne_of_gt (hzmem t ht)))).aestronglyMeasurable measurableSet_Ioi
  have hv_mem : MemLp v 2 (volume.restrict (Set.Ioi z)) := by
    rw [MeasureTheory.memLp_two_iff_integrable_sq hv_aesm]
    have hbase : Integrable (fun t : ℝ => t ^ (-(3/2:ℝ))) (volume.restrict (Set.Ioi z)) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num : (-(3/2:ℝ)) < -1) hzpos
    refine hbase.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (hv_sq t ht).symm
  have hcs := Work.Spaces.cs_integral hu_mem hv_mem
  rw [setIntegral_congr_fun measurableSet_Ioi huv,
      setIntegral_congr_fun measurableSet_Ioi hu_sq,
      setIntegral_congr_fun measurableSet_Ioi hv_sq,
      integral_Ioi_rpow_neg_three_halves z hzpos] at hcs
  -- The fundamental theorem of calculus on `(z,∞)`: `∫_z^∞ U' = 0 - U z`.
  have hFTC : ∫ t in Set.Ioi z, U' t = - U z := by
    have hcont : ContinuousWithinAt U (Set.Ici z) z :=
      (hderiv z hz).continuousAt.continuousWithinAt
    have hd : ∀ x ∈ Set.Ioi z, HasDerivAt U (U' x) x :=
      fun x hx => hderiv x (mem_Ioi.mpr (lt_trans hz1 (mem_Ioi.mp hx)))
    have key := integral_Ioi_of_hasDerivAt_of_tendsto hcont hd hU'int htend
    simpa using key
  calc (U z) ^ 2 = (∫ t in Set.Ioi z, U' t) ^ 2 := by rw [hFTC]; ring
    _ ≤ (∫ t in Set.Ioi z, (t * U' t) ^ 2 * t ^ (-(1/2:ℝ))) * (2 * z ^ (-(1/2:ℝ))) := hcs
    _ = 2 * z ^ (-(1/2:ℝ)) * ∫ t in Set.Ioi z, (t * U' t) ^ 2 * t ^ (-(1/2:ℝ)) := by ring

/-- **Lintegral bound for `ofReal` gives Bochner integrability.**  If `f ≥ 0` a.e. is
a.e. strongly measurable on `(1,∞)` and `∫⁻ ofReal (f z) ≤ ofReal c` with `c ≥ 0`, then
`f` is integrable on `(1,∞)` and `∫ f ≤ c`. -/
private theorem integrable_of_lintegral_ofReal_le (f : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hmeas : MeasureTheory.AEStronglyMeasurable f (MeasureTheory.volume.restrict (Set.Ioi (1:ℝ))))
    (hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (1:ℝ))] f)
    (h : ∫⁻ z in Set.Ioi (1:ℝ), ENNReal.ofReal (f z) ≤ ENNReal.ofReal c) :
    MeasureTheory.IntegrableOn f (Set.Ioi (1:ℝ)) ∧
      ∫ z in Set.Ioi (1:ℝ), f z ≤ c := by
  have hne : (∫⁻ z in Set.Ioi (1:ℝ), ENNReal.ofReal (f z)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  have hint : IntegrableOn f (Set.Ioi (1:ℝ)) :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hmeas hnn).mp hne
  refine ⟨hint, ?_⟩
  rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae hnn hmeas]
  calc (∫⁻ z in Set.Ioi (1:ℝ), ENNReal.ofReal (f z)).toReal
      ≤ (ENNReal.ofReal c).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    _ = c := ENNReal.toReal_ofReal hc

/-! ## The Hardy inequality on the right half-line -/

theorem HardyRightNoCont (U U' : ℝ → ℝ)
    (hderiv : ∀ z ∈ Set.Ioi (1 : ℝ), HasDerivAt U (U' z) z)
    (htend : Filter.Tendsto U Filter.atTop (nhds 0))
    (hint : MeasureTheory.IntegrableOn (fun z : ℝ => (z * U' z) ^ 2) (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn (fun z : ℝ => U z ^ 2) (Set.Ioi 1) ∧
      ∫ z in Set.Ioi (1 : ℝ), U z ^ 2 ≤ 6 * ∫ z in Set.Ioi (1 : ℝ), (z * U' z) ^ 2 := by
  -- Abbreviations.
  set phi : ℝ → ℝ := fun t => (t * U' t) ^ 2 * t ^ (-(1/2:ℝ)) with hphi
  set G : ℝ → ℝ := fun z => (z * U' z) ^ 2 with hG
  set gg : ℝ → ℝ := fun t => (t * deriv U t) ^ 2 * (Real.sqrt t)⁻¹ with hgg
  set f : ℝ → ENNReal := fun t => ENNReal.ofReal (gg t) with hf
  -- `U'` coincides with `deriv U` on `(1,∞)`.
  have hU'eq : ∀ t ∈ Set.Ioi (1:ℝ), U' t = deriv U t :=
    fun t ht => (hderiv t ht).deriv.symm
  -- Measurability of `gg` and `f`.
  have hgg_meas : Measurable gg := by
    rw [hgg]
    exact ((measurable_id.mul (measurable_deriv U)).pow_const 2).mul
      (Real.continuous_sqrt.measurable.inv)
  have hf_meas : Measurable f := by
    rw [hf]; exact ENNReal.continuous_ofReal.measurable.comp hgg_meas
  -- `phi` and `gg` agree on `(1,∞)`.
  have hphigg : ∀ t ∈ Set.Ioi (1:ℝ), phi t = gg t := by
    intro t ht
    have htpos : 0 < t := lt_trans one_pos ht
    simp only [hphi, hgg]
    rw [hU'eq t ht]
    congr 1
    rw [Real.sqrt_eq_rpow, Real.rpow_neg htpos.le]
  have htail := hardy_right_tail_pw U U' hderiv htend hint
  -- Per-`z` bound in `ℝ≥0∞`.
  have hpt : ∀ z ∈ Set.Ioi (1:ℝ),
      ENNReal.ofReal (U z ^ 2)
        ≤ ENNReal.ofReal (2 * z ^ (-(1/2:ℝ))) * (∫⁻ t in Set.Ioi z, f t) := by
    intro z hz
    have hz1 : (1:ℝ) < z := mem_Ioi.mp hz
    have hzpos : (0:ℝ) < z := lt_trans one_pos hz1
    obtain ⟨_hU'int, hbound⟩ := htail z hz
    have hbound' : (U z) ^ 2 ≤ 2 * z ^ (-(1/2:ℝ)) * ∫ t in Set.Ioi z, phi t := hbound
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi z)] phi := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have htpos : 0 < t := lt_trans hzpos (mem_Ioi.mp ht)
      rw [hphi]
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg htpos.le _)
    have hmeas : AEStronglyMeasurable phi (volume.restrict (Set.Ioi z)) := by
      have hcongr : gg =ᵐ[volume.restrict (Set.Ioi z)] phi := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact (hphigg t (lt_trans hz1 (mem_Ioi.mp ht))).symm
      exact hgg_meas.aestronglyMeasurable.congr hcongr
    have hint_eq : (∫ t in Set.Ioi z, phi t) = (∫⁻ t in Set.Ioi z, f t).toReal := by
      rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas]
      congr 1
      refine setLIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
      rw [hf]
      congr 1
      exact hphigg t (lt_trans hz1 (mem_Ioi.mp ht))
    have hc : 0 ≤ 2 * z ^ (-(1/2:ℝ)) := by positivity
    calc ENNReal.ofReal (U z ^ 2)
        ≤ ENNReal.ofReal (2 * z ^ (-(1/2:ℝ)) * ∫ t in Set.Ioi z, phi t) :=
          ENNReal.ofReal_le_ofReal hbound'
      _ = ENNReal.ofReal (2 * z ^ (-(1/2:ℝ)) * (∫⁻ t in Set.Ioi z, f t).toReal) := by
          rw [hint_eq]
      _ = ENNReal.ofReal (2 * z ^ (-(1/2:ℝ))) *
            ENNReal.ofReal ((∫⁻ t in Set.Ioi z, f t).toReal) :=
          ENNReal.ofReal_mul hc
      _ ≤ ENNReal.ofReal (2 * z ^ (-(1/2:ℝ))) * (∫⁻ t in Set.Ioi z, f t) :=
          mul_le_mul_of_nonneg_left ENNReal.ofReal_toReal_le bot_le
  have hstep1 : (∫⁻ z in Set.Ioi (1:ℝ), ENNReal.ofReal (U z ^ 2))
      ≤ ∫⁻ z in Set.Ioi (1:ℝ),
          ENNReal.ofReal (2 * z ^ (-(1/2:ℝ))) * (∫⁻ t in Set.Ioi z, f t) :=
    setLIntegral_mono' measurableSet_Ioi hpt
  have hstep2 := HardyRightTonelliSwap f hf_meas
  have hGint : IntegrableOn G (Set.Ioi (1:ℝ)) := by rw [hG]; exact hint
  have hpt2 : ∀ t ∈ Set.Ioi (1:ℝ), f t * ENNReal.ofReal (4 * (t ^ ((1/2:ℝ)) - 1))
      ≤ ENNReal.ofReal (4 * G t) := by
    intro t ht
    have ht1 : (1:ℝ) < t := mem_Ioi.mp ht
    have htpos : (0:ℝ) < t := lt_trans one_pos ht1
    have hggnn : 0 ≤ gg t := by
      rw [hgg]
      exact mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (Real.sqrt_nonneg t))
    rw [hf, ← ENNReal.ofReal_mul hggnn]
    apply ENNReal.ofReal_le_ofReal
    simp only [hgg, hG]
    rw [hU'eq t ht, Real.sqrt_eq_rpow]
    have h1 : (0:ℝ) ≤ t ^ (1/2:ℝ) := Real.rpow_nonneg htpos.le _
    have hpos : 0 < t ^ (1/2:ℝ) := Real.rpow_pos_of_pos htpos _
    have hkey : (t ^ (1/2:ℝ))⁻¹ * (t ^ (1/2:ℝ) - 1) = 1 - (t ^ (1/2:ℝ))⁻¹ := by
      rw [mul_sub, inv_mul_cancel₀ hpos.ne', mul_one]
    have hle1 : 1 - (t ^ (1/2:ℝ))⁻¹ ≤ 1 := sub_le_self _ (inv_nonneg.mpr h1)
    have heq : (t * deriv U t) ^ 2 * (t ^ (1/2:ℝ))⁻¹ * (4 * (t ^ (1/2:ℝ) - 1))
        = 4 * (t * deriv U t) ^ 2 * (1 - (t ^ (1/2:ℝ))⁻¹) := by
      rw [← hkey]; ring
    rw [heq]
    calc 4 * (t * deriv U t) ^ 2 * (1 - (t ^ (1/2:ℝ))⁻¹)
        ≤ 4 * (t * deriv U t) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hle1 (mul_nonneg (by norm_num) (sq_nonneg _))
      _ = 4 * (t * deriv U t) ^ 2 := by ring
  have hstep3 : (∫⁻ t in Set.Ioi (1:ℝ), f t * ENNReal.ofReal (4 * (t ^ ((1/2:ℝ)) - 1)))
      ≤ ENNReal.ofReal (4 * ∫ z in Set.Ioi (1:ℝ), G z) := by
    have h4Gnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (1:ℝ))] (fun t => 4 * G t) :=
      Filter.Eventually.of_forall (fun t => mul_nonneg (by norm_num) (by rw [hG]; exact sq_nonneg _))
    calc (∫⁻ t in Set.Ioi (1:ℝ), f t * ENNReal.ofReal (4 * (t ^ ((1/2:ℝ)) - 1)))
        ≤ ∫⁻ t in Set.Ioi (1:ℝ), ENNReal.ofReal (4 * G t) :=
          setLIntegral_mono' measurableSet_Ioi hpt2
      _ = ENNReal.ofReal (∫ t in Set.Ioi (1:ℝ), 4 * G t) :=
          (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hGint.const_mul (4:ℝ)) h4Gnn).symm
      _ = ENNReal.ofReal (4 * ∫ z in Set.Ioi (1:ℝ), G z) := by
          rw [MeasureTheory.integral_const_mul]
  have hmain : (∫⁻ z in Set.Ioi (1:ℝ), ENNReal.ofReal (U z ^ 2))
      ≤ ENNReal.ofReal (4 * ∫ z in Set.Ioi (1:ℝ), G z) :=
    le_trans hstep1 (le_trans (le_of_eq hstep2) hstep3)
  have hUon : ContinuousOn U (Set.Ioi (1:ℝ)) :=
    fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
  have hU2_aesm : AEStronglyMeasurable (fun z => U z ^ 2) (volume.restrict (Set.Ioi (1:ℝ))) :=
    (hUon.pow 2).aestronglyMeasurable measurableSet_Ioi
  have hU2_nn : 0 ≤ᵐ[volume.restrict (Set.Ioi (1:ℝ))] (fun z => U z ^ 2) :=
    Filter.Eventually.of_forall (fun z => sq_nonneg _)
  have hGnn : 0 ≤ ∫ z in Set.Ioi (1:ℝ), G z :=
    integral_nonneg (fun z => by rw [hG]; exact sq_nonneg _)
  have hc4 : 0 ≤ 4 * ∫ z in Set.Ioi (1:ℝ), G z := by linarith
  obtain ⟨hintU2, hle4⟩ :=
    integrable_of_lintegral_ofReal_le (fun z => U z ^ 2) (4 * ∫ z in Set.Ioi (1:ℝ), G z) hc4
      hU2_aesm hU2_nn hmain
  refine ⟨hintU2, ?_⟩
  have hGeq : (∫ z in Set.Ioi (1:ℝ), G z) = ∫ z in Set.Ioi (1:ℝ), (z * U' z) ^ 2 := by
    simp only [hG]
  rw [hGeq] at hle4
  have hX : 0 ≤ ∫ z in Set.Ioi (1:ℝ), (z * U' z) ^ 2 :=
    integral_nonneg (fun z => sq_nonneg _)
  linarith

end Work.Elliptic
