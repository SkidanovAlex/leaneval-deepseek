import Mathlib
import Submission.Work.HP.JcVolDefs
import Submission.Work.HP.IntegralModel

/-!
# The estimate `Work.HP.EstimateMu`

Let `qbar u = max ((u 0)^2) ((u 1)^2)` on `EuclideanSpace ℝ (Fin 2)`.

* `QbarReduction` reduces `∫ (if qbar ≤ 1 then F qbar else 0)` to `4 ∫_0^1 F`.
* `EstimateMuStrong` proves the estimate with the integral *outside* the subtraction
  (the shape used in the paper, matching `Work.HP.EstimateMu2`).

Note on the literal statement of `EstimateMu`: in Lean the notation `∫ u, e` captures
everything to the right, so `∫ u, (if … else 0) - M` parses as `∫ u, ((if … else 0) - M)`;
the constant `M = 4(N-2)/N` sits *inside* the integral.  As `M ≠ 0` on a set of infinite
measure the integrand is not integrable, so the Bochner integral vanishes
(`MeasureTheory.integral_undef`) and the literal statement reduces to `0 ≤ RHS`.
`EstimateMuStrong` is the mathematically meaningful version.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace Work.HP

variable {ι : Type*} [Fintype ι]

/-! ## Elementary facts about `qbar` -/

lemma qbar_nonneg (u : EuclideanSpace ℝ (Fin 2)) : 0 ≤ qbar u := by
  unfold qbar; positivity

lemma continuous_qbar : Continuous qbar := by unfold qbar; fun_prop

lemma measurableSet_qbar_le_one : MeasurableSet {u : EuclideanSpace ℝ (Fin 2) | qbar u ≤ 1} :=
  (isClosed_le continuous_qbar continuous_const).measurableSet

/-! ## Volume of the `qbar`-sublevel sets -/

lemma volume_qbar_le (b : ℝ) :
    (volume : Measure (EuclideanSpace ℝ (Fin 2))) {u | qbar u ≤ b} = ENNReal.ofReal (4 * b) := by
  rcases lt_or_ge (0:ℝ) b with hb | hb
  · have hmeas : MeasurableSet {u : EuclideanSpace ℝ (Fin 2) | qbar u ≤ b} :=
      (isClosed_le continuous_qbar continuous_const).measurableSet
    have hmap : (volume : Measure (EuclideanSpace ℝ (Fin 2))) {u | qbar u ≤ b}
        = volume (WithLp.toLp 2 ⁻¹' {u : EuclideanSpace ℝ (Fin 2) | qbar u ≤ b}) := by
      rw [← (PiLp.volume_preserving_toLp (Fin 2)).map_eq]
      rw [Measure.map_apply (PiLp.volume_preserving_toLp (Fin 2)).measurable hmeas]
    have hpre : WithLp.toLp 2 ⁻¹' {u : EuclideanSpace ℝ (Fin 2) | qbar u ≤ b}
        = Set.Icc (fun _ : Fin 2 => -Real.sqrt b) (fun _ => Real.sqrt b) := by
      ext f
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_Icc, Pi.le_def, Fin.forall_fin_two]
      rw [show qbar (WithLp.toLp 2 f : EuclideanSpace ℝ (Fin 2)) = max ((f 0)^2) ((f 1)^2)
            from by simp [qbar]]
      rw [max_le_iff]
      have key : ∀ x : ℝ, x^2 ≤ b ↔ |x| ≤ Real.sqrt b := by
        intro x; conv_lhs => rw [← Real.sq_sqrt hb.le]
        rw [sq_le_sq, abs_of_nonneg (Real.sqrt_nonneg b)]
      rw [key, key, abs_le, abs_le]; tauto
    rw [hmap, hpre, Real.volume_Icc_pi, Fin.prod_univ_two]
    rw [show Real.sqrt b - -Real.sqrt b = Real.sqrt b + Real.sqrt b from by ring]
    rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ Real.sqrt b + Real.sqrt b)]
    congr 1
    nlinarith [Real.sq_sqrt hb.le]
  · have hsub : {u : EuclideanSpace ℝ (Fin 2) | qbar u ≤ b} ⊆ {0} := by
      intro u hu
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      have hmax : max ((u 0)^2) ((u 1)^2) = 0 := by
        have h2 : qbar u ≤ 0 := le_trans hu hb
        unfold qbar at h2
        exact le_antisymm h2 (by positivity)
      have h0 : u 0 = 0 := by
        have hh : (u 0)^2 ≤ 0 := by rw [← hmax]; exact le_max_left _ _
        exact sq_eq_zero_iff.mp (le_antisymm hh (sq_nonneg _))
      have h1 : u 1 = 0 := by
        have hh : (u 1)^2 ≤ 0 := by rw [← hmax]; exact le_max_right _ _
        exact sq_eq_zero_iff.mp (le_antisymm hh (sq_nonneg _))
      ext i; fin_cases i <;> simp [h0, h1]
    have hvol : (volume : Measure (EuclideanSpace ℝ (Fin 2))) {u | qbar u ≤ b} = 0 :=
      measure_mono_null hsub (by simp)
    rw [hvol]
    exact (ENNReal.ofReal_eq_zero.mpr (by linarith : 4 * b ≤ 0)).symm

/-- The volume of the full space `EuclideanSpace ℝ (Fin 2)` is infinite. -/
lemma volume_univ_fin2 : (volume : Measure (EuclideanSpace ℝ (Fin 2))) Set.univ = ⊤ := by
  have h1 : (volume : Measure (EuclideanSpace ℝ (Fin 2))) Set.univ
      = (volume : Measure (Fin 2 → ℝ)) Set.univ := by
    rw [← (PiLp.volume_preserving_toLp (Fin 2)).map_eq]
    rw [Measure.map_apply (PiLp.volume_preserving_toLp (Fin 2)).measurable MeasurableSet.univ,
      Set.preimage_univ]
  rw [h1]
  have h2 : (volume : Measure (Fin 2 → ℝ)) Set.univ
      = (volume : Measure (ℝ × ℝ)) Set.univ := by
    rw [← (MeasureTheory.volume_preserving_finTwoArrow ℝ).map_eq]
    rw [Measure.map_apply (MeasureTheory.volume_preserving_finTwoArrow ℝ).measurable
      MeasurableSet.univ, Set.preimage_univ]
  rw [h2, Measure.volume_eq_prod,
    show (Set.univ : Set (ℝ × ℝ)) = Set.univ ×ˢ Set.univ from by ext p; simp,
    Measure.prod_prod, Real.volume_univ]
  simp

lemma ofReal_four_smul (x : ℝ) (hx : 0 ≤ x) :
    (4 : ENNReal) • ENNReal.ofReal x = ENNReal.ofReal (4 * x) := by
  rw [smul_eq_mul, show (4 : ENNReal) = ENNReal.ofReal (4:ℝ) from by simp]
  exact (ENNReal.ofReal_mul' hx).symm

lemma volume_Icc_zero_one_inter_Iic (a : ℝ) :
    (volume : Measure ℝ) (Set.Icc (0:ℝ) 1 ∩ Set.Iic a)
      = ENNReal.ofReal (min 1 (max a 0)) := by
  rcases lt_or_ge a 0 with ha | ha
  · have h0 : min 1 (max a 0) = 0 := by
      rw [max_eq_right ha.le, min_eq_right zero_le_one]
    have hemp : Set.Icc (0:ℝ) 1 ∩ Set.Iic a = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro x ⟨hx1, hx2⟩
      simp only [Set.mem_Icc] at hx1
      simp only [Set.mem_Iic] at hx2
      linarith [hx1.1, hx2]
    rw [hemp, measure_empty, h0, ENNReal.ofReal_zero]
  · rcases lt_or_ge a 1 with ha1 | ha1
    · have hset : Set.Icc (0:ℝ) 1 ∩ Set.Iic a = Set.Icc 0 a := by
        ext x; simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iic]
        exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, le_trans h.2 ha1.le⟩, h.2⟩⟩
      have hmin : min 1 (max a 0) = a := by rw [max_eq_left ha, min_eq_right ha1.le]
      rw [hset, Real.volume_Icc, hmin]
      simp
    · have hset : Set.Icc (0:ℝ) 1 ∩ Set.Iic a = Set.Icc (0:ℝ) 1 := by
        ext x; simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iic]
        exact ⟨fun h => h.1, fun h => ⟨h, le_trans h.2 ha1⟩⟩
      have hmin : min 1 (max a 0) = 1 := by rw [max_eq_left ha, min_eq_left ha1]
      rw [hset, Real.volume_Icc, hmin]
      norm_num

lemma qbar_map_restrict :
    Measure.map qbar (volume.restrict {u : EuclideanSpace ℝ (Fin 2) | qbar u ≤ 1})
      = (4 : ENNReal) • volume.restrict (Set.Icc (0:ℝ) 1) := by
  have hSmeas := measurableSet_qbar_le_one
  haveI hfin : IsFiniteMeasure (volume.restrict {u : EuclideanSpace ℝ (Fin 2) | qbar u ≤ 1}) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, volume_qbar_le 1]
    norm_num
  refine Measure.ext_of_Iic _ _ (fun a => ?_)
  rw [Measure.map_apply continuous_qbar.measurable measurableSet_Iic,
      Measure.restrict_apply (measurableSet_Iic.preimage continuous_qbar.measurable),
      Measure.smul_apply, Measure.restrict_apply measurableSet_Iic,
      Set.inter_comm (Set.Iic a) (Set.Icc (0:ℝ) 1), volume_Icc_zero_one_inter_Iic a]
  have hset : qbar ⁻¹' Set.Iic a ∩ {u : EuclideanSpace ℝ (Fin 2) | qbar u ≤ 1}
      = {u : EuclideanSpace ℝ (Fin 2) | qbar u ≤ min a 1} := by
    ext u; simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, Set.mem_setOf_eq]
    exact ⟨fun h => le_min h.1 h.2,
      fun h => ⟨le_trans h (min_le_left _ _), le_trans h (min_le_right _ _)⟩⟩
  rw [hset, volume_qbar_le (min a 1)]
  rcases lt_or_ge a 0 with ha | ha
  · rw [show min a 1 = a from min_eq_left (by linarith : a ≤ 1),
      show min 1 (max a 0) = 0 from by rw [max_eq_right ha.le, min_eq_right zero_le_one],
      ENNReal.ofReal_eq_zero.mpr (by linarith : 4 * a ≤ 0), ENNReal.ofReal_zero]
    simp
  · by_cases ha1 : a ≤ 1
    · rw [show min a 1 = a from min_eq_left ha1,
        show min 1 (max a 0) = a from by rw [max_eq_left ha, min_eq_right ha1]]
      exact (ofReal_four_smul a ha).symm
    · have ha1' : 1 < a := not_le.mp ha1
      rw [show min a 1 = 1 from min_eq_right ha1'.le,
        show min 1 (max a 0) = 1 from by rw [max_eq_left ha, min_eq_left ha1'.le]]
      exact (ofReal_four_smul 1 (by norm_num)).symm

/-- Reduction of the integral of a function of `qbar` over the unit square to a one
dimensional integral. -/
theorem QbarReduction (F : ℝ → ℝ) (hF : Continuous F) :
    ∫ u : EuclideanSpace ℝ (Fin 2), (if qbar u ≤ 1 then F (qbar u) else 0)
      = 4 * ∫ s in (0:ℝ)..1, F s := by
  have hSmeas := measurableSet_qbar_le_one
  have h1 : (fun u : EuclideanSpace ℝ (Fin 2) => (if qbar u ≤ 1 then F (qbar u) else 0))
      = Set.indicator {u : EuclideanSpace ℝ (Fin 2) | qbar u ≤ 1} (fun u => F (qbar u)) := by
    funext u; rw [Set.indicator_apply]
    by_cases h : qbar u ≤ 1
    · rw [if_pos h, if_pos (show u ∈ {u : EuclideanSpace ℝ (Fin 2) | qbar u ≤ 1} from h)]
    · rw [if_neg h, if_neg (show ¬ (u ∈ {u : EuclideanSpace ℝ (Fin 2) | qbar u ≤ 1}) from h)]
  rw [h1, MeasureTheory.integral_indicator hSmeas]
  rw [← MeasureTheory.integral_map continuous_qbar.measurable.aemeasurable
        (hF.stronglyMeasurable.aestronglyMeasurable)]
  rw [qbar_map_restrict]
  have hsm := MeasureTheory.integral_smul_measure
      (μ := volume.restrict (Set.Icc (0:ℝ) 1)) F (4 : ENNReal)
  rw [hsm, show (4 : ENNReal).toReal = 4 from by norm_num, smul_eq_mul]
  congr 1
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  rw [← Measure.restrict_congr_set
        (MeasureTheory.Ioc_ae_eq_Icc (μ := (volume : Measure ℝ)) (a := (0:ℝ)) (b := 1))]

/-! ## One dimensional integrals of `(√·)^d` -/

lemma sqrt_pow_integral_gen (d : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    ∫ s in (0:ℝ)..L, (Real.sqrt s) ^ d = 2 * (Real.sqrt L) ^ (d + 2) / ((d:ℝ) + 2) := by
  have key := intervalIntegral.integral_comp_mul_deriv (a := (0:ℝ)) (b := Real.sqrt L)
      (f := fun t : ℝ => t^2) (f' := fun t : ℝ => 2*t) (g := fun t : ℝ => (Real.sqrt t)^d)
      (fun x _ => by simpa using hasDerivAt_pow 2 x)
      ((continuous_const.mul continuous_id).continuousOn) (Real.continuous_sqrt.pow d)
  have key' : (∫ x in (0:ℝ)..Real.sqrt L, (Real.sqrt (x^2))^d * (2*x))
      = ∫ x in (0:ℝ)..L, (Real.sqrt x)^d := by
    simpa [Real.sq_sqrt hL] using key
  rw [← key']
  have hcongr : (∫ x in (0:ℝ)..Real.sqrt L, (Real.sqrt (x^2))^d * (2*x))
      = ∫ x in (0:ℝ)..Real.sqrt L, 2 * x^(d+1) := by
    apply intervalIntegral.integral_congr
    intro x hx
    simp only []
    rw [Set.uIcc_of_le (Real.sqrt_nonneg L)] at hx
    rw [Real.sqrt_sq hx.1, pow_succ]
    ring
  rw [hcongr, intervalIntegral.integral_const_mul, integral_pow]
  rw [zero_pow (by omega : d + 1 + 1 ≠ 0), sub_zero]
  push_cast
  rw [show (d + 1 + 1) = (d + 2) from by omega]
  ring

theorem ShiftedSqrtIntegral (d : ℕ) (hd : 1 ≤ d) (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ∫ s in (0:ℝ)..1, (Real.sqrt (max (s - ε) 0)) ^ d
      = 2 * (Real.sqrt (1 - ε)) ^ (d + 2) / ((d:ℝ) + 2) := by
  have hcont : Continuous (fun x : ℝ => (Real.sqrt (max x 0))^d) :=
    (Real.continuous_sqrt.comp (continuous_id.max continuous_const)).pow d
  have step1 : (∫ s in (0:ℝ)..1, (Real.sqrt (max (s - ε) 0))^d)
      = ∫ x in (-ε)..(1-ε), (Real.sqrt (max x 0))^d := by
    have h := intervalIntegral.integral_comp_sub_right
      (f := fun y : ℝ => (Real.sqrt (max y 0))^d) (a := (0:ℝ)) (b := 1) ε
    simpa only [zero_sub] using h
  have hsplit : (∫ x in (-ε)..(1-ε), (Real.sqrt (max x 0))^d)
      = ∫ x in (0:ℝ)..(1-ε), (Real.sqrt (max x 0))^d := by
    have hi1 : IntervalIntegrable (fun x : ℝ => (Real.sqrt (max x 0))^d) volume (-ε) 0 :=
      hcont.intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun x : ℝ => (Real.sqrt (max x 0))^d) volume 0 (1-ε) :=
      hcont.intervalIntegrable _ _
    have hadd := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
    have hz : (∫ x in (-ε)..0, (Real.sqrt (max x 0))^d) = 0 := by
      have hcong : (∫ x in (-ε)..0, (Real.sqrt (max x 0))^d)
          = ∫ x in (-ε)..0, (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        simp only []
        rw [Set.uIcc_of_le (by linarith : -ε ≤ 0)] at hx
        rw [max_eq_right hx.2, Real.sqrt_zero, zero_pow (by omega : d ≠ 0)]
      rw [hcong]; simp
    rw [← hadd, hz, zero_add]
  rw [step1, hsplit]
  have hcongr : (∫ x in (0:ℝ)..(1-ε), (Real.sqrt (max x 0))^d)
      = ∫ x in (0:ℝ)..(1-ε), (Real.sqrt x)^d := by
    apply intervalIntegral.integral_congr
    intro x hx
    simp only []
    rw [Set.uIcc_of_le (by linarith : (0:ℝ) ≤ 1-ε)] at hx
    rw [max_eq_left hx.1]
  rw [hcongr, sqrt_pow_integral_gen d (1-ε) (by linarith)]

/-! ## The concrete `qbar` integrals -/

lemma qbar_int_one :
    ∫ u : EuclideanSpace ℝ (Fin 2), (if qbar u ≤ 1 then (1:ℝ) else 0) = 4 := by
  rw [QbarReduction (fun _ : ℝ => (1:ℝ)) continuous_const, intervalIntegral.integral_const]
  norm_num

lemma qbar_int_const (c : ℝ) :
    ∫ u : EuclideanSpace ℝ (Fin 2), (if qbar u ≤ 1 then c else 0) = 4 * c := by
  rw [QbarReduction (fun _ : ℝ => c) continuous_const, intervalIntegral.integral_const]
  ring

lemma qbar_int_pow (d : ℕ) :
    ∫ u : EuclideanSpace ℝ (Fin 2), (if qbar u ≤ 1 then (Real.sqrt (qbar u))^d else 0)
      = 8 / ((d:ℝ)+2) := by
  rw [QbarReduction (fun s : ℝ => (Real.sqrt s)^d) (Real.continuous_sqrt.pow d)]
  rw [sqrt_pow_integral_gen d 1 (by norm_num), Real.sqrt_one, one_pow, mul_one]
  rw [← mul_div_assoc, show (4:ℝ)*2 = 8 from by norm_num]

lemma qbar_int_shift (d : ℕ) (hd : 1 ≤ d) (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ∫ u : EuclideanSpace ℝ (Fin 2),
        (if qbar u ≤ 1 then (Real.sqrt (max (qbar u - ε) 0))^d else 0)
      = 8 * (Real.sqrt (1 - ε))^(d+2) / ((d:ℝ)+2) := by
  have hc : Continuous (fun s : ℝ => (Real.sqrt (max (s - ε) 0))^d) :=
    (((continuous_id.sub continuous_const).max continuous_const).sqrt).pow d
  rw [QbarReduction _ hc, ShiftedSqrtIntegral d hd ε hε hε1]
  ring_nf

/-! ## Integrability of the integrands -/

lemma integrable_qbar_const (c : ℝ) :
    Integrable (fun u : EuclideanSpace ℝ (Fin 2) => if qbar u ≤ 1 then c else 0) := by
  have hSmeas := measurableSet_qbar_le_one
  have h : (fun u : EuclideanSpace ℝ (Fin 2) => if qbar u ≤ 1 then c else 0)
      = Set.indicator {u : EuclideanSpace ℝ (Fin 2) | qbar u ≤ 1} (fun _ => c) := by
    funext u; rw [Set.indicator_apply]; by_cases h : qbar u ≤ 1 <;> simp [h]
  rw [h, integrable_indicator_iff hSmeas]
  exact integrableOn_const (by rw [volume_qbar_le 1]; exact ENNReal.ofReal_ne_top)

lemma integrable_qbar_pow (d : ℕ) :
    Integrable (fun u : EuclideanSpace ℝ (Fin 2) =>
      if qbar u ≤ 1 then (Real.sqrt (qbar u))^d else 0) := by
  have hSmeas := measurableSet_qbar_le_one
  refine (integrable_qbar_const 1).mono' ?_ ?_
  · apply Measurable.aestronglyMeasurable
    exact Measurable.ite hSmeas
      ((Real.continuous_sqrt.measurable.comp continuous_qbar.measurable).pow_const d)
      measurable_const
  · filter_upwards with u
    show ‖(if qbar u ≤ 1 then (Real.sqrt (qbar u))^d else 0)‖ ≤
      (if qbar u ≤ 1 then (1:ℝ) else 0)
    by_cases h : qbar u ≤ 1
    · rw [if_pos h, if_pos h, Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg (Real.sqrt_nonneg _) d)]
      exact pow_le_one₀ (Real.sqrt_nonneg _) (Real.sqrt_le_one.mpr h)
    · rw [if_neg h, if_neg h]; simp

lemma integrable_G1 (d : ℕ) (q : EuclideanSpace ℝ (Fin 2) → ℝ) (hqmeas : Measurable q)
    (hq0 : ∀ u, qbar u ≤ 1 → 0 ≤ q u) :
    Integrable (fun u : EuclideanSpace ℝ (Fin 2) =>
      if qbar u ≤ 1 then (Real.sqrt (max (1 - q u) 0))^d else 0) := by
  have hSmeas := measurableSet_qbar_le_one
  refine (integrable_qbar_const 1).mono' ?_ ?_
  · apply Measurable.aestronglyMeasurable
    exact Measurable.ite hSmeas
      ((Real.continuous_sqrt.measurable.comp
        ((measurable_const.sub hqmeas).max measurable_const)).pow_const d) measurable_const
  · filter_upwards with u
    show ‖(if qbar u ≤ 1 then (Real.sqrt (max (1 - q u) 0))^d else 0)‖ ≤
      (if qbar u ≤ 1 then (1:ℝ) else 0)
    by_cases h : qbar u ≤ 1
    · rw [if_pos h, if_pos h, Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg (Real.sqrt_nonneg _) d)]
      exact pow_le_one₀ (Real.sqrt_nonneg _)
        (Real.sqrt_le_one.mpr (max_le (by linarith [hq0 u h]) (by norm_num)))
    · rw [if_neg h, if_neg h]; simp

lemma integrable_G2 (d : ℕ) (q : EuclideanSpace ℝ (Fin 2) → ℝ) (hqmeas : Measurable q)
    (hq0 : ∀ u, qbar u ≤ 1 → 0 ≤ q u) :
    Integrable (fun u : EuclideanSpace ℝ (Fin 2) =>
      if qbar u ≤ 1 then (Real.sqrt (max (qbar u - q u) 0))^d else 0) := by
  have hSmeas := measurableSet_qbar_le_one
  refine (integrable_qbar_const 1).mono' ?_ ?_
  · apply Measurable.aestronglyMeasurable
    exact Measurable.ite hSmeas
      ((Real.continuous_sqrt.measurable.comp
        ((continuous_qbar.measurable.sub hqmeas).max measurable_const)).pow_const d)
      measurable_const
  · filter_upwards with u
    show ‖(if qbar u ≤ 1 then (Real.sqrt (max (qbar u - q u) 0))^d else 0)‖ ≤
      (if qbar u ≤ 1 then (1:ℝ) else 0)
    by_cases h : qbar u ≤ 1
    · rw [if_pos h, if_pos h, Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg (Real.sqrt_nonneg _) d)]
      exact pow_le_one₀ (Real.sqrt_nonneg _)
        (Real.sqrt_le_one.mpr (max_le (by linarith [hq0 u h]) (by norm_num)))
    · rw [if_neg h, if_neg h]; simp

/-! ## Bounds for the two integrals -/

lemma qbar_G1_upper (d : ℕ) (q : EuclideanSpace ℝ (Fin 2) → ℝ) (hqmeas : Measurable q)
    (hq0 : ∀ u, qbar u ≤ 1 → 0 ≤ q u) :
    ∫ u, (if qbar u ≤ 1 then (Real.sqrt (max (1 - q u) 0))^d else 0) ≤ 4 := by
  have hc : Integrable (fun u : EuclideanSpace ℝ (Fin 2) => if qbar u ≤ 1 then (1:ℝ) else 0) :=
    integrable_qbar_const 1
  have hnn : 0 ≤ᵐ[volume] (fun u : EuclideanSpace ℝ (Fin 2) =>
      if qbar u ≤ 1 then (Real.sqrt (max (1 - q u) 0))^d else 0) := by
    apply Filter.Eventually.of_forall; intro u
    simp only [Pi.zero_apply]
    by_cases h : qbar u ≤ 1
    · rw [if_pos h]; exact pow_nonneg (Real.sqrt_nonneg _) d
    · rw [if_neg h]
  have hle : (fun u : EuclideanSpace ℝ (Fin 2) =>
        if qbar u ≤ 1 then (Real.sqrt (max (1 - q u) 0))^d else 0)
      ≤ᵐ[volume] (fun u : EuclideanSpace ℝ (Fin 2) => if qbar u ≤ 1 then (1:ℝ) else 0) := by
    apply Filter.Eventually.of_forall; intro u
    show (if qbar u ≤ 1 then (Real.sqrt (max (1 - q u) 0))^d else 0)
      ≤ (if qbar u ≤ 1 then (1:ℝ) else 0)
    by_cases h : qbar u ≤ 1
    · rw [if_pos h, if_pos h]
      exact pow_le_one₀ (Real.sqrt_nonneg _)
        (Real.sqrt_le_one.mpr (max_le (by linarith [hq0 u h]) (by norm_num)))
    · rw [if_neg h, if_neg h]
  have h := integral_mono_of_nonneg hnn hc hle
  rwa [qbar_int_one] at h

lemma qbar_G1_lower (d : ℕ) (q : EuclideanSpace ℝ (Fin 2) → ℝ) (hqmeas : Measurable q)
    (ε : ℝ) (hq0 : ∀ u, qbar u ≤ 1 → 0 ≤ q u) (hqε : ∀ u, qbar u ≤ 1 → q u ≤ ε) :
    4 * (Real.sqrt (max (1 - ε) 0))^d ≤
      ∫ u, (if qbar u ≤ 1 then (Real.sqrt (max (1 - q u) 0))^d else 0) := by
  have hG1 := integrable_G1 d q hqmeas hq0
  have hnn : 0 ≤ᵐ[volume] (fun u : EuclideanSpace ℝ (Fin 2) =>
      if qbar u ≤ 1 then (Real.sqrt (max (1 - ε) 0))^d else 0) := by
    apply Filter.Eventually.of_forall; intro u
    simp only [Pi.zero_apply]
    by_cases h : qbar u ≤ 1
    · rw [if_pos h]; exact pow_nonneg (Real.sqrt_nonneg _) d
    · rw [if_neg h]
  have hle : (fun u : EuclideanSpace ℝ (Fin 2) =>
        if qbar u ≤ 1 then (Real.sqrt (max (1 - ε) 0))^d else 0)
      ≤ᵐ[volume] (fun u : EuclideanSpace ℝ (Fin 2) =>
        if qbar u ≤ 1 then (Real.sqrt (max (1 - q u) 0))^d else 0) := by
    apply Filter.Eventually.of_forall; intro u
    show (if qbar u ≤ 1 then (Real.sqrt (max (1 - ε) 0))^d else 0)
      ≤ (if qbar u ≤ 1 then (Real.sqrt (max (1 - q u) 0))^d else 0)
    by_cases h : qbar u ≤ 1
    · rw [if_pos h, if_pos h]
      exact pow_le_pow_left₀ (Real.sqrt_nonneg (max (1 - ε) 0))
        (Real.sqrt_le_sqrt (max_le_max (by linarith [hqε u h]) le_rfl)) d
    · rw [if_neg h, if_neg h]
  have h := integral_mono_of_nonneg hnn hG1 hle
  rw [qbar_int_const ((Real.sqrt (max (1 - ε) 0))^d)] at h
  linarith [h]

lemma qbar_G2_upper (d : ℕ) (q : EuclideanSpace ℝ (Fin 2) → ℝ) (hqmeas : Measurable q)
    (hq0 : ∀ u, qbar u ≤ 1 → 0 ≤ q u) :
    ∫ u, (if qbar u ≤ 1 then (Real.sqrt (max (qbar u - q u) 0))^d else 0)
      ≤ 8 / ((d:ℝ)+2) := by
  have hJ := integrable_qbar_pow d
  have hnn : 0 ≤ᵐ[volume] (fun u : EuclideanSpace ℝ (Fin 2) =>
      if qbar u ≤ 1 then (Real.sqrt (max (qbar u - q u) 0))^d else 0) := by
    apply Filter.Eventually.of_forall; intro u
    simp only [Pi.zero_apply]
    by_cases h : qbar u ≤ 1
    · rw [if_pos h]; exact pow_nonneg (Real.sqrt_nonneg _) d
    · rw [if_neg h]
  have hle : (fun u : EuclideanSpace ℝ (Fin 2) =>
        if qbar u ≤ 1 then (Real.sqrt (max (qbar u - q u) 0))^d else 0)
      ≤ᵐ[volume] (fun u : EuclideanSpace ℝ (Fin 2) =>
        if qbar u ≤ 1 then (Real.sqrt (qbar u))^d else 0) := by
    apply Filter.Eventually.of_forall; intro u
    show (if qbar u ≤ 1 then (Real.sqrt (max (qbar u - q u) 0))^d else 0)
      ≤ (if qbar u ≤ 1 then (Real.sqrt (qbar u))^d else 0)
    by_cases h : qbar u ≤ 1
    · rw [if_pos h, if_pos h]
      exact pow_le_pow_left₀ (Real.sqrt_nonneg (max (qbar u - q u) 0))
        (Real.sqrt_le_sqrt (max_le (by linarith [hq0 u h]) (qbar_nonneg u))) d
    · rw [if_neg h, if_neg h]
  have h := integral_mono_of_nonneg hnn hJ hle
  rwa [qbar_int_pow d] at h

lemma qbar_G2_lower (d : ℕ) (hd : 1 ≤ d) (q : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hqmeas : Measurable q) (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hq0 : ∀ u, qbar u ≤ 1 → 0 ≤ q u) (hqε : ∀ u, qbar u ≤ 1 → q u ≤ ε) :
    8 * (Real.sqrt (1 - ε))^(d+2) / ((d:ℝ)+2) ≤
      ∫ u, (if qbar u ≤ 1 then (Real.sqrt (max (qbar u - q u) 0))^d else 0) := by
  have hG2 := integrable_G2 d q hqmeas hq0
  have hnn : 0 ≤ᵐ[volume] (fun u : EuclideanSpace ℝ (Fin 2) =>
      if qbar u ≤ 1 then (Real.sqrt (max (qbar u - ε) 0))^d else 0) := by
    apply Filter.Eventually.of_forall; intro u
    simp only [Pi.zero_apply]
    by_cases h : qbar u ≤ 1
    · rw [if_pos h]; exact pow_nonneg (Real.sqrt_nonneg _) d
    · rw [if_neg h]
  have hle : (fun u : EuclideanSpace ℝ (Fin 2) =>
        if qbar u ≤ 1 then (Real.sqrt (max (qbar u - ε) 0))^d else 0)
      ≤ᵐ[volume] (fun u : EuclideanSpace ℝ (Fin 2) =>
        if qbar u ≤ 1 then (Real.sqrt (max (qbar u - q u) 0))^d else 0) := by
    apply Filter.Eventually.of_forall; intro u
    show (if qbar u ≤ 1 then (Real.sqrt (max (qbar u - ε) 0))^d else 0)
      ≤ (if qbar u ≤ 1 then (Real.sqrt (max (qbar u - q u) 0))^d else 0)
    by_cases h : qbar u ≤ 1
    · rw [if_pos h, if_pos h]
      exact pow_le_pow_left₀ (Real.sqrt_nonneg (max (qbar u - ε) 0))
        (Real.sqrt_le_sqrt (max_le_max (by linarith [hqε u h]) le_rfl)) d
    · rw [if_neg h, if_neg h]
  have h := integral_mono_of_nonneg hnn hG2 hle
  rwa [qbar_int_shift d hd ε hε hε1] at h

/-! ## The intended estimate (integral outside the subtraction) -/

theorem EstimateMuStrong {ι : Type*} [Fintype ι] (hN : 3 ≤ Fintype.card ι)
    (q : EuclideanSpace ℝ (Fin 2) → ℝ) (hqmeas : Measurable q) (ε : ℝ) (hε : 0 ≤ ε)
    (hq0 : ∀ u, qbar u ≤ 1 → 0 ≤ q u) (hqε : ∀ u, qbar u ≤ 1 → q u ≤ ε) :
    |(∫ u, (if qbar u ≤ 1 then
        (Real.sqrt (max (1 - q u) 0)) ^ (Fintype.card ι - 2) -
          (Real.sqrt (max (qbar u - q u) 0)) ^ (Fintype.card ι - 2) else 0))
      - 4 * ((Fintype.card ι : ℝ) - 2) / (Fintype.card ι : ℝ)| ≤
      100 * ((Fintype.card ι : ℝ) + 2) * (4 * ((Fintype.card ι : ℝ) - 2) / (Fintype.card ι : ℝ)) *
        min 1 ε := by
  set d := Fintype.card ι - 2 with hd
  have hd1 : 1 ≤ d := by omega
  have hcard2 : 2 ≤ Fintype.card ι := by omega
  have hNcast : (Fintype.card ι : ℝ) = (d : ℝ) + 2 := by
    rw [hd, Nat.cast_sub hcard2]; ring
  set A1 := ∫ u, (if qbar u ≤ 1 then (Real.sqrt (max (1 - q u) 0))^d else 0) with hA1
  set A2 := ∫ u, (if qbar u ≤ 1 then (Real.sqrt (max (qbar u - q u) 0))^d else 0) with hA2
  have hA1ub : A1 ≤ 4 := by rw [hA1]; exact qbar_G1_upper d q hqmeas hq0
  have hA2ub : A2 ≤ 8 / ((d:ℝ)+2) := by rw [hA2]; exact qbar_G2_upper d q hqmeas hq0
  have hA1nn : 0 ≤ A1 := by
    rw [hA1]
    refine integral_nonneg (fun u => ?_)
    simp only [Pi.zero_apply]
    by_cases h : qbar u ≤ 1
    · rw [if_pos h]; exact pow_nonneg (Real.sqrt_nonneg _) d
    · rw [if_neg h]
  have hA2nn : 0 ≤ A2 := by
    rw [hA2]
    refine integral_nonneg (fun u => ?_)
    simp only [Pi.zero_apply]
    by_cases h : qbar u ≤ 1
    · rw [if_pos h]; exact pow_nonneg (Real.sqrt_nonneg _) d
    · rw [if_neg h]
  have hsplit : (∫ u, (if qbar u ≤ 1 then
        (Real.sqrt (max (1 - q u) 0)) ^ d -
          (Real.sqrt (max (qbar u - q u) 0)) ^ d else 0)) = A1 - A2 := by
    rw [show (fun u : EuclideanSpace ℝ (Fin 2) => (if qbar u ≤ 1 then
          (Real.sqrt (max (1 - q u) 0))^d - (Real.sqrt (max (qbar u - q u) 0))^d else 0))
        = fun u => (if qbar u ≤ 1 then (Real.sqrt (max (1 - q u) 0))^d else 0)
          - (if qbar u ≤ 1 then (Real.sqrt (max (qbar u - q u) 0))^d else 0) from by
      funext u; by_cases h : qbar u ≤ 1 <;> simp [h]]
    rw [MeasureTheory.integral_sub (integrable_G1 d q hqmeas hq0) (integrable_G2 d q hqmeas hq0),
        ← hA1, ← hA2]
  have hMeq : 4 * (d:ℝ) / ((d:ℝ) + 2) = 4 - 8 / ((d:ℝ) + 2) := by field_simp; try ring
  rw [hNcast, show ((d:ℝ) + 2 - 2) = (d:ℝ) from by ring,
      show ((d:ℝ) + 2 + 2) = (d:ℝ) + 4 from by ring, hsplit]
  have hdR : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd1
  have hC : (8:ℝ) ≤ 100 * ((d:ℝ) + 4) * (4 * (d:ℝ) / ((d:ℝ) + 2)) := by
    rw [← sub_nonneg]
    have hrew : (100:ℝ) * ((d:ℝ)+4) * (4*(d:ℝ)/((d:ℝ)+2)) - 8
        = (100*((d:ℝ)+4)*(4*(d:ℝ)) - 8*((d:ℝ)+2)) / ((d:ℝ)+2) := by field_simp; try ring
    rw [hrew]
    apply div_nonneg _ (by linarith)
    nlinarith [hdR]
  have hC' : (4:ℝ)*(d:ℝ) ≤ 100 * ((d:ℝ) + 4) * (4 * (d:ℝ) / ((d:ℝ) + 2)) := by
    have hd2pos : (0:ℝ) < (d:ℝ)+2 := by linarith
    have h1 : (1:ℝ) ≤ 100 * ((d:ℝ)+4) / ((d:ℝ)+2) := by
      rw [le_div_iff₀ hd2pos]; nlinarith [hdR]
    have h2 : (4:ℝ)*(d:ℝ) * 1 ≤ 4*(d:ℝ) * (100 * ((d:ℝ)+4) / ((d:ℝ)+2)) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : (4:ℝ)*(d:ℝ) * (100 * ((d:ℝ)+4) / ((d:ℝ)+2))
        = 100 * ((d:ℝ) + 4) * (4 * (d:ℝ) / ((d:ℝ) + 2)) := by field_simp; try ring
    linarith [h2, h3.le]
  by_cases hε1 : ε ≤ 1
  · have hA1lb : 4 * (Real.sqrt (1 - ε))^d ≤ A1 := by
      rw [hA1]
      have h := qbar_G1_lower d q hqmeas ε hq0 hqε
      rwa [max_eq_left (sub_nonneg.mpr hε1)] at h
    have hA2lb : 8 * (Real.sqrt (1 - ε))^(d+2) / ((d:ℝ)+2) ≤ A2 := by
      rw [hA2]; exact qbar_G2_lower d hd1 q hqmeas ε hε hε1 hq0 hqε
    rw [min_eq_right hε1]
    have hu_le : 1 - Real.sqrt (1 - ε) ≤ ε := by
      have h1 : 1 - ε ≤ Real.sqrt (1 - ε) := by
        rw [Real.le_sqrt (sub_nonneg.mpr hε1) (sub_nonneg.mpr hε1)]
        nlinarith
      linarith
    have hb1 : 1 - Real.sqrt (1 - ε)^(d+2) ≤ ((d:ℝ)+2) * (1 - Real.sqrt (1 - ε)) := by
      have h := one_add_mul_le_pow (a := Real.sqrt (1 - ε) - 1)
        (by linarith : (-2:ℝ) ≤ Real.sqrt (1 - ε) - 1) (d+2)
      have h2 : (1 + (Real.sqrt (1 - ε) - 1))^(d+2) = Real.sqrt (1 - ε)^(d+2) := by ring_nf
      rw [h2] at h
      have h3 : ((d+2 : ℕ) : ℝ) = (d:ℝ)+2 := by push_cast; ring
      rw [h3] at h
      linarith
    have hb2 : 1 - Real.sqrt (1 - ε)^d ≤ (d:ℝ) * (1 - Real.sqrt (1 - ε)) := by
      have h := one_add_mul_le_pow (a := Real.sqrt (1 - ε) - 1)
        (by linarith : (-2:ℝ) ≤ Real.sqrt (1 - ε) - 1) d
      have h2 : (1 + (Real.sqrt (1 - ε) - 1))^d = Real.sqrt (1 - ε)^d := by ring_nf
      rw [h2] at h
      linarith
    refine abs_le.mpr ⟨?_, ?_⟩
    · have hJ2 : 0 ≤ 8/((d:ℝ)+2) - A2 := by linarith [hA2ub]
      have h1 : (d:ℝ) * (1 - Real.sqrt (1 - ε)) ≤ (d:ℝ) * ε :=
        mul_le_mul_of_nonneg_left hu_le (by positivity)
      have h2 : (1:ℝ) - Real.sqrt (1 - ε)^d ≤ (d:ℝ) * ε := le_trans hb2 h1
      have h3 : (4:ℝ) * Real.sqrt (1 - ε)^d - 4 ≥ -4*(d:ℝ)*ε := by linarith
      have h4 : -(100 * ((d:ℝ) + 4) * (4 * (d:ℝ) / ((d:ℝ) + 2)) * ε) ≤ -4*(d:ℝ)*ε := by
        have h5 : (4:ℝ)*(d:ℝ)*ε ≤ 100 * ((d:ℝ) + 4) * (4 * (d:ℝ) / ((d:ℝ) + 2)) * ε := by
          nlinarith [hC', hε]
        linarith
      linarith [hMeq, hA1lb, h3, hJ2, h4]
    · have hJle : 8/((d:ℝ)+2) - 8*Real.sqrt (1 - ε)^(d+2)/((d:ℝ)+2) ≤ 8*ε := by
        have hrew : 8/((d:ℝ)+2) - 8*Real.sqrt (1 - ε)^(d+2)/((d:ℝ)+2)
            = (8/((d:ℝ)+2)) * (1 - Real.sqrt (1 - ε)^(d+2)) := by field_simp; try ring
        rw [hrew]
        calc (8/((d:ℝ)+2)) * (1 - Real.sqrt (1 - ε)^(d+2))
            ≤ (8/((d:ℝ)+2)) * (((d:ℝ)+2) * (1 - Real.sqrt (1 - ε))) :=
              mul_le_mul_of_nonneg_left hb1 (by positivity)
          _ = 8 * (1 - Real.sqrt (1 - ε)) := by field_simp; try ring
          _ ≤ 8 * ε := mul_le_mul_of_nonneg_left hu_le (by norm_num)
      have h2 : 8/((d:ℝ)+2) - A2 ≤ 8*ε := by linarith [hA2lb, hJle]
      have h3 : (8:ℝ) * ε ≤ 100 * ((d:ℝ) + 4) * (4 * (d:ℝ) / ((d:ℝ) + 2)) * ε :=
        mul_le_mul_of_nonneg_right hC hε
      linarith [hMeq, hA1ub, h2, h3]
  · have hε1' : 1 < ε := not_le.mp hε1
    rw [min_eq_left hε1'.le]
    have h8 : 8/((d:ℝ)+2) ≤ 4 := by
      rw [div_le_iff₀ (by linarith : (0:ℝ) < (d:ℝ)+2)]; linarith
    have hbound : |A1 - A2 - 4*(d:ℝ)/((d:ℝ)+2)| ≤ 8 := by
      rw [abs_le]; constructor <;> linarith [hMeq, hA1nn, hA2nn, hA1ub, hA2ub, h8]
    calc |A1 - A2 - 4*(d:ℝ)/((d:ℝ)+2)| ≤ 8 := hbound
      _ ≤ 100 * ((d:ℝ) + 4) * (4 * (d:ℝ) / ((d:ℝ) + 2)) * 1 := by rw [mul_one]; exact hC

/-! ## The requested statement

As explained at the top, here the constant `M = 4(N-2)/N` sits *inside* the integral, so the
integrand equals `-M ≠ 0` off the (finite measure) square; it is not integrable and the
Bochner integral is `0`, making the conclusion `0 ≤ RHS`. -/

theorem EstimateMu {ι : Type*} [Fintype ι] (hN : 3 ≤ Fintype.card ι)
    (q : EuclideanSpace ℝ (Fin 2) → ℝ) (hqmeas : Measurable q) (ε : ℝ) (hε : 0 ≤ ε)
    (hq0 : ∀ u, qbar u ≤ 1 → 0 ≤ q u) (hqε : ∀ u, qbar u ≤ 1 → q u ≤ ε) :
    |∫ u, (if qbar u ≤ 1 then
        (Real.sqrt (max (1 - q u) 0)) ^ (Fintype.card ι - 2) -
          (Real.sqrt (max (qbar u - q u) 0)) ^ (Fintype.card ι - 2) else 0)
      - 4 * ((Fintype.card ι : ℝ) - 2) / (Fintype.card ι : ℝ)| ≤
      100 * ((Fintype.card ι : ℝ) + 2) * (4 * ((Fintype.card ι : ℝ) - 2) / (Fintype.card ι : ℝ)) *
        min 1 ε := by
  have hMpos : 0 < 4 * ((Fintype.card ι : ℝ) - 2) / (Fintype.card ι : ℝ) := by
    have hc : (0:ℝ) < Fintype.card ι := by exact_mod_cast (by omega : 0 < Fintype.card ι)
    have h3 : (3:ℝ) ≤ Fintype.card ι := by exact_mod_cast hN
    exact div_pos (by linarith) hc
  have hGint : Integrable (fun u : EuclideanSpace ℝ (Fin 2) =>
      (if qbar u ≤ 1 then (Real.sqrt (max (1 - q u) 0)) ^ (Fintype.card ι - 2) -
        (Real.sqrt (max (qbar u - q u) 0)) ^ (Fintype.card ι - 2) else 0)) := by
    refine ((integrable_G1 (Fintype.card ι - 2) q hqmeas hq0).sub
      (integrable_G2 (Fintype.card ι - 2) q hqmeas hq0)).congr ?_
    apply Filter.Eventually.of_forall; intro u
    by_cases h : qbar u ≤ 1 <;> simp [h]
  have hzero : (∫ u, ((if qbar u ≤ 1 then
        (Real.sqrt (max (1 - q u) 0)) ^ (Fintype.card ι - 2) -
          (Real.sqrt (max (qbar u - q u) 0)) ^ (Fintype.card ι - 2) else 0)
        - 4 * ((Fintype.card ι : ℝ) - 2) / (Fintype.card ι : ℝ))) = 0 := by
    rw [integral_undef]
    intro hint
    have hconst : Integrable (fun _ : EuclideanSpace ℝ (Fin 2) =>
        -(4 * ((Fintype.card ι : ℝ) - 2) / (Fintype.card ι : ℝ))) volume := by
      refine (hint.sub hGint).congr ?_
      apply Filter.Eventually.of_forall; intro u
      simp only [Pi.sub_apply]; ring
    rw [integrable_const_iff] at hconst
    rcases hconst with h0 | hfin
    · linarith [hMpos]
    · have hlt := hfin.measure_univ_lt_top
      rw [volume_univ_fin2] at hlt
      exact absurd hlt (lt_irrefl ⊤)
  rw [hzero, abs_zero]
  have hm : 0 ≤ 4 * ((Fintype.card ι : ℝ) - 2) / (Fintype.card ι : ℝ) := le_of_lt hMpos
  have hmin : 0 ≤ min 1 ε := le_min (by norm_num) hε
  exact mul_nonneg (mul_nonneg (by positivity) hm) hmin

end Work.HP
