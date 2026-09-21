import Mathlib
import Submission.Work.Analysis.Abel.abel_inversion
import Submission.Work.Analysis.Abel.intervalIntegrable_invSqrt_mul_invSqrt_sub
import Submission.Commons.Analysis.Abel.volterra_double_integral

open MeasureTheory
open scoped Interval Topology

namespace Commons.Analysis.Radon

lemma integrableOn_weight_triangle_singular {x : ℝ} (hx : 0 < x) :
    MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => if p.1 ≤ p.2 then
        (Real.sqrt (p.2 - p.1))⁻¹ * (Real.sqrt (x - p.2))⁻¹ * (Real.sqrt p.1)⁻¹ else 0)
      (Set.uIoc 0 x ×ˢ Set.uIoc 0 x) := by
  let S : Set ℝ := Set.uIoc 0 x
  let μ : Measure ℝ := volume.restrict S
  let g : ℝ × ℝ → ℝ := fun p => if p.1 ≤ p.2 then
    (Real.sqrt (p.2 - p.1))⁻¹ * (Real.sqrt (x - p.2))⁻¹ * (Real.sqrt p.1)⁻¹ else 0
  have hS_meas : MeasurableSet S := by dsimp [S]; exact measurableSet_uIoc
  have h_ae_Ioo : ∀ᵐ t ∂μ, t ∈ Set.Ioo 0 x := by
    rw [ae_iff]
    change (volume.restrict S) {t | t ∉ Set.Ioo 0 x} = 0
    dsimp [S]
    rw [Set.uIoc_of_le (le_of_lt hx)]
    rw [Measure.restrict_apply (s := Set.Ioc 0 x) (t := {t | t ∉ Set.Ioo 0 x}) (ht := measurableSet_Ioo.compl)]
    have h_inter : {t : ℝ | t ∉ Set.Ioo 0 x} ∩ Set.Ioc 0 x = {x} := by
      ext t
      constructor
      · intro ht
        have htIoc : t ∈ Set.Ioc 0 x := ht.2
        have htnot : t ∉ Set.Ioo 0 x := ht.1
        have htle : t ≤ x := htIoc.2
        have ht0 : 0 < t := htIoc.1
        by_cases htx : t = x
        · exact htx
        · exfalso
          exact htnot ⟨ht0, lt_of_le_of_ne htle htx⟩
      · intro ht
        rw [Set.mem_singleton_iff] at ht
        subst t
        exact ⟨by simp, ⟨hx, le_rfl⟩⟩
    rw [h_inter]
    simp [measure_singleton]
  have hsqrt1 : Measurable (fun p : ℝ × ℝ => Real.sqrt (p.2 - p.1)) :=
    Real.continuous_sqrt.measurable.comp (measurable_snd.sub measurable_fst)
  have hsqrt2 : Measurable (fun p : ℝ × ℝ => Real.sqrt (x - p.2)) :=
    Real.continuous_sqrt.measurable.comp (measurable_const.sub measurable_snd)
  have hsqrt3 : Measurable (fun p : ℝ × ℝ => Real.sqrt p.1) :=
    Real.continuous_sqrt.measurable.comp measurable_fst
  have hg_measurable : Measurable g := by
    dsimp [g]
    exact Measurable.ite (measurableSet_le measurable_fst measurable_snd)
      (((Measurable.inv hsqrt1).mul (Measurable.inv hsqrt2)).mul (Measurable.inv hsqrt3))
      measurable_const
  have hg_meas : AEStronglyMeasurable g (μ.prod μ) := hg_measurable.aestronglyMeasurable
  have h_fib : ∀ᵐ t ∂μ, Integrable (fun v => g (t, v)) μ := by
    filter_upwards [h_ae_Ioo] with t ht
    have hint : IntervalIntegrable (fun v : ℝ =>
        (Real.sqrt (v - t))⁻¹ * (Real.sqrt (x - v))⁻¹) volume t x :=
      Commons.Analysis.Abel.intervalIntegrable_invSqrt_mul_invSqrt_sub ht.2
    have hint_const : IntervalIntegrable (fun v : ℝ =>
        (Real.sqrt t)⁻¹ * ((Real.sqrt (v - t))⁻¹ * (Real.sqrt (x - v))⁻¹)) volume t x :=
      hint.const_mul _
    have hintOn : MeasureTheory.IntegrableOn
        (fun v : ℝ => (Real.sqrt t)⁻¹ * ((Real.sqrt (v - t))⁻¹ * (Real.sqrt (x - v))⁻¹))
        (Set.Ioc t x) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.2.le).mp hint_const
    have hzero : MeasureTheory.IntegrableOn
        (fun v : ℝ => (Real.sqrt t)⁻¹ * ((Real.sqrt (v - t))⁻¹ * (Real.sqrt (x - v))⁻¹))
        (Set.Ioc (0:ℝ) t) := by
      refine MeasureTheory.integrableOn_zero.congr_fun ?_ measurableSet_Ioc
      intro v hv
      have hsqrt_zero : Real.sqrt (v - t) = 0 := Real.sqrt_eq_zero_of_nonpos (by linarith [hv.2])
      simp [hsqrt_zero]
    have h_union : MeasureTheory.IntegrableOn
        (fun v : ℝ => (Real.sqrt t)⁻¹ * ((Real.sqrt (v - t))⁻¹ * (Real.sqrt (x - v))⁻¹))
        (Set.Ioc (0:ℝ) t ∪ Set.Ioc t x) := hzero.union hintOn
    have h_set : Set.Ioc (0:ℝ) t ∪ Set.Ioc t x = Set.Ioc 0 x := by
      ext v
      constructor
      · intro hv
        rcases hv with hv | hv
        · exact ⟨hv.1, le_trans hv.2 ht.2.le⟩
        · exact ⟨lt_trans ht.1 hv.1, hv.2⟩
      · intro hv
        by_cases hvt : v ≤ t
        · left; exact ⟨hv.1, hvt⟩
        · right; exact ⟨lt_of_not_ge hvt, hv.2⟩
    have h_on_g : MeasureTheory.IntegrableOn (fun v : ℝ => g (t, v)) (Set.Ioc (0:ℝ) x) := by
      rw [← h_set]
      refine h_union.congr_fun ?_ (measurableSet_Ioc.union measurableSet_Ioc)
      intro v hv
      rcases hv with hv | hv
      · by_cases htv : t ≤ v
        · have hveq : v = t := le_antisymm hv.2 htv
          subst v
          dsimp [g]
          rw [if_pos le_rfl]
          simp
        · have hsqrt_zero : Real.sqrt (v - t) = 0 := Real.sqrt_eq_zero_of_nonpos (by linarith [hv.2])
          dsimp [g]
          rw [if_neg htv]
          simp [hsqrt_zero]
      · have htv : t ≤ v := le_of_lt hv.1
        dsimp [g]
        rw [if_pos htv]
        ring
    dsimp [μ, S]
    rw [Set.uIoc_of_le (le_of_lt hx)]
    exact h_on_g
  have h_int_x : Integrable (fun t : ℝ => ∫ v : ℝ, ‖g (t, v)‖ ∂μ) μ := by
    have hconst : Integrable (fun t : ℝ => Real.pi * (Real.sqrt t)⁻¹) μ := by
      have hbase : IntervalIntegrable (fun t : ℝ => (Real.sqrt t)⁻¹) volume (0:ℝ) x :=
        by simpa using Commons.Analysis.Abel.intervalIntegrable_invSqrt_sub (a := (0:ℝ)) (b := x) hx
      have hbaseOn : IntegrableOn (fun t : ℝ => (Real.sqrt t)⁻¹) (Set.Ioc 0 x) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le hx.le).mp hbase
      have hmulOn : IntegrableOn (fun t : ℝ => Real.pi * (Real.sqrt t)⁻¹) (Set.Ioc 0 x) :=
        hbaseOn.const_mul Real.pi
      dsimp [μ, S]
      rw [Set.uIoc_of_le (le_of_lt hx)]
      simpa [MeasureTheory.IntegrableOn, mul_comm] using hmulOn
    refine hconst.congr ?_
    filter_upwards [h_ae_Ioo] with t ht
    have hinner : (∫ v : ℝ, ‖g (t, v)‖ ∂μ) =
        (Real.sqrt t)⁻¹ * ∫ v in t..x, (Real.sqrt (v - t))⁻¹ * (Real.sqrt (x - v))⁻¹ := by
      let f : ℝ → ℝ := fun v => (Real.sqrt t)⁻¹ * ((Real.sqrt (v - t))⁻¹ * (Real.sqrt (x - v))⁻¹)
      have h_left : (∫ v : ℝ, ‖g (t, v)‖ ∂μ) =
          ∫ v in (0:ℝ)..x, (Set.Ici t).indicator f v := by
        dsimp [μ, S]
        rw [Set.uIoc_of_le (le_of_lt hx)]
        rw [intervalIntegral.integral_of_le (le_of_lt hx)]
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
        intro v hv
        by_cases htv : t ≤ v
        · have hnonneg : 0 ≤ (Real.sqrt (v - t))⁻¹ * (Real.sqrt (x - v))⁻¹ * (Real.sqrt t)⁻¹ := by
            positivity
          dsimp [g, f]
          rw [if_pos htv, Set.indicator_of_mem (Set.mem_Ici.mpr htv)]
          rw [abs_of_nonneg hnonneg]
          ring
        · have hnot : v ∉ Set.Ici t := by simpa [Set.mem_Ici] using htv
          dsimp [g, f]
          rw [if_neg htv, Set.indicator_of_notMem hnot]
          simp
      have h_ind := Commons.Analysis.Abel.intervalIntegral_indicator_ge (a := (0:ℝ)) (b := x) (c := t) ht.1 (le_of_lt ht.2) f
      calc
        (∫ v : ℝ, ‖g (t, v)‖ ∂μ)
            = ∫ v in (0:ℝ)..x, (Set.Ici t).indicator f v := h_left
        _ = ∫ v in t..x, f v := h_ind
        _ = (Real.sqrt t)⁻¹ * ∫ v in t..x, (Real.sqrt (v - t))⁻¹ * (Real.sqrt (x - v))⁻¹ := by
              dsimp [f]
              rw [intervalIntegral.integral_const_mul]
    rw [hinner]
    have hker : (∫ v in t..x, (Real.sqrt (v - t))⁻¹ * (Real.sqrt (x - v))⁻¹) = Real.pi := by
      rw [show (∫ v in t..x, (Real.sqrt (v - t))⁻¹ * (Real.sqrt (x - v))⁻¹)
          = ∫ v in t..x, (Real.sqrt (x - v))⁻¹ * (Real.sqrt (v - t))⁻¹ by
        apply intervalIntegral.integral_congr
        intro v _
        ring]
      exact Commons.Analysis.Abel.integral_invSqrt_mul_invSqrt_sub (a := t) (b := x) ht.2
    rw [hker]
    ring
  have h_prod : Integrable g (μ.prod μ) :=
    (MeasureTheory.integrable_prod_iff (μ := μ) (ν := μ) hg_meas).2 ⟨h_fib, h_int_x⟩
  have h_on : IntegrableOn g (S ×ˢ S) := by
    change Integrable g ((volume.prod volume).restrict (S ×ˢ S))
    rw [← MeasureTheory.Measure.prod_restrict]
    exact h_prod
  simpa [g, S] using h_on


/-- **Integrability of the Abel triangle kernel with the singular profile
`t ↦ G (√t) / √t`.** -/
lemma integrableOn_abel_kernel_singular {G : ℝ → ℝ} {x : ℝ}
    (hx : 0 < x) (hx1 : x ≤ 1) (hG : ContinuousOn G (Set.Icc (0:ℝ) 1)) :
    MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => if p.1 ≤ p.2 then
        (Real.sqrt (p.2 - p.1))⁻¹ * (Real.sqrt (x - p.2))⁻¹ *
          (G (Real.sqrt p.1) / Real.sqrt p.1) else 0)
      (Set.uIoc 0 x ×ˢ Set.uIoc 0 x) := by
  rw [Set.uIoc_of_le hx.le]
  let S : Set (ℝ × ℝ) := Set.Ioc 0 x ×ˢ Set.Ioc 0 x
  let W : ℝ × ℝ → ℝ := fun p => if p.1 ≤ p.2 then
    (Real.sqrt (p.2 - p.1))⁻¹ * (Real.sqrt (x - p.2))⁻¹ * (Real.sqrt p.1)⁻¹ else 0
  let K : ℝ × ℝ → ℝ := fun p => if p.1 ≤ p.2 then
    (Real.sqrt (p.2 - p.1))⁻¹ * (Real.sqrt (x - p.2))⁻¹ *
      (G (Real.sqrt p.1) / Real.sqrt p.1) else 0
  have hW_int : IntegrableOn W S := by
    dsimp [W, S]
    simpa [Set.uIoc_of_le hx.le] using integrableOn_weight_triangle_singular hx
  have hG_bound : ∃ C, ∀ t ∈ Set.Icc (0:ℝ) x, ‖G (Real.sqrt t)‖ ≤ C := by
    have hcomp : ContinuousOn (fun t : ℝ => G (Real.sqrt t)) (Set.Icc (0:ℝ) x) := by
      apply hG.comp Real.continuous_sqrt.continuousOn
      intro t ht
      have ht0 : 0 ≤ t := ht.1
      have htx : t ≤ x := ht.2
      have hsqrt_nonneg : 0 ≤ Real.sqrt t := Real.sqrt_nonneg _
      have hsqrt_le : Real.sqrt t ≤ 1 := by
        calc Real.sqrt t ≤ Real.sqrt x := Real.sqrt_le_sqrt htx
          _ ≤ 1 := by
              rw [← Real.sqrt_one]
              exact Real.sqrt_le_sqrt hx1
      exact ⟨hsqrt_nonneg, hsqrt_le⟩
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcomp.norm
    exact ⟨C, fun t ht => by simpa using hC t ht⟩
  obtain ⟨C, hC⟩ := hG_bound
  have hCW_int : Integrable (fun p : ℝ × ℝ => C * W p) (volume.restrict S) := by
    have h := hW_int.const_mul C
    simpa [MeasureTheory.IntegrableOn, mul_comm] using h
  have hG_sqrt_cont : ContinuousOn (fun p : ℝ × ℝ => G (Real.sqrt p.1)) S := by
    have hsqrt_cont : ContinuousOn (fun p : ℝ × ℝ => Real.sqrt p.1) S := by
      apply Real.continuous_sqrt.continuousOn.comp continuous_fst.continuousOn
      intro p hp
      exact le_of_lt hp.1.1
    refine hG.comp hsqrt_cont ?_
    intro p hp
    have hp1_pos : 0 < p.1 := hp.1.1
    have hp1_le_x : p.1 ≤ x := hp.1.2
    have hsqrt_le_one : Real.sqrt p.1 ≤ 1 := by
      calc Real.sqrt p.1 ≤ Real.sqrt x := Real.sqrt_le_sqrt hp1_le_x
        _ ≤ 1 := by
            rw [← Real.sqrt_one]
            exact Real.sqrt_le_sqrt hx1
    exact ⟨Real.sqrt_nonneg _, hsqrt_le_one⟩
  have hG_sqrt_meas : AEStronglyMeasurable (fun p : ℝ × ℝ => G (Real.sqrt p.1)) (volume.restrict S) :=
    hG_sqrt_cont.aestronglyMeasurable (measurableSet_Ioc.prod measurableSet_Ioc)
  have hK_meas : AEStronglyMeasurable K (volume.restrict S) := by
    dsimp [K]
    have h1 : Measurable (fun p : ℝ × ℝ => Real.sqrt (p.2 - p.1)) :=
      Real.continuous_sqrt.measurable.comp (measurable_snd.sub measurable_fst)
    have h2 : Measurable (fun p : ℝ × ℝ => Real.sqrt (x - p.2)) :=
      Real.continuous_sqrt.measurable.comp (measurable_const.sub measurable_snd)
    have h4 : Measurable (fun p : ℝ × ℝ => Real.sqrt p.1) :=
      Real.continuous_sqrt.measurable.comp measurable_fst
    have hprod : AEStronglyMeasurable
        (fun p : ℝ × ℝ => (Real.sqrt (p.2 - p.1))⁻¹ * (Real.sqrt (x - p.2))⁻¹ *
          (G (Real.sqrt p.1) / Real.sqrt p.1)) (volume.restrict S) :=
      ((h1.inv).mul (h2.inv)).aestronglyMeasurable.mul (hG_sqrt_meas.mul h4.inv.aestronglyMeasurable)
    have h_ind : AEStronglyMeasurable
        ({p : ℝ × ℝ | p.1 ≤ p.2}.indicator
          (fun p => (Real.sqrt (p.2 - p.1))⁻¹ * (Real.sqrt (x - p.2))⁻¹ *
            (G (Real.sqrt p.1) / Real.sqrt p.1))) (volume.restrict S) :=
      hprod.indicator (measurableSet_le measurable_fst measurable_snd)
    convert h_ind using 1
    ext p
    by_cases hle : p.1 ≤ p.2
    · simp [Set.indicator, hle]
    · simp [Set.indicator, hle]

  have hK_bound : ∀ᵐ p : ℝ × ℝ ∂(volume.restrict S), ‖K p‖ ≤ C * W p := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
    have hp1 : p.1 ∈ Set.Icc (0:ℝ) x := ⟨le_of_lt hp.1.1, hp.1.2⟩
    have hgC : ‖G (Real.sqrt p.1)‖ ≤ C := hC p.1 hp1
    dsimp [K, W]
    by_cases hle : p.1 ≤ p.2
    · have h1 : 0 ≤ (Real.sqrt (p.2 - p.1))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
      have h2 : 0 ≤ (Real.sqrt (x - p.2))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
      have h3 : 0 ≤ (Real.sqrt p.1)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
      rw [if_pos hle]
      have hnorm : ‖(Real.sqrt (p.2 - p.1))⁻¹ * (Real.sqrt (x - p.2))⁻¹ *
            (G (Real.sqrt p.1) / Real.sqrt p.1)‖ ≤
          (Real.sqrt (p.2 - p.1))⁻¹ * (Real.sqrt (x - p.2))⁻¹ * (Real.sqrt p.1)⁻¹ * C := by
        calc
          ‖(Real.sqrt (p.2 - p.1))⁻¹ * (Real.sqrt (x - p.2))⁻¹ *
              (G (Real.sqrt p.1) / Real.sqrt p.1)‖
              = (Real.sqrt (p.2 - p.1))⁻¹ * (Real.sqrt (x - p.2))⁻¹ *
                  ‖G (Real.sqrt p.1) / Real.sqrt p.1‖ := by
                simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg h1, abs_of_nonneg h2]
          _ = (Real.sqrt (p.2 - p.1))⁻¹ * (Real.sqrt (x - p.2))⁻¹ *
                  (‖G (Real.sqrt p.1)‖ / ‖Real.sqrt p.1‖) := by
                rw [norm_div]
          _ = (Real.sqrt (p.2 - p.1))⁻¹ * (Real.sqrt (x - p.2))⁻¹ *
                  (‖G (Real.sqrt p.1)‖ * (Real.sqrt p.1)⁻¹) := by
                rw [Real.norm_of_nonneg (Real.sqrt_nonneg p.1)]
                ring
          _ ≤ (Real.sqrt (p.2 - p.1))⁻¹ * (Real.sqrt (x - p.2))⁻¹ * (C * (Real.sqrt p.1)⁻¹) := by
                gcongr
          _ = (Real.sqrt (p.2 - p.1))⁻¹ * (Real.sqrt (x - p.2))⁻¹ * (Real.sqrt p.1)⁻¹ * C := by ring
      calc
        ‖(Real.sqrt (p.2 - p.1))⁻¹ * (Real.sqrt (x - p.2))⁻¹ *
            (G (Real.sqrt p.1) / Real.sqrt p.1)‖
            ≤ (Real.sqrt (p.2 - p.1))⁻¹ * (Real.sqrt (x - p.2))⁻¹ * (Real.sqrt p.1)⁻¹ * C := hnorm
        _ = C * ((Real.sqrt (p.2 - p.1))⁻¹ * (Real.sqrt (x - p.2))⁻¹ * (Real.sqrt p.1)⁻¹) := by ring
      rw [if_pos hle]
    · simp [W, K, hle]
  have hK_int : Integrable K (volume.restrict S) :=
    Integrable.mono' hCW_int hK_meas hK_bound
  dsimp [K, S] at hK_int
  exact hK_int

end Commons.Analysis.Radon
