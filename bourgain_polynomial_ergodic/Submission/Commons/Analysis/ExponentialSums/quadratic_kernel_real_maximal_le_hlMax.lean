import Mathlib
import Submission.Commons.Analysis.HardyLittlewood.lintegral_convolution_radial_decreasing_measurable_le_hlMax
import Submission.Commons.Analysis.HardyLittlewood.left_tail_maximal_nat
import Submission.Commons.Analysis.Integral.lintegral_Ioc_ofReal_const_mul_rpow
import Submission.Commons.Analysis.Maximal.real_maximal_weak_type
import Submission.Commons.Analysis.Maximal.real_maximal_strong_type

namespace Commons.Analysis.ExponentialSums

open _root_.MeasureTheory Set Filter
open scoped ENNReal Topology

/-- The even, radially decreasing kernel `|v|^{-1/2}` truncated to `|v| ≤ N²`. -/
private noncomputable def qkr (N : ℝ) (v : ℝ) : ℝ≥0∞ :=
  if |v| ≤ N ^ 2 then (ENNReal.ofReal (Real.sqrt |v|))⁻¹ else 0

private lemma qkr_symm (N v : ℝ) : qkr N (-v) = qkr N v := by
  simp only [qkr, abs_neg]

private lemma qkr_zero (N : ℝ) : qkr N 0 = ⊤ := by
  rw [qkr]
  simp only [abs_zero]
  rw [if_pos (sq_nonneg N)]
  simp

private lemma qkr_apply_of_pos {N v : ℝ} (hN : |v| ≤ N^2) :
    qkr N v = (ENNReal.ofReal (Real.sqrt |v|))⁻¹ := by
  rw [qkr, if_pos hN]

private lemma qkr_antitone (N : ℝ) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    qkr N y ≤ qkr N x := by
  rcases eq_or_lt_of_le hx with h | h
  · subst h; rw [qkr_zero]; exact le_top
  · have hy : 0 < y := lt_of_lt_of_le h hxy
    by_cases hN : |y| ≤ N^2
    · have hxN : |x| ≤ N^2 := by
        have h1 : |x| = x := abs_of_nonneg hx
        have h2 : |y| = y := abs_of_pos hy
        rw [h2] at hN
        rw [h1]
        linarith
      rw [qkr_apply_of_pos hN, qkr_apply_of_pos hxN]
      refine ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt ?_))
      have h1 : |x| = x := abs_of_nonneg hx
      have h2 : |y| = y := abs_of_pos hy
      rw [h1, h2]; exact hxy
    · rw [qkr, if_neg hN]; exact bot_le

private lemma qkr_measurable (N : ℝ) : Measurable (qkr N) := by
  have h1 : Measurable (fun v : ℝ => ENNReal.ofReal (Real.sqrt |v|)) :=
    ENNReal.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp continuous_abs.measurable)
  have h2 : Measurable (fun v : ℝ => (ENNReal.ofReal (Real.sqrt |v|))⁻¹) := h1.inv
  have h3 : MeasurableSet {v : ℝ | |v| ≤ N^2} :=
    measurableSet_le continuous_abs.measurable measurable_const
  have heq : qkr N = {v : ℝ | |v| ≤ N^2}.indicator (fun v => (ENNReal.ofReal (Real.sqrt |v|))⁻¹) := by
    funext v
    rw [qkr, Set.indicator_apply]
    by_cases h : |v| ≤ N^2 <;> simp [h]
  rw [heq]
  exact h2.indicator h3

private lemma lintegral_qkr_pos (N : ℝ) (hN : 0 ≤ N) :
    ∫⁻ v in Set.Ioi 0, qkr N v = ENNReal.ofReal (2 * N) := by
  have hcongr : (∫⁻ v in Set.Ioi 0, qkr N v)
      = ∫⁻ v in Set.Ioi 0,
          (Set.Iic (N^2)).indicator (fun v => (ENNReal.ofReal (Real.sqrt v))⁻¹) v := by
    apply lintegral_congr_ae
    show ∀ᵐ v ∂volume.restrict (Set.Ioi 0),
      qkr N v = (Set.Iic (N^2)).indicator (fun v => (ENNReal.ofReal (Real.sqrt v))⁻¹) v
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with v hv
    have habs : |v| = v := abs_of_pos hv
    by_cases h : v ≤ N^2
    · rw [qkr, if_pos (by rw [habs]; exact h), Set.indicator_of_mem (Set.mem_Iic.mpr h), habs]
    · rw [qkr, if_neg (by rw [habs]; exact h),
        Set.indicator_of_notMem (fun hc => h (Set.mem_Iic.mp hc))]
  rw [hcongr, Commons.Analysis.HardyLittlewood.setLIntegral_indicator_eq_inter measurableSet_Iic]
  rw [show Set.Ioi (0:ℝ) ∩ Set.Iic (N^2) = Set.Ioc 0 (N^2) by
        ext x; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Iic, Set.mem_Ioc]]
  have hcongr2 : (∫⁻ v in Set.Ioc 0 (N^2), (ENNReal.ofReal (Real.sqrt v))⁻¹)
      = ∫⁻ v in Set.Ioc 0 (N^2), ENNReal.ofReal (v ^ (-(1/2 : ℝ))) := by
    apply lintegral_congr_ae
    show ∀ᵐ v ∂volume.restrict (Set.Ioc 0 (N^2)),
      (ENNReal.ofReal (Real.sqrt v))⁻¹ = ENNReal.ofReal (v ^ (-(1/2 : ℝ)))
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with v hv
    have hv0 : (0:ℝ) < v := hv.1
    have hpos : (0:ℝ) < v ^ (1/2:ℝ) := by
      rw [← Real.sqrt_eq_rpow]; exact Real.sqrt_pos.mpr hv0
    rw [Real.sqrt_eq_rpow v, Real.rpow_neg (le_of_lt hv0)]
    exact (ENNReal.ofReal_inv_of_pos hpos).symm
  rw [hcongr2]
  have hkey := Commons.Analysis.Integral.lintegral_Ioc_ofReal_const_mul_rpow (A := N^2) (c := 1)
      (sq_nonneg N) (by norm_num : (0:ℝ) ≤ 1) (r := -(1/2)) (by norm_num : (-1:ℝ) < -(1/2))
  simp only [one_mul] at hkey
  rw [hkey]
  congr 1
  rw [show -(1/2:ℝ) + 1 = 1/2 by norm_num,
      show (N^2) ^ (1/2:ℝ) = N by
        rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs, abs_of_nonneg hN]]
  ring

private lemma lintegral_qkr_le (N : ℝ) (hN : 0 ≤ N) :
    ∫⁻ v, qkr N v ≤ ENNReal.ofReal (4 * N) := by
  have hcompl : (∫⁻ v in (Set.Ioi (0:ℝ))ᶜ, qkr N v) = ∫⁻ v in Set.Iio 0, qkr N v := by
    have hset : (Set.Ioi (0:ℝ))ᶜ = Set.Iio 0 ∪ {0} := by
      ext x; simp only [Set.mem_compl_iff, Set.mem_Ioi, Set.mem_union, Set.mem_Iio,
        Set.mem_singleton_iff]
      exact ⟨fun h => lt_or_eq_of_le (le_of_not_gt h), fun h => by
        rcases h with h | h <;> linarith⟩
    rw [hset, lintegral_union (measurableSet_singleton 0) (by
      rw [Set.disjoint_left]; intro a ha hb; rw [Set.mem_singleton_iff] at hb
      rw [hb] at ha; exact absurd ha (by simp))]
    rw [setLIntegral_measure_zero ({0} : Set ℝ) (qkr N) Real.volume_singleton, add_zero]
  have hneg : (∫⁻ v in Set.Iio 0, qkr N v) = ∫⁻ v in Set.Ioi 0, qkr N v := by
    have h := (MeasureTheory.Measure.measurePreserving_neg (volume : Measure ℝ)).setLIntegral_comp_preimage
      (s := Set.Ioi 0) measurableSet_Ioi (f := qkr N) (qkr_measurable N)
    have hpre : Neg.neg ⁻¹' (Set.Ioi (0:ℝ)) = Set.Iio 0 := by
      ext x; simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_Iio, neg_pos]
    rw [hpre] at h
    calc (∫⁻ v in Set.Iio 0, qkr N v) = ∫⁻ v in Set.Iio 0, qkr N (-v) := by
          apply lintegral_congr; intro v; rw [qkr_symm]
      _ = ∫⁻ v in Set.Ioi 0, qkr N v := h
  have hsum : (∫⁻ v, qkr N v)
      = (∫⁻ v in Set.Ioi 0, qkr N v) + ∫⁻ v in Set.Iio 0, qkr N v := by
    rw [(lintegral_add_compl (qkr N) measurableSet_Ioi).symm, hcompl]
  have h2 : (∫⁻ v in Set.Ioi 0, qkr N v) + (∫⁻ v in Set.Ioi 0, qkr N v)
      = ENNReal.ofReal (2 * N) + ENNReal.ofReal (2 * N) := by
    nth_rw 1 [lintegral_qkr_pos N hN]
    nth_rw 1 [lintegral_qkr_pos N hN]
  have htotal : (∫⁻ v, qkr N v) = ENNReal.ofReal (4 * N) := by
    rw [hsum, hneg, h2,
      ← ENNReal.ofReal_add (by linarith : (0:ℝ) ≤ 2 * N) (by linarith : (0:ℝ) ≤ 2 * N)]
    congr 1; ring
  exact le_of_eq htotal

theorem quadratic_kernel_real_maximal_le_hlMax :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℝ → ℝ), Measurable f → (∀ y, 0 ≤ f y) → ∀ x : ℝ,
      (⨆ N : ℝ, ENNReal.ofReal ((2 * N)⁻¹) *
          ∫⁻ u in Set.Ioc (0 : ℝ) (N ^ 2),
            ENNReal.ofReal (f (x - u)) * ENNReal.ofReal ((Real.sqrt u)⁻¹))
        ≤ ENNReal.ofReal C * Commons.Analysis.Maximal.hlMax (fun y : ℝ => ENNReal.ofReal (f y)) x := by
  refine ⟨2, by norm_num, ?_⟩
  intro f hf hfnn x
  refine iSup_le fun N => ?_
  by_cases hNle : N ≤ 0
  · have hz : ENNReal.ofReal ((2 * N)⁻¹) = 0 :=
      ENNReal.ofReal_of_nonpos (inv_nonpos.mpr (by linarith))
    rw [hz, zero_mul]
    exact bot_le
  · replace hNle := not_le.mp hNle
    have hI : (∫⁻ u in Set.Ioc (0:ℝ) (N^2),
          ENNReal.ofReal (f (x - u)) * ENNReal.ofReal ((Real.sqrt u)⁻¹))
        ≤ ENNReal.ofReal (4 * N)
            * Commons.Analysis.Maximal.hlMax (fun y : ℝ => ENNReal.ofReal (f y)) x := by
      have hFmeas : Measurable (fun u : ℝ => ENNReal.ofReal (f (x - u)) * qkr N u) :=
        ((hf.ennreal_ofReal).comp (continuous_const.sub continuous_id).measurable).mul
          (qkr_measurable N)
      have hstep1 : (∫⁻ u in Set.Ioc (0:ℝ) (N^2),
            ENNReal.ofReal (f (x - u)) * ENNReal.ofReal ((Real.sqrt u)⁻¹))
          = ∫⁻ u in Set.Ioc (0:ℝ) (N^2),
            ENNReal.ofReal (f (x - u)) * qkr N u := by
        apply lintegral_congr_ae
        show ∀ᵐ u ∂volume.restrict (Set.Ioc 0 (N^2)),
          ENNReal.ofReal (f (x - u)) * ENNReal.ofReal ((Real.sqrt u)⁻¹)
            = ENNReal.ofReal (f (x - u)) * qkr N u
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
        filter_upwards with u hu
        have hu0 : 0 < u := hu.1
        have huN : |u| ≤ N^2 := by rw [abs_of_pos hu0]; exact hu.2
        rw [qkr_apply_of_pos huN, abs_of_pos hu0]
        congr 1
        exact ENNReal.ofReal_inv_of_pos (Real.sqrt_pos.mpr hu0)
      have hstep2 : (∫⁻ u in Set.Ioc (0:ℝ) (N^2),
            ENNReal.ofReal (f (x - u)) * qkr N u)
          = ∫⁻ y in Set.Ico (x - N^2) x, ENNReal.ofReal (f y) * qkr N (x - y) := by
        have hmp : MeasurePreserving (fun y : ℝ => x - y) volume volume := by
          have h1 : (fun y : ℝ => x - y) = fun y : ℝ => x + (-y) := by funext y; ring
          rw [h1]
          exact (MeasureTheory.measurePreserving_add_left volume x).comp
            (MeasureTheory.Measure.measurePreserving_neg volume)
        have hpre : (fun y : ℝ => x - y) ⁻¹' (Set.Ioc 0 (N^2)) = Set.Ico (x - N^2) x := by
          ext y; simp only [Set.mem_preimage, Set.mem_Ioc, Set.mem_Ico]
          constructor <;> intro h <;> exact ⟨by linarith [h.1], by linarith [h.2]⟩
        have hkey := hmp.setLIntegral_comp_preimage (s := Set.Ioc 0 (N^2)) measurableSet_Ioc
          (f := fun u : ℝ => ENNReal.ofReal (f (x - u)) * qkr N u) hFmeas
        rw [hpre] at hkey
        rw [← hkey]
        apply lintegral_congr
        intro y
        show ENNReal.ofReal (f (x - (x - y))) * qkr N (x - y) = ENNReal.ofReal (f y) * qkr N (x - y)
        rw [show x - (x - y) = y by ring]
      have hstep3 : (∫⁻ y in Set.Ico (x - N^2) x, ENNReal.ofReal (f y) * qkr N (x - y))
          ≤ ∫⁻ y, ENNReal.ofReal (f y) * qkr N (x - y) := by
        simpa using lintegral_mono_set (Set.subset_univ (Set.Ico (x - N^2) x))
          (f := fun y : ℝ => ENNReal.ofReal (f y) * qkr N (x - y))
      have hstep4 := Commons.Analysis.HardyLittlewood.lintegral_convolution_radial_decreasing_measurable_le_hlMax
        (qkr N) (qkr_symm N) (fun a b ha hab => qkr_antitone N ha hab) (fun y : ℝ => ENNReal.ofReal (f y))
        (hf.ennreal_ofReal) x
      have hstep5 : (∫⁻ z, qkr N z) ≤ ENNReal.ofReal (4 * N) := lintegral_qkr_le N (le_of_lt hNle)
      calc (∫⁻ u in Set.Ioc (0:ℝ) (N^2),
              ENNReal.ofReal (f (x - u)) * ENNReal.ofReal ((Real.sqrt u)⁻¹))
          = ∫⁻ u in Set.Ioc (0:ℝ) (N^2), ENNReal.ofReal (f (x - u)) * qkr N u := hstep1
        _ = ∫⁻ y in Set.Ico (x - N^2) x, ENNReal.ofReal (f y) * qkr N (x - y) := hstep2
        _ ≤ ∫⁻ y, ENNReal.ofReal (f y) * qkr N (x - y) := hstep3
        _ ≤ (∫⁻ z, qkr N z) * Commons.Analysis.Maximal.hlMax (fun y : ℝ => ENNReal.ofReal (f y)) x :=
              hstep4
        _ ≤ ENNReal.ofReal (4 * N) * Commons.Analysis.Maximal.hlMax (fun y : ℝ => ENNReal.ofReal (f y)) x := by
              gcongr
    calc ENNReal.ofReal ((2 * N)⁻¹) *
            (∫⁻ u in Set.Ioc (0:ℝ) (N^2),
              ENNReal.ofReal (f (x - u)) * ENNReal.ofReal ((Real.sqrt u)⁻¹))
        ≤ ENNReal.ofReal ((2 * N)⁻¹) *
            (ENNReal.ofReal (4 * N) *
              Commons.Analysis.Maximal.hlMax (fun y : ℝ => ENNReal.ofReal (f y)) x) := by
          gcongr
      _ = ENNReal.ofReal 2 * Commons.Analysis.Maximal.hlMax (fun y : ℝ => ENNReal.ofReal (f y)) x := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (2 * N)⁻¹)]
          congr 1
          have hval : (2 * N)⁻¹ * (4 * N) = 2 := by
            field_simp
            ring
          rw [hval]

end Commons.Analysis.ExponentialSums
