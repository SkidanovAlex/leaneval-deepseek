import Mathlib.Order.CompletePartialOrder
import Submission.Commons.Analysis.HardyLittlewood.left_tail_maximal_nat

open MeasureTheory Set Filter
open scoped ENNReal

namespace Commons.Analysis.Maximal

private lemma lintegral_Ioi_rpow_mul_indicator_Iio {r c : ℝ} (hr : -1 < r) (hc : 0 ≤ c) :
    ∫⁻ t in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (t ^ r) * (if t < c then (1 : ENNReal) else 0) ∂volume
      = ENNReal.ofReal (c ^ (r + 1) / (r + 1)) := by
  have hfun : (fun t : ℝ => ENNReal.ofReal (t ^ r) * (if t < c then (1:ENNReal) else 0))
      = (Set.Iio c).indicator (fun t : ℝ => ENNReal.ofReal (t ^ r)) := by
    funext t
    by_cases h : t < c
    · rw [Set.indicator_of_mem (show t ∈ Set.Iio c from h), if_pos h, mul_one]
    · rw [Set.indicator_of_notMem (show t ∉ Set.Iio c from h), if_neg h, mul_zero]
  rw [hfun, Commons.Analysis.HardyLittlewood.setLIntegral_indicator_eq_inter measurableSet_Iio]
  rw [show Set.Ioi (0:ℝ) ∩ Set.Iio c = Set.Ioo 0 c by
    ext x; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Iio, Set.mem_Ioo]]
  rw [Commons.Analysis.HardyLittlewood.lintegral_Ioo_rpow hr hc]

private lemma inner_value {p : ℝ} (hp : 2 < p) {c : ℝ} (hc : 0 ≤ c) :
    ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t ^ (p-3)) *
      (if t < c then (1:ENNReal) else 0) ∂volume
      = ENNReal.ofReal (c ^ (p-2) / (p-2)) := by
  have hr : -1 < p - 3 := by linarith
  rw [lintegral_Ioi_rpow_mul_indicator_Iio hr hc]
  rw [show (p - 3) + 1 = p - 2 by ring]

private lemma term_ident (p : ℝ) (hp : 2 < p) (x : ℝ) :
    ‖x‖ₑ ^ (2:ℝ) * ENNReal.ofReal ((2*|x|) ^ (p-2) / (p-2))
      = ENNReal.ofReal (2^(p-2)/(p-2)) * ‖x‖ₑ ^ p := by
  have hy : 0 ≤ |x| := abs_nonneg x
  have hx2 : ‖x‖ₑ ^ (2:ℝ) = ENNReal.ofReal (|x| ^ (2:ℝ)) := by
    rw [Real.enorm_eq_ofReal_abs,
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg x) (by norm_num)]
  have hxp : ‖x‖ₑ ^ p = ENNReal.ofReal (|x| ^ p) := by
    rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg x) (by linarith : (0:ℝ) ≤ p)]
  rw [hx2, hxp]
  have hmul : (2 * |x|) ^ (p - 2) = 2^(p-2) * |x|^(p-2) := by
    rw [Real.mul_rpow (by norm_num) hy]
  rw [hmul, ← ENNReal.ofReal_mul (Real.rpow_nonneg hy 2)]
  rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2^(p-2)/(p-2))]
  congr 1
  have hyadd : |x| ^ (2:ℝ) * |x| ^ (p-2) = |x| ^ p := by
    rw [← Real.rpow_add' hy (by linarith : (2:ℝ) + (p-2) ≠ 0)]
    ring_nf
  have hre : |x| ^ (2:ℝ) * (2 ^ (p - 2) * |x| ^ (p - 2) / (p - 2))
      = (|x| ^ (2:ℝ) * |x| ^ (p - 2)) * 2 ^ (p-2) / (p - 2) := by ring
  rw [hre, hyadd]; ring

private lemma real_ident {t p : ℝ} (ht : 0 < t) (hp : 2 < p) :
    ((t/2)^(2:ℝ))⁻¹ * t^(p-1) = 4 * t^(p-3) := by
  have h1 : (t/2)^(2:ℝ) = t^2/4 := by rw [Real.rpow_ofNat]; ring
  have h2 : (t^2)⁻¹ = t^(-(2:ℝ)) := by rw [← Real.rpow_ofNat, ← Real.rpow_neg ht.le]
  rw [h1, inv_div, show 4/(t^2) = 4 * t^(-(2:ℝ)) by rw [div_eq_mul_inv, h2]]
  rw [mul_assoc, ← Real.rpow_add ht (-(2:ℝ)) (p-1)]
  congr 1; ring

private lemma integral_tail_rpow_enorm_sq {p : ℝ} (hp : 2 < p) {f : ℕ → ℝ} {s : Finset ℕ}
    (hs : ∀ n ∉ s, f n = 0) :
    ∫⁻ t in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (t ^ (p - 3)) *
          (∫⁻ n, ‖(if t / 2 < |f n| then f n else (0:ℝ))‖ₑ ^ (2 : ℝ)
            ∂MeasureTheory.Measure.count) ∂volume
      = ENNReal.ofReal (2 ^ (p - 2) / (p - 2)) *
          ∫⁻ n, ‖f n‖ₑ ^ p ∂MeasureTheory.Measure.count := by
  have hinner : ∀ t : ℝ,
      (∫⁻ n, ‖(if t / 2 < |f n| then f n else (0:ℝ))‖ₑ ^ (2 : ℝ)
          ∂MeasureTheory.Measure.count)
        = ∑ n ∈ s, (if t / 2 < |f n| then ‖f n‖ₑ ^ (2:ℝ) else 0) := by
    intro t
    have hzero : ∀ n ∉ s,
        ‖(if t / 2 < |f n| then f n else (0:ℝ))‖ₑ ^ (2 : ℝ) = 0 := by
      intro n hn
      rw [hs n hn]; simp
    rw [MeasureTheory.lintegral_count, tsum_eq_sum (s := s) hzero]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases h : t / 2 < |f n|
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]; simp
  rw [show (fun t : ℝ => ENNReal.ofReal (t ^ (p - 3)) *
        (∫⁻ n, ‖(if t / 2 < |f n| then f n else (0:ℝ))‖ₑ ^ (2 : ℝ)
          ∂MeasureTheory.Measure.count))
      = (fun t : ℝ => ENNReal.ofReal (t ^ (p - 3)) *
        (∑ n ∈ s, (if t / 2 < |f n| then ‖f n‖ₑ ^ (2:ℝ) else 0))) from
    funext (fun t => by rw [hinner t])]
  simp_rw [Finset.mul_sum]
  rw [MeasureTheory.lintegral_finsetSum (μ := volume.restrict (Set.Ioi 0)) s (fun n hn => ?_)]
  swap
  · have h1 : Measurable (fun t : ℝ => ENNReal.ofReal (t ^ (p - 3))) := by fun_prop
    have h2 : Measurable (fun t : ℝ => (if t / 2 < |f n| then ‖f n‖ₑ ^ (2:ℝ) else 0)) := by
      have e : (fun t : ℝ => (if t / 2 < |f n| then ‖f n‖ₑ ^ (2:ℝ) else 0))
          = (Set.Iio (2*|f n|)).indicator (fun _ => ‖f n‖ₑ ^ (2:ℝ)) := by
        funext t
        by_cases h : t < 2*|f n|
        · rw [Set.indicator_of_mem (show t ∈ Set.Iio (2*|f n|) from h),
            if_pos (by linarith : t/2 < |f n|)]
        · rw [Set.indicator_of_notMem (show t ∉ Set.Iio (2*|f n|) from h),
            if_neg (by linarith : ¬ t/2 < |f n|)]
      rw [e]; exact measurable_const.indicator measurableSet_Iio
    exact h1.mul h2
  have hterm : ∀ n ∈ s,
      (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t ^ (p - 3)) *
        (if t / 2 < |f n| then ‖f n‖ₑ ^ (2:ℝ) else 0) ∂volume)
      = ‖f n‖ₑ ^ (2:ℝ) * ENNReal.ofReal ((2*|f n|) ^ (p-2) / (p-2)) := by
    intro n hn
    have hif : (fun t : ℝ => ENNReal.ofReal (t ^ (p - 3)) *
          (if t / 2 < |f n| then ‖f n‖ₑ ^ (2:ℝ) else 0))
        = (fun t : ℝ => ‖f n‖ₑ ^ (2:ℝ) * (ENNReal.ofReal (t ^ (p - 3)) *
          (if t < 2*|f n| then (1:ENNReal) else 0))) := by
      funext t
      by_cases h : t / 2 < |f n|
      · have h' : t < 2*|f n| := by linarith
        rw [if_pos h, if_pos h']; ring
      · have h' : ¬ t < 2*|f n| := by linarith
        rw [if_neg h, if_neg h']; ring
    rw [hif, MeasureTheory.lintegral_const_mul]
    · rw [inner_value hp (by positivity : (0:ℝ) ≤ 2*|f n|)]
    · have hm1 : Measurable (fun t : ℝ => ENNReal.ofReal (t ^ (p - 3))) := by fun_prop
      have hm2 : Measurable (fun t : ℝ => (if t < 2*|f n| then (1:ENNReal) else 0)) :=
        Measurable.ite measurableSet_Iio measurable_const measurable_const
      exact hm1.mul hm2
  have hfin : (∑ n ∈ s, ‖f n‖ₑ ^ p)
      = ∫⁻ n, ‖f n‖ₑ ^ p ∂MeasureTheory.Measure.count := by
    have hzero : ∀ n ∉ s, ‖f n‖ₑ ^ p = 0 := by
      intro n hn
      rw [hs n hn]
      simp [ENNReal.zero_rpow_of_pos (by linarith : (0:ℝ) < p)]
    rw [MeasureTheory.lintegral_count, tsum_eq_sum (s := s) hzero]
  rw [Finset.sum_congr rfl hterm, ← hfin]
  rw [Finset.sum_congr rfl (fun n hn => term_ident p hp (f n))]
  rw [← Finset.mul_sum]

private lemma sq_mul_meas_le_lintegral (g : ℕ → ENNReal) (ε : ENNReal) :
    ε ^ (2:ℝ) * Measure.count {n : ℕ | ε ≤ g n}
      ≤ ∫⁻ n, (g n) ^ (2:ℝ) ∂Measure.count := by
  have hle : Measure.count {n : ℕ | ε ≤ g n}
      ≤ Measure.count {n : ℕ | ε ^ (2:ℝ) ≤ (g n) ^ (2:ℝ)} :=
    MeasureTheory.measure_mono (fun n hn => ENNReal.rpow_le_rpow hn (by norm_num))
  have hcheb := MeasureTheory.mul_meas_ge_le_lintegral
    (μ := Measure.count) (f := fun n : ℕ => (g n) ^ (2:ℝ))
    (measurable_of_countable _) (ε ^ (2:ℝ))
  refine le_trans ?_ hcheb
  gcongr

private lemma hpt_aux {T : (ℕ → ℝ) → ℕ → ENNReal} {C : ℝ} (hC : 0 < C)
    (hsub : ∀ f h : ℕ → ℝ, T (f + h) ≤ T f + T h)
    (hunif : ∀ f : ℕ → ℝ, T f ≤ (fun n => ⨆ k, ‖f k‖ₑ))
    (hl2 : ∀ f : ℕ → ℝ, (∃ s : Finset ℕ, ∀ n, n ∉ s → f n = 0) →
      ∫⁻ n, (T f n) ^ (2 : ℝ) ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C ^ 2) * ∫⁻ n, (‖f n‖ₑ) ^ (2 : ℝ) ∂MeasureTheory.Measure.count)
    {p : ℝ} (hp : 2 < p) {f : ℕ → ℝ} {s : Finset ℕ} (hs : ∀ n ∉ s, f n = 0)
    (hTfin : ∀ a : ℕ, T f a ≠ ⊤) :
    ∀ t : ℝ, 0 < t →
      Measure.count {a : ℕ | t < (T f a).toReal} * ENNReal.ofReal (t ^ (p - 1))
        ≤ ENNReal.ofReal (4 * C^2) *
            (ENNReal.ofReal (t ^ (p - 3)) *
              ∫⁻ n, ‖(if t / 2 < |f n| then f n else (0:ℝ))‖ₑ ^ (2:ℝ)
                ∂MeasureTheory.Measure.count) := by
  intro t ht
  set fb : ℕ → ℝ := fun n => if t / 2 < |f n| then f n else 0 with hfbdef
  set fs : ℕ → ℝ := fun n => if |f n| ≤ t / 2 then f n else 0 with hfsdef
  have hfb_supp : ∀ n ∉ s, fb n = 0 := by
    intro n hn; simp only [fb]; rw [hs n hn]; simp
  have hfs_small : T fs ≤ (fun _ : ℕ => ENNReal.ofReal (t / 2)) := by
    refine (hunif fs).trans ?_
    intro n
    apply iSup_le; intro k
    simp only [fs]
    by_cases hk : |f k| ≤ t / 2
    · rw [if_pos hk, Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal hk
    · rw [if_neg hk]; simp
  have hsum : fb + fs = f := by
    funext n; simp only [Pi.add_apply, fb, fs]
    by_cases h : t / 2 < |f n|
    · rw [if_pos h, if_neg (by linarith : ¬ |f n| ≤ t/2)]; ring
    · rw [if_neg h, if_pos (by linarith : |f n| ≤ t/2)]; ring
  have hb : T f ≤ T fb + (fun _ : ℕ => ENNReal.ofReal (t / 2)) := by
    calc T f = T (fb + fs) := by rw [hsum]
      _ ≤ T fb + T fs := hsub fb fs
      _ ≤ T fb + (fun _ => ENNReal.ofReal (t/2)) := add_le_add le_rfl hfs_small
  have hcard : Measure.count {a : ℕ | t < (T f a).toReal}
      ≤ Measure.count {a : ℕ | ENNReal.ofReal (t/2) ≤ T fb a} := by
    apply MeasureTheory.measure_mono
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have h1 : ENNReal.ofReal t < T f a :=
      (ENNReal.ofReal_lt_iff_lt_toReal ht.le (hTfin a)).mpr ha
    have h3 : ENNReal.ofReal (t/2) + ENNReal.ofReal (t/2)
        < T fb a + ENNReal.ofReal (t/2) := by
      rw [← ENNReal.ofReal_add (by linarith) (by linarith), show t/2 + t/2 = t by ring]
      exact lt_of_lt_of_le h1 (hb a)
    exact ((ENNReal.add_lt_add_iff_right ENNReal.ofReal_ne_top).mp h3).le
  have hcheb := sq_mul_meas_le_lintegral (T fb) (ENNReal.ofReal (t/2))
  have hl2b : ∫⁻ n, (T fb n) ^ (2:ℝ) ∂Measure.count
      ≤ ENNReal.ofReal (C ^ 2) * ∫⁻ n, ‖fb n‖ₑ ^ (2:ℝ) ∂Measure.count :=
    hl2 fb ⟨s, hfb_supp⟩
  have hcf : (ENNReal.ofReal (t/2)) ^ (2:ℝ) * Measure.count {a : ℕ | t < (T f a).toReal}
      ≤ ENNReal.ofReal (C ^ 2) * ∫⁻ n, ‖fb n‖ₑ ^ (2:ℝ) ∂Measure.count := by
    calc (ENNReal.ofReal (t/2)) ^ (2:ℝ) * Measure.count {a : ℕ | t < (T f a).toReal}
        ≤ (ENNReal.ofReal (t/2)) ^ (2:ℝ)
            * Measure.count {a : ℕ | ENNReal.ofReal (t/2) ≤ T fb a} := by gcongr
      _ ≤ ∫⁻ n, (T fb n) ^ (2:ℝ) ∂Measure.count := hcheb
      _ ≤ ENNReal.ofReal (C ^ 2) * ∫⁻ n, ‖fb n‖ₑ ^ (2:ℝ) ∂Measure.count := hl2b
  have hA0 : (ENNReal.ofReal (t/2)) ^ (2:ℝ) ≠ 0 := by
    rw [ENNReal.ofReal_rpow_of_nonneg (by linarith) (by norm_num : (0:ℝ) ≤ 2)]
    exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hAt : (ENNReal.ofReal (t/2)) ^ (2:ℝ) ≠ ⊤ :=
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top).ne
  have hX : Measure.count {a : ℕ | t < (T f a).toReal}
      ≤ ((ENNReal.ofReal (t/2)) ^ (2:ℝ))⁻¹ *
          (ENNReal.ofReal (C ^ 2) * ∫⁻ n, ‖fb n‖ₑ ^ (2:ℝ) ∂Measure.count) := by
    calc Measure.count {a : ℕ | t < (T f a).toReal}
        = ((ENNReal.ofReal (t/2)) ^ (2:ℝ))⁻¹ * ((ENNReal.ofReal (t/2)) ^ (2:ℝ))
            * Measure.count {a : ℕ | t < (T f a).toReal} := by
          rw [ENNReal.inv_mul_cancel hA0 hAt, one_mul]
      _ = ((ENNReal.ofReal (t/2)) ^ (2:ℝ))⁻¹ *
            (((ENNReal.ofReal (t/2)) ^ (2:ℝ)) * Measure.count {a : ℕ | t < (T f a).toReal}) := by
          rw [mul_assoc]
      _ ≤ ((ENNReal.ofReal (t/2)) ^ (2:ℝ))⁻¹ *
            (ENNReal.ofReal (C ^ 2) * ∫⁻ n, ‖fb n‖ₑ ^ (2:ℝ) ∂Measure.count) := by gcongr
  have hAinv : ((ENNReal.ofReal (t/2)) ^ (2:ℝ))⁻¹ * ENNReal.ofReal (t ^ (p-1))
      = ENNReal.ofReal 4 * ENNReal.ofReal (t ^ (p-3)) := by
    have hpos : 0 < (t/2)^(2:ℝ) := Real.rpow_pos_of_pos (by linarith) _
    rw [ENNReal.ofReal_rpow_of_nonneg (by linarith : (0:ℝ) ≤ t/2) (by norm_num : (0:ℝ) ≤ 2)]
    rw [← ENNReal.ofReal_inv_of_pos hpos]
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hpos.le)]
    rw [real_ident ht hp]
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)]
  have hC4 : ENNReal.ofReal (C^2) * ENNReal.ofReal 4 = ENNReal.ofReal (4 * C^2) := by
    rw [mul_comm, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)]
  calc Measure.count {a : ℕ | t < (T f a).toReal} * ENNReal.ofReal (t ^ (p - 1))
      ≤ (((ENNReal.ofReal (t/2)) ^ (2:ℝ))⁻¹ *
          (ENNReal.ofReal (C ^ 2) * ∫⁻ n, ‖fb n‖ₑ ^ (2:ℝ) ∂Measure.count))
          * ENNReal.ofReal (t^(p-1)) := by gcongr
    _ = ENNReal.ofReal (4 * C^2) *
          (ENNReal.ofReal (t^(p-3)) * ∫⁻ n, ‖fb n‖ₑ ^ (2:ℝ) ∂Measure.count) := by
        rw [show ((((ENNReal.ofReal (t/2)) ^ (2:ℝ))⁻¹ *
              (ENNReal.ofReal (C ^ 2) * ∫⁻ n, ‖fb n‖ₑ ^ (2:ℝ) ∂Measure.count))
              * ENNReal.ofReal (t^(p-1)))
            = ENNReal.ofReal (C^2) * (∫⁻ n, ‖fb n‖ₑ ^ (2:ℝ) ∂Measure.count)
              * (((ENNReal.ofReal (t/2)) ^ (2:ℝ))⁻¹ * ENNReal.ofReal (t^(p-1))) by ring]
        rw [hAinv, ← hC4]
        ring


theorem lintegral_rpow_iSup_le_of_l2_linf {T : (ℕ → ℝ) → ℕ → ENNReal} {C : ℝ} (hC : 0 < C)
    (hT0 : T 0 = 0)
    (hsub : ∀ f h : ℕ → ℝ, T (f + h) ≤ T f + T h)
    (hmono : ∀ f h : ℕ → ℝ, (∀ n, |f n| ≤ |h n|) → T f ≤ T h)
    (hunif : ∀ f : ℕ → ℝ, T f ≤ (fun n => ⨆ k, ‖f k‖ₑ))
    (hl2 : ∀ f : ℕ → ℝ, (∃ s : Finset ℕ, ∀ n, n ∉ s → f n = 0) →
      ∫⁻ n, (T f n) ^ (2 : ℝ) ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C ^ 2) * ∫⁻ n, (‖f n‖ₑ) ^ (2 : ℝ) ∂MeasureTheory.Measure.count)
    {p : ℝ} (hp : 2 < p) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ f : ℕ → ℝ, (∃ s : Finset ℕ, ∀ n, n ∉ s → f n = 0) →
      ∫⁻ n, (T f n) ^ p ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C' ^ p) * ∫⁻ n, (‖f n‖ₑ) ^ p ∂MeasureTheory.Measure.count := by
  have hppos : 0 < p := by linarith
  have hp2 : 0 < p - 2 := by linarith
  have hKpos : 0 < p * (4 * C^2) * (2^(p-2)/(p-2)) :=
    mul_pos (mul_pos hppos (by positivity))
      (div_pos (Real.rpow_pos_of_pos (by norm_num) _) hp2)
  refine ⟨(p * (4 * C^2) * (2^(p-2)/(p-2)))^(1/p), Real.rpow_pos_of_pos hKpos _, ?_⟩
  intro f hf
  obtain ⟨s, hs⟩ := hf
  have hTfin : ∀ a : ℕ, T f a ≠ ⊤ := by
    intro a
    have hsup : (⨆ k, ‖f k‖ₑ) ≤ ENNReal.ofReal (∑ n ∈ s, |f n|) := by
      apply iSup_le; intro k
      by_cases hk : k ∈ s
      · rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal
          (Finset.single_le_sum (s := s) (f := fun i => |f i|) (fun i _ => abs_nonneg (f i)) hk)
      · rw [hs k hk]; simp
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((hunif f a).trans hsup)
  let G : ℕ → ℝ := fun n => (T f n).toReal
  have hGnn : 0 ≤ᵐ[Measure.count] G := Eventually.of_forall (fun n => ENNReal.toReal_nonneg)
  have hGmeas : AEMeasurable G Measure.count := (measurable_of_countable G).aemeasurable
  have hlc := MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul (μ := Measure.count)
    hGnn hGmeas hppos
  have hrewrite : (∫⁻ n, (T f n) ^ p ∂Measure.count)
      = ∫⁻ n, ENNReal.ofReal (G n ^ p) ∂Measure.count := by
    apply MeasureTheory.lintegral_congr; intro n
    have hGnonneg : 0 ≤ G n := by simp only [G]; exact ENNReal.toReal_nonneg
    have h2 : ENNReal.ofReal (G n) = T f n := by
      simp only [G]; exact ENNReal.ofReal_toReal (hTfin n)
    rw [← h2, ENNReal.ofReal_rpow_of_nonneg hGnonneg hppos.le]
  have hbound : (∫⁻ t in Set.Ioi (0:ℝ),
        Measure.count {a : ℕ | t < G a} * ENNReal.ofReal (t ^ (p - 1)) ∂volume)
      ≤ ENNReal.ofReal (4 * C^2) * (∫⁻ t in Set.Ioi (0:ℝ),
          ENNReal.ofReal (t ^ (p - 3)) *
            (∫⁻ n, ‖(if t / 2 < |f n| then f n else (0:ℝ))‖ₑ ^ (2:ℝ)
              ∂Measure.count) ∂volume) := by
    rw [← MeasureTheory.lintegral_const_mul' (ENNReal.ofReal (4*C^2)) _ ENNReal.ofReal_ne_top]
    apply MeasureTheory.lintegral_mono_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact hpt_aux hC hsub hunif hl2 hp hs hTfin t ht
  have hcomp := integral_tail_rpow_enorm_sq (s := s) hp hs
  have hC'p : ((p * (4 * C^2) * (2^(p-2)/(p-2)))^(1/p))^p = p * (4 * C^2) * (2^(p-2)/(p-2)) := by
    rw [← Real.rpow_mul (le_of_lt hKpos) (1/p) p]
    rw [show 1/p * p = 1 by field_simp, Real.rpow_one]
  calc ∫⁻ n, (T f n) ^ p ∂Measure.count
      = ∫⁻ n, ENNReal.ofReal (G n ^ p) ∂Measure.count := hrewrite
    _ = ENNReal.ofReal p * (∫⁻ t in Set.Ioi (0:ℝ),
          Measure.count {a : ℕ | t < G a} * ENNReal.ofReal (t ^ (p - 1)) ∂volume) := hlc
    _ ≤ ENNReal.ofReal p * (ENNReal.ofReal (4 * C^2) * (∫⁻ t in Set.Ioi (0:ℝ),
          ENNReal.ofReal (t ^ (p - 3)) * (∫⁻ n, ‖(if t / 2 < |f n| then f n else (0:ℝ))‖ₑ ^ (2:ℝ)
            ∂Measure.count) ∂volume)) := by gcongr
    _ = ENNReal.ofReal p * (ENNReal.ofReal (4 * C^2) *
          (ENNReal.ofReal (2^(p-2)/(p-2)) * ∫⁻ n, ‖f n‖ₑ ^ p ∂Measure.count)) := by rw [hcomp]
    _ = ENNReal.ofReal (p * (4 * C^2) * (2^(p-2)/(p-2))) * ∫⁻ n, ‖f n‖ₑ ^ p ∂Measure.count := by
        have e : ENNReal.ofReal p * (ENNReal.ofReal (4 * C^2) *
              (ENNReal.ofReal (2^(p-2)/(p-2)) * ∫⁻ n, ‖f n‖ₑ ^ p ∂Measure.count))
            = (ENNReal.ofReal p * ENNReal.ofReal (4 * C^2) * ENNReal.ofReal (2^(p-2)/(p-2)))
              * ∫⁻ n, ‖f n‖ₑ ^ p ∂Measure.count := by ring
        rw [e, ← ENNReal.ofReal_mul (le_of_lt hppos),
          ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ p * (4 * C^2))]
    _ = ENNReal.ofReal (((p * (4 * C^2) * (2^(p-2)/(p-2)))^(1/p))^p)
          * ∫⁻ n, ‖f n‖ₑ ^ p ∂Measure.count := by rw [hC'p]

end Commons.Analysis.Maximal