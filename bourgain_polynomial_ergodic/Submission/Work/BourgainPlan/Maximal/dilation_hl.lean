import Mathlib
import Submission.Commons.Analysis.HardyLittlewood.lintegral_convolution_radial_decreasing_measurable_le_hlMax
import Submission.Commons.Analysis.Maximal.lintegral_rpow_hlMax_le
import Submission.Commons.Analysis.HardyLittlewood.left_tail_maximal_nat

/-!
# Bourgain §7.1 for pure-power dilations of every degree

Bourgain's *Pointwise ergodic theorems for arithmetic sets* (IHÉS 69, 1989), §7.1, Lemma 7.16,
asserts the real-variable maximal inequality

`‖ sup_N |f * ν_N| ‖_{L^p(ℝ)} ≤ C_p ‖f‖_{L^p(ℝ)}`   (7.17)

for `ν_N` = image of `N⁻¹ dy` on `[0,N]` under the polynomial `p`, and proves it from the
Hardy–Littlewood maximal theorem.  In the *smooth-window* form in which §7.2 consumes it, the
statement becomes a domination of the Hardy–Littlewood maximal function `hlMax`, uniformly in `N`.

The commons proves the case `p = y²` (`Commons.Analysis.ExponentialSums.quadratic_kernel_real_maximal_le_hlMax`,
and the `s`-form in `model721`), where the substitution `u = t s²` and the explicit kernel
`(2√u)⁻¹` are used.  This file proves it for **every pure power** `p = y^d`, `d ≥ 1`, i.e.

  `∫_{(0,1]} g (x − t s^d) ds ≤ C · hlMax g x`,   `t = N^d`,  `N ≥ 1`,

by (i) the change of variables `u = t s^d` (the `d`-generalisation of
`lintegral_Ioc_sq_dilation`), and (ii) the published radial-kernel comparison
`Commons.Analysis.HardyLittlewood.lintegral_convolution_radial_decreasing_measurable_le_hlMax`
applied to the even, radially non-increasing kernel `u ↦ |u|^{1/d−1} 1_{|u|<t}`
(non-increasing because `1/d − 1 ≤ 0`).

This is the analytic core of Bourgain's Lemma 7.20 (§7.2) for the pure powers `X^d`, `d ≥ 3`, which
the commons does not have (there only the Fresnel / quadratic case `d = 2` is available).
-/

open MeasureTheory Set
open scoped ENNReal

set_option linter.unusedTactic false

namespace Work.BourgainPlan.Maximal

open Commons.Analysis.Maximal (hlMax)

/-! ## 1. The change of variables `u = t s^d` -/

/-- The image of `(0,1]` under `s ↦ t s^d` is `(0,t]` (for `t > 0`, `d ≥ 1`). -/
lemma image_pow_Ioc {t : ℝ} (ht : 0 < t) {d : ℕ} (hd : 0 < d) :
    (fun s : ℝ => t * s ^ d) '' Set.Ioc (0:ℝ) 1 = Set.Ioc (0:ℝ) t := by
  ext u
  constructor
  · rintro ⟨s, ⟨hs0, hs1⟩, rfl⟩
    refine ⟨mul_pos ht (pow_pos hs0 d), ?_⟩
    calc t * s ^ d ≤ t * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ (n := d) hs0.le hs1) ht.le
      _ = t := mul_one t
  · rintro ⟨hu0, hut⟩
    have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
    have hdiv : 0 < u / t := div_pos hu0 ht
    refine ⟨(u / t) ^ ((d:ℝ)⁻¹), ⟨Real.rpow_pos_of_pos hdiv _, ?_⟩, ?_⟩
    · exact Real.rpow_le_one hdiv.le ((div_le_one ht).mpr hut) (by positivity)
    · show t * ((u / t) ^ ((d:ℝ)⁻¹)) ^ d = u
      rw [← Real.rpow_natCast ((u / t) ^ ((d:ℝ)⁻¹)) d, ← Real.rpow_mul hdiv.le,
        inv_mul_cancel₀ (ne_of_gt hdR), Real.rpow_one]
      field_simp

/-- **The change of variables `u = t s^d` in the lower Lebesgue integral.**  For `t > 0`, `d ≥ 1`
and any `g : ℝ → ℝ≥0∞`,

`∫_{(0,t]} g u · u^{1/d−1} du = d · t^{1/d} · ∫_{(0,1]} g (t s^d) ds`.

This is the `d`-generalisation of `Commons.Analysis.ExponentialSums.lintegral_Ioc_sq_dilation`
(`d = 2`), and is used below with `t = N^d`. -/
theorem lintegral_Ioc_rpow_dilation {t : ℝ} (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (g : ℝ → ℝ≥0∞) :
    ∫⁻ u in Set.Ioc (0:ℝ) t, g u * ENNReal.ofReal (u ^ ((d:ℝ)⁻¹ - 1))
      = ENNReal.ofReal ((d:ℝ) * t ^ ((d:ℝ)⁻¹)) *
          ∫⁻ s in Set.Ioc (0:ℝ) 1, g (t * s ^ d) := by
  have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  have hs : MeasurableSet (Set.Ioc (0:ℝ) 1) := measurableSet_Ioc
  have hderiv : ∀ x ∈ Set.Ioc (0:ℝ) 1,
      HasDerivWithinAt (fun s : ℝ => t * s ^ d) ((d:ℝ) * t * x ^ (d - 1))
        (Set.Ioc (0:ℝ) 1) x := by
    intro x _
    have h : HasDerivAt (fun s : ℝ => s ^ d) ((d:ℝ) * x ^ (d - 1)) x := by
      simpa using hasDerivAt_pow (n := d) x
    have h2 : HasDerivAt (fun s : ℝ => t * s ^ d) (t * ((d:ℝ) * x ^ (d - 1))) x :=
      h.const_mul t
    have he : t * ((d:ℝ) * x ^ (d - 1)) = (d:ℝ) * t * x ^ (d - 1) := by ring
    rw [he] at h2
    exact h2.hasDerivWithinAt
  have hinj : Set.InjOn (fun s : ℝ => t * s ^ d) (Set.Ioc (0:ℝ) 1) := by
    intro a ha b hb hab
    have hda : a ^ d = b ^ d := mul_left_cancel₀ (ne_of_gt ht) hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have h := pow_lt_pow_left₀ hlt ha.1.le hd.ne'
      rw [hda] at h
      exact lt_irrefl _ h
    · have h := pow_lt_pow_left₀ hlt hb.1.le hd.ne'
      rw [← hda] at h
      exact lt_irrefl _ h
  have hchange := lintegral_image_eq_lintegral_abs_deriv_mul (s := Set.Ioc (0:ℝ) 1) hs hderiv
    hinj (fun u => g u * ENNReal.ofReal (u ^ ((d:ℝ)⁻¹ - 1)))
  rw [image_pow_Ioc ht hd] at hchange
  rw [hchange]
  have key : ∀ x ∈ Set.Ioc (0:ℝ) 1,
      ENNReal.ofReal (|(d:ℝ) * t * x ^ (d - 1)|)
          * ENNReal.ofReal ((t * x ^ d) ^ ((d:ℝ)⁻¹ - 1))
        = ENNReal.ofReal ((d:ℝ) * t ^ ((d:ℝ)⁻¹)) := by
    intro x hx
    have hx0 : 0 < x := hx.1
    rw [← ENNReal.ofReal_mul (abs_nonneg _)]
    congr 1
    have habs : |(d:ℝ) * t * x ^ (d - 1)| = (d:ℝ) * t * x ^ (d - 1) := by
      rw [abs_of_nonneg]; positivity
    rw [habs]
    have hxd : (t * x ^ d) ^ ((d:ℝ)⁻¹ - 1)
        = t ^ ((d:ℝ)⁻¹ - 1) * x ^ ((d:ℝ) * ((d:ℝ)⁻¹ - 1)) := by
      rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast x d,
        ← Real.rpow_mul hx0.le]
    rw [hxd]
    have hxd2 : (d:ℝ) * ((d:ℝ)⁻¹ - 1) = 1 - (d:ℝ) := by
      rw [mul_sub, mul_inv_cancel₀ (ne_of_gt hdR)]
      ring
    rw [hxd2]
    have hxpow : x ^ (d - 1) = x ^ ((d:ℝ) - 1) := by
      rw [← Real.rpow_natCast x (d - 1), Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
    rw [hxpow]
    have hx1 : x ^ ((d:ℝ) - 1) * x ^ (1 - (d:ℝ)) = 1 := by
      rw [← Real.rpow_add hx0]
      have h0 : (d:ℝ) - 1 + (1 - (d:ℝ)) = 0 := by ring
      rw [h0, Real.rpow_zero]
    have ht1 : t * t ^ ((d:ℝ)⁻¹ - 1) = t ^ ((d:ℝ)⁻¹) := by
      nth_rewrite 1 [← Real.rpow_one t]
      rw [← Real.rpow_add ht]
      congr 1
      ring
    calc (d:ℝ) * t * x ^ ((d:ℝ) - 1) * (t ^ ((d:ℝ)⁻¹ - 1) * x ^ (1 - (d:ℝ)))
        = ((d:ℝ) * (x ^ ((d:ℝ) - 1) * x ^ (1 - (d:ℝ)))) * (t * t ^ ((d:ℝ)⁻¹ - 1)) := by
          ring
      _ = ((d:ℝ) * 1) * t ^ ((d:ℝ)⁻¹) := by rw [hx1, ht1]
      _ = (d:ℝ) * t ^ ((d:ℝ)⁻¹) := by ring
  have hpt : ∀ x ∈ Set.Ioc (0:ℝ) 1,
      ENNReal.ofReal (|(d:ℝ) * t * x ^ (d - 1)|)
          * (g (t * x ^ d) * ENNReal.ofReal ((t * x ^ d) ^ ((d:ℝ)⁻¹ - 1)))
        = ENNReal.ofReal ((d:ℝ) * t ^ ((d:ℝ)⁻¹)) * g (t * x ^ d) := by
    intro x hx
    rw [mul_comm (g (t * x ^ d)) (ENNReal.ofReal ((t * x ^ d) ^ ((d:ℝ)⁻¹ - 1))),
      ← mul_assoc, key x hx]
  calc ∫⁻ x in Set.Ioc (0:ℝ) 1,
        ENNReal.ofReal (|(d:ℝ) * t * x ^ (d - 1)|)
          * (g (t * x ^ d) * ENNReal.ofReal ((t * x ^ d) ^ ((d:ℝ)⁻¹ - 1)))
      = ∫⁻ x in Set.Ioc (0:ℝ) 1, ENNReal.ofReal ((d:ℝ) * t ^ ((d:ℝ)⁻¹)) * g (t * x ^ d) :=
        setLIntegral_congr_fun measurableSet_Ioc hpt
    _ = ENNReal.ofReal ((d:ℝ) * t ^ ((d:ℝ)⁻¹))
          * ∫⁻ x in Set.Ioc (0:ℝ) 1, g (t * x ^ d) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- The total mass identity underlying the dilation: `∫_{(0,t]} u^{1/d−1} du = d t^{1/d}`. -/
lemma lintegral_Ioc_rpow_sub_one {t : ℝ} (ht : 0 < t) {d : ℕ} (hd : 0 < d) :
    ∫⁻ u in Set.Ioc (0:ℝ) t, ENNReal.ofReal (u ^ ((d:ℝ)⁻¹ - 1))
      = ENNReal.ofReal ((d:ℝ) * t ^ ((d:ℝ)⁻¹)) := by
  have h := lintegral_Ioc_rpow_dilation ht hd (fun _ : ℝ => (1 : ℝ≥0∞))
  simpa using h



/-! ## 2. The even radial weight `|v|^{1/d−1}` on `{|v| ≤ t}` -/

/-- Reversal of the Lebesgue integral on `ℝ`: `∫⁻ y, F (x − y) = ∫⁻ y, F y`. -/
lemma lintegral_comp_sub_left (F : ℝ → ℝ≥0∞) (hF : Measurable F) (x : ℝ) :
    ∫⁻ y, F (x - y) = ∫⁻ y, F y := by
  have h := MeasureTheory.lintegral_map (μ := (volume : Measure ℝ)) (f := F)
    (g := fun t : ℝ => x - t) hF (measurable_const.sub measurable_id)
  rw [MeasureTheory.Measure.map_sub_left_eq_self volume x] at h
  exact h.symm

/-- The even, radially non-increasing weight `|v|^{1/d−1}` cut to `|v| ≤ t`. -/
noncomputable def purePowerKernel (d : ℕ) (t v : ℝ) : ℝ≥0∞ :=
  if |v| ≤ t then (ENNReal.ofReal |v|) ^ ((d:ℝ)⁻¹ - 1) else 0

lemma purePowerKernel_symm (d : ℕ) (t v : ℝ) :
    purePowerKernel d t (-v) = purePowerKernel d t v := by
  simp only [purePowerKernel, abs_neg]

lemma purePowerKernel_antitone (d : ℕ) (hd : 0 < d) (t : ℝ) :
    ∀ x y : ℝ, 0 ≤ x → x ≤ y → purePowerKernel d t y ≤ purePowerKernel d t x := by
  have h1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have h2 : ((d:ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
  have hr : ((d:ℝ)⁻¹ - 1) ≤ 0 := by linarith
  intro x y hx hxy
  have hxabs : |x| = x := abs_of_nonneg hx
  have hyabs : |y| = y := abs_of_nonneg (hx.trans hxy)
  have hle : |x| ≤ |y| := by rw [hxabs, hyabs]; exact hxy
  simp only [purePowerKernel]
  by_cases hy : |y| ≤ t
  · rw [if_pos hy, if_pos (hle.trans hy)]
    rcases eq_or_lt_of_le hx with h | h
    · subst h
      rw [abs_zero, ENNReal.ofReal_zero]
      rcases lt_or_eq_of_le hr with hr' | hr'
      · rw [ENNReal.zero_rpow_of_neg hr']; exact le_top
      · rw [hr', ENNReal.rpow_zero, ENNReal.rpow_zero]
    · have hy0 : 0 < y := lt_of_lt_of_le h hxy
      rw [hxabs, hyabs, ENNReal.ofReal_rpow_of_pos h, ENNReal.ofReal_rpow_of_pos hy0]
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos h hxy hr)
  · rw [if_neg hy]; exact bot_le

/-! ### The value of the integrals -/

lemma setLIntegral_Ioi_purePowerKernel (d : ℕ) (hd : 0 < d) {t : ℝ} (ht : 0 < t) :
    ∫⁻ v in Set.Ioi (0:ℝ), purePowerKernel d t v
      = ENNReal.ofReal ((d:ℝ) * t ^ ((d:ℝ)⁻¹)) := by
  have hcongr : ∫⁻ v in Set.Ioi (0:ℝ), purePowerKernel d t v
      = ∫⁻ v in Set.Ioi (0:ℝ),
          (Set.Ioc (0:ℝ) t).indicator (fun v : ℝ => ENNReal.ofReal (v ^ ((d:ℝ)⁻¹ - 1))) v := by
    apply lintegral_congr_ae
    show ∀ᵐ v ∂volume.restrict (Set.Ioi (0:ℝ)), purePowerKernel d t v
      = (Set.Ioc (0:ℝ) t).indicator (fun v : ℝ => ENNReal.ofReal (v ^ ((d:ℝ)⁻¹ - 1))) v
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with v hv
    have hv0 : 0 < v := hv
    have hvabs : |v| = v := abs_of_pos hv0
    by_cases hvt : v ≤ t
    · rw [purePowerKernel, if_pos (by rw [hvabs]; exact hvt), hvabs,
        Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hv0, hvt⟩), ENNReal.ofReal_rpow_of_pos hv0]
    · rw [purePowerKernel, if_neg (by rw [hvabs]; exact hvt),
        Set.indicator_of_notMem (fun hc => hvt (Set.mem_Ioc.mp hc).2)]
  rw [hcongr, Commons.Analysis.HardyLittlewood.setLIntegral_indicator_eq_inter measurableSet_Ioc]
  rw [show Set.Ioi (0:ℝ) ∩ Set.Ioc (0:ℝ) t = Set.Ioc (0:ℝ) t by
    ext x; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ioc]; tauto]
  exact lintegral_Ioc_rpow_sub_one ht hd

lemma setLIntegral_Iio_purePowerKernel (d : ℕ) (t : ℝ) :
    ∫⁻ v in Set.Iio (0:ℝ), purePowerKernel d t v
      = ∫⁻ v in Set.Ioi (0:ℝ), purePowerKernel d t v := by
  have hstep : ∫⁻ v in Set.Iio (0:ℝ), purePowerKernel d t v
      = ∫⁻ v, (Set.Iio (0:ℝ)).indicator (purePowerKernel d t) v :=
    (lintegral_indicator measurableSet_Iio _).symm
  rw [hstep, ← MeasureTheory.lintegral_neg_eq_self
    (fun v : ℝ => (Set.Iio (0:ℝ)).indicator (purePowerKernel d t) v),
    ← lintegral_indicator measurableSet_Ioi (purePowerKernel d t)]
  apply lintegral_congr
  intro v
  by_cases hv : 0 < v
  · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hv),
      Set.indicator_of_mem (show -v ∈ Set.Iio (0:ℝ) by simp only [Set.mem_Iio]; linarith),
      purePowerKernel_symm]
  · rw [Set.indicator_of_notMem (fun hc => hv (Set.mem_Ioi.mp hc)),
      Set.indicator_of_notMem (show -v ∉ Set.Iio (0:ℝ) by simp only [Set.mem_Iio]; linarith)]

lemma lintegral_purePowerKernel (d : ℕ) (hd : 0 < d) {t : ℝ} (ht : 0 < t) :
    ∫⁻ v, purePowerKernel d t v
      = ENNReal.ofReal (2 * ((d:ℝ) * t ^ ((d:ℝ)⁻¹))) := by
  have hpos := setLIntegral_Ioi_purePowerKernel d hd ht
  have hsplit := lintegral_add_compl (μ := volume) (A := Set.Ioi (0:ℝ)) (purePowerKernel d t)
    (measurableSet_Ioi : MeasurableSet (Set.Ioi (0:ℝ)))
  have hcompl : ∫⁻ v in (Set.Ioi (0:ℝ))ᶜ, purePowerKernel d t v
      = ∫⁻ v in Set.Ioi (0:ℝ), purePowerKernel d t v := by
    have hset : (Set.Ioi (0:ℝ))ᶜ = Set.Iio (0:ℝ) ∪ {0} := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_Ioi, Set.mem_union, Set.mem_Iio,
        Set.mem_singleton_iff]
      exact ⟨fun h => lt_or_eq_of_le (le_of_not_gt h), by
        rintro (h | h) <;> linarith⟩
    rw [hset, lintegral_union (measurableSet_singleton 0) (by
      rw [Set.disjoint_left]; intro a ha hb
      rw [Set.mem_singleton_iff] at hb; rw [hb] at ha
      exact absurd ha (by simp)), setLIntegral_measure_zero ({0} : Set ℝ)
        (purePowerKernel d t) (Real.volume_singleton), add_zero,
      setLIntegral_Iio_purePowerKernel]
  rw [hcompl, hpos] at hsplit
  rw [← hsplit, ← ENNReal.ofReal_add (by positivity : (0:ℝ) ≤ (d:ℝ) * t ^ ((d:ℝ)⁻¹))
    (by positivity : (0:ℝ) ≤ (d:ℝ) * t ^ ((d:ℝ)⁻¹))]
  congr 1
  ring

/-! ## 3. The dilation bound and Bourgain (7.16)/(7.17) in the `s`-form -/

/-- **The weighted `u`-integral is dominated by the Hardy–Littlewood maximal function.** -/
theorem dilation_weight_le_hlMax (d : ℕ) (hd : 0 < d) (g : ℝ → ℝ≥0∞) (hg : Measurable g)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ∫⁻ u in Set.Ioc (0:ℝ) t, g (x - u) * ENNReal.ofReal (u ^ ((d:ℝ)⁻¹ - 1))
      ≤ ENNReal.ofReal (2 * ((d:ℝ) * t ^ ((d:ℝ)⁻¹))) * hlMax g x := by
  have hK_meas : Measurable (purePowerKernel d t) :=
    Commons.Analysis.HardyLittlewood.measurable_of_even_antitone_on_nonneg
      (purePowerKernel_symm d t) (purePowerKernel_antitone d hd t)
  have hcmp : ∫⁻ u in Set.Ioc (0:ℝ) t, g (x - u) * ENNReal.ofReal (u ^ ((d:ℝ)⁻¹ - 1))
      ≤ ∫⁻ v, g (x - v) * purePowerKernel d t v := by
    rw [← lintegral_indicator measurableSet_Ioc]
    refine lintegral_mono fun v => ?_
    by_cases hv : v ∈ Set.Ioc (0:ℝ) t
    · rw [Set.indicator_of_mem hv]
      congr 1
      rw [purePowerKernel, if_pos (by rw [abs_of_pos hv.1]; exact hv.2),
        abs_of_pos hv.1, ENNReal.ofReal_rpow_of_pos hv.1]
    · rw [Set.indicator_of_notMem hv]; exact bot_le
  have hrev : ∫⁻ v, g (x - v) * purePowerKernel d t v
      = ∫⁻ y, g y * purePowerKernel d t (x - y) := by
    have hF : Measurable (fun y : ℝ => g y * purePowerKernel d t (x - y)) :=
      hg.mul (hK_meas.comp (measurable_const.sub measurable_id))
    have h := lintegral_comp_sub_left (fun y : ℝ => g y * purePowerKernel d t (x - y)) hF x
    simpa using h
  refine le_trans hcmp ?_
  rw [hrev]
  have hrad := Commons.Analysis.HardyLittlewood.lintegral_convolution_radial_decreasing_measurable_le_hlMax
    (purePowerKernel d t) (purePowerKernel_symm d t) (purePowerKernel_antitone d hd t) g hg x
  rw [lintegral_purePowerKernel d hd ht] at hrad
  exact hrad

/-- **Bourgain (7.16)/(7.17) for a pure-power dilation, in the `s`-form.** -/
theorem purePower_dilation_le_hlMax {d : ℕ} (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : ℝ → ℝ≥0∞), Measurable g → ∀ (N : ℕ) (x : ℝ), 1 ≤ N →
      ∫⁻ s in Set.Ioc (0:ℝ) 1, g (x - (N:ℝ) ^ d * s ^ d)
        ≤ ENNReal.ofReal C * hlMax g x := by
  refine ⟨2, by norm_num, fun g hg N x hN => ?_⟩
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have ht : 0 < (N:ℝ) ^ d := pow_pos hNpos d
  have hsub := lintegral_Ioc_rpow_dilation (t := (N:ℝ) ^ d) ht hd (fun u => g (x - u))
  have hmain := dilation_weight_le_hlMax d hd g hg ht x
  have hval : ((N:ℝ) ^ d) ^ ((d:ℝ)⁻¹) = (N:ℝ) := by
    rw [← Real.rpow_natCast (N:ℝ) d, ← Real.rpow_mul hNpos.le]
    rw [mul_inv_cancel₀ (by positivity : ((d:ℝ)) ≠ 0), Real.rpow_one]
  have hconst : ENNReal.ofReal ((d:ℝ) * ((N:ℝ) ^ d) ^ ((d:ℝ)⁻¹))
      = ENNReal.ofReal ((d:ℝ) * (N:ℝ)) := by rw [hval]
  have hcpos : ENNReal.ofReal ((d:ℝ) * (N:ℝ)) ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]; positivity
  have hctop : ENNReal.ofReal ((d:ℝ) * (N:ℝ)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsub2 : ∫⁻ u in Set.Ioc (0:ℝ) ((N:ℝ) ^ d),
        g (x - u) * ENNReal.ofReal (u ^ ((d:ℝ)⁻¹ - 1))
      = ENNReal.ofReal ((d:ℝ) * (N:ℝ)) *
          ∫⁻ s in Set.Ioc (0:ℝ) 1, g (x - (N:ℝ) ^ d * s ^ d) := by
    rw [hsub, hconst]
  have hmain2 : ∫⁻ u in Set.Ioc (0:ℝ) ((N:ℝ) ^ d),
        g (x - u) * ENNReal.ofReal (u ^ ((d:ℝ)⁻¹ - 1))
      ≤ ENNReal.ofReal (2 * ((d:ℝ) * (N:ℝ))) * hlMax g x := by
    have harg : 2 * ((d:ℝ) * ((N:ℝ) ^ d) ^ ((d:ℝ)⁻¹)) = 2 * ((d:ℝ) * (N:ℝ)) := by rw [hval]
    rwa [harg] at hmain
  have hcancel : ∀ (c o H : ℝ≥0∞), c ≠ 0 → c ≠ ⊤ → c⁻¹ * ((o * c) * H) = o * H := by
    intro c o H hc0 hct
    rw [mul_comm o c, ← mul_assoc]
    congr 1
    rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]
  have hone : ∀ H : ℝ≥0∞, (ENNReal.ofReal ((d:ℝ) * (N:ℝ)))⁻¹ *
      (ENNReal.ofReal (2 * ((d:ℝ) * (N:ℝ))) * H) = ENNReal.ofReal 2 * H := by
    intro H
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    exact hcancel _ _ H hcpos hctop
  calc ∫⁻ s in Set.Ioc (0:ℝ) 1, g (x - (N:ℝ) ^ d * s ^ d)
      = (ENNReal.ofReal ((d:ℝ) * (N:ℝ)))⁻¹ *
          ∫⁻ u in Set.Ioc (0:ℝ) ((N:ℝ) ^ d),
            g (x - u) * ENNReal.ofReal (u ^ ((d:ℝ)⁻¹ - 1)) := by
        rw [hsub2, ← mul_assoc, ENNReal.inv_mul_cancel hcpos hctop, one_mul]
    _ ≤ (ENNReal.ofReal ((d:ℝ) * (N:ℝ)))⁻¹ *
          (ENNReal.ofReal (2 * ((d:ℝ) * (N:ℝ))) * hlMax g x) := mul_le_mul_right hmain2 _
    _ = ENNReal.ofReal 2 * hlMax g x := hone _
/-- **The sup over the dilation scales.**  For every `d ≥ 1` there is `C` with
`sup_N ∫_{(0,1]} g (x − (N+1)^d s^d) ds ≤ C · hlMax g x` for every measurable `g ≥ 0`. -/
theorem purePower_sup_le_hlMax {d : ℕ} (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ψ : ℝ → ℝ≥0∞), Measurable ψ → ∀ x : ℝ,
      (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0:ℝ) 1, ψ (x - ((N + 1 : ℕ) : ℝ) ^ d * s ^ d))
        ≤ ENNReal.ofReal C * hlMax ψ x := by
  obtain ⟨C, hC, hb⟩ := purePower_dilation_le_hlMax (d := d) hd
  exact ⟨C, hC, fun ψ hψ x => iSup_le fun N => hb ψ hψ (N + 1) x (by omega)⟩

/-- The `L^p` consequence of `purePower_sup_le_hlMax` (`p > 1`), via the Hardy–Littlewood
maximal theorem `Commons.Analysis.Maximal.lintegral_rpow_hlMax_le`. -/
theorem purePower_sup_lintegral_rpow_le {d : ℕ} (hd : 0 < d) {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ψ : ℝ → ℝ≥0∞), Measurable ψ → (∀ x, ψ x ≠ ⊤) →
      (∫⁻ x, ENNReal.rpow (ψ x) p < ⊤) →
      ∫⁻ x, ENNReal.rpow (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0:ℝ) 1,
          ψ (x - ((N + 1 : ℕ) : ℝ) ^ d * s ^ d)) p
        ≤ ENNReal.ofReal C * ∫⁻ x, ENNReal.rpow (ψ x) p := by
  obtain ⟨C₀, hC₀, hsup⟩ := purePower_sup_le_hlMax (d := d) hd
  have hp0 : (0:ℝ) ≤ p := le_of_lt (lt_trans zero_lt_one hp)
  set K : ℝ := 8 * p * 2 ^ (p - 1) / (p - 1) with hK
  have hKpos : 0 < K := by
    rw [hK]; positivity
  refine ⟨C₀ ^ p * K, by positivity, fun ψ hψ hψfin hH => ?_⟩
  calc ∫⁻ x, ENNReal.rpow (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0:ℝ) 1,
        ψ (x - ((N + 1 : ℕ) : ℝ) ^ d * s ^ d)) p
      ≤ ∫⁻ x, ENNReal.rpow (ENNReal.ofReal C₀ * hlMax ψ x) p :=
        lintegral_mono fun x => ENNReal.rpow_le_rpow (hsup ψ hψ x) hp0
    _ = ENNReal.ofReal (C₀ ^ p) * ∫⁻ x, ENNReal.rpow (hlMax ψ x) p := by
        have hC0top : ENNReal.ofReal C₀ ^ p ≠ ⊤ := by
          intro h
          rcases (ENNReal.rpow_eq_top_iff.mp h) with ⟨h1, _⟩ | ⟨h1, _⟩
          · exact absurd h1 (ENNReal.ofReal_pos.mpr hC₀).ne'
          · exact absurd h1 ENNReal.ofReal_ne_top
        rw [← ENNReal.ofReal_rpow_of_nonneg hC₀.le hp0]
        rw [show (fun x => ENNReal.rpow (ENNReal.ofReal C₀ * hlMax ψ x) p)
            = (fun x => ENNReal.ofReal C₀ ^ p * ENNReal.rpow (hlMax ψ x) p) from
          funext fun x => ENNReal.mul_rpow_of_nonneg _ _ hp0]
        exact lintegral_const_mul' _ _ hC0top
    _ ≤ ENNReal.ofReal (C₀ ^ p) *
        (ENNReal.ofReal K * ∫⁻ x, ENNReal.rpow (ψ x) p) :=
        mul_le_mul_right (by rw [hK]; exact Commons.Analysis.Maximal.lintegral_rpow_hlMax_le hψ hψfin hp hH) _
    _ = ENNReal.ofReal (C₀ ^ p * K) * ∫⁻ x, ENNReal.rpow (ψ x) p := by
        rw [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ C₀ ^ p), mul_assoc]

end Work.BourgainPlan.Maximal
