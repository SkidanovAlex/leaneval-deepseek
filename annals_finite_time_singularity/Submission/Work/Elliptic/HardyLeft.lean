import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.Interval.Basic
import Mathlib.Topology.Separation.CompletelyRegular

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
open scoped Interval Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

private lemma lintegral_Ioo_le_of_seq
    (X : ℝ → ℝ) (hXm : AEMeasurable X volume)
    {C : ℝ} (hC : 0 ≤ C) (g : ℝ → ℝ)
    (hg : Tendsto (fun n : ℕ => g (1 / ((n:ℝ) + 2))) atTop (𝓝 0))
    (hbound : ∀ n : ℕ, ∫⁻ z in Set.Ioo (1 / ((n:ℝ) + 2)) 1, ENNReal.ofReal (X z)
      ≤ ENNReal.ofReal (C + g (1 / ((n:ℝ) + 2)))) :
    ∫⁻ z in Set.Ioo (0:ℝ) 1, ENNReal.ofReal (X z) ≤ ENNReal.ofReal C := by
  set e : ℕ → ℝ := fun n => 1 / ((n:ℝ) + 2) with he
  have he0 : ∀ n, 0 < e n := fun n => by rw [he]; positivity
  have he1 : ∀ n, e n < 1 := by
    intro n; rw [he, div_lt_one (by positivity)]
    have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    linarith
  have heanti : Antitone e := by
    intro m n hmn
    rw [he]
    apply one_div_le_one_div_of_le (by positivity)
    have : (m:ℝ) ≤ (n:ℝ) := by exact_mod_cast hmn
    linarith
  have hetend0 : Tendsto e atTop (𝓝 (0:ℝ)) := by
    rw [he]
    have hg2 : Tendsto (fun n : ℕ => ((n:ℝ) + 2)) atTop atTop := by
      have h := (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 2)
      have h2 : (fun n : ℕ => ((n:ℝ) + 2)) = (fun n : ℕ => ((n + 2 : ℕ) : ℝ)) := by
        funext n; push_cast; ring
      rw [h2]; exact h
    exact (tendsto_const_nhds (x := (1:ℝ))).div_atTop hg2
  set F : ℝ → ENNReal := (Set.Ioo (0:ℝ) 1).indicator (fun z => ENNReal.ofReal (X z)) with hFdef
  set f : ℕ → ℝ → ENNReal := fun n => (Set.Ioo (e n) 1).indicator (fun z => ENNReal.ofReal (X z)) with hf
  have hfmeas : ∀ n, AEMeasurable (f n) volume :=
    fun n => (hXm.ennreal_ofReal).indicator measurableSet_Ioo
  have hmono : ∀ᵐ z ∂volume, Monotone fun n => f n z := by
    apply Eventually.of_forall
    intro z m n hmn
    simp only [hf]
    by_cases hz : z ∈ Set.Ioo (e m) 1
    · have hz' : z ∈ Set.Ioo (e n) 1 := ⟨lt_of_le_of_lt (heanti hmn) hz.1, hz.2⟩
      rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz']
    · rw [Set.indicator_of_notMem hz]; exact bot_le
  have htend : ∀ᵐ z ∂volume, Tendsto (fun n => f n z) atTop (𝓝 (F z)) := by
    apply Eventually.of_forall
    intro z
    by_cases hz : z ∈ Set.Ioo (0:ℝ) 1
    · have hFz : F z = ENNReal.ofReal (X z) := by
        simp only [hFdef, Set.indicator_of_mem hz]
      rw [hFz]
      have hev : ∀ᶠ n in atTop, z ∈ Set.Ioo (e n) 1 := by
        have hlt : ∀ᶠ n in atTop, e n < z := hetend0.eventually (Iio_mem_nhds hz.1)
        filter_upwards [hlt] with n hn
        exact ⟨hn, hz.2⟩
      refine tendsto_nhds_of_eventually_eq ?_
      filter_upwards [hev] with n hn
      simp only [hf, Set.indicator_of_mem hn]
    · have hFz : F z = 0 := by
        simp only [hFdef, Set.indicator_of_notMem hz]
      rw [hFz]
      have hzero : ∀ᶠ n in atTop, f n z = 0 := by
        apply Eventually.of_forall
        intro n; simp only [hf]; rw [Set.indicator_of_notMem]
        intro hmem; exact hz ⟨lt_trans (he0 n) hmem.1, hmem.2⟩
      exact tendsto_nhds_of_eventually_eq hzero
  have hconv := lintegral_tendsto_of_tendsto_of_monotone hfmeas hmono htend
  have hfn : ∀ n, ∫⁻ z, f n z ∂volume = ∫⁻ z in Set.Ioo (e n) 1, ENNReal.ofReal (X z) := by
    intro n
    rw [hf]
    rw [lintegral_indicator measurableSet_Ioo]
  have hgtend : Tendsto (fun n => ENNReal.ofReal (C + g (e n))) atTop (𝓝 (ENNReal.ofReal C)) := by
    have hg' : Tendsto (fun n => g (e n)) atTop (𝓝 0) := by rw [he]; exact hg
    have : Tendsto (fun n => C + g (e n)) atTop (𝓝 (C + 0)) := tendsto_const_nhds.add hg'
    simpa using ENNReal.tendsto_ofReal this
  have hle : ∀ n, ∫⁻ z, f n z ∂volume ≤ ENNReal.ofReal (C + g (e n)) := by
    intro n
    rw [hfn n]
    exact hbound n
  have hmain := le_of_tendsto_of_tendsto' hconv hgtend hle
  have hFint : ∫⁻ z in Set.Ioo (0:ℝ) 1, ENNReal.ofReal (X z) = ∫⁻ z, F z ∂volume := by
    rw [hFdef]
    rw [lintegral_indicator measurableSet_Ioo]
  rw [hFint]
  exact hmain

private lemma deriv_meas (U U' : ℝ → ℝ)
    (hderiv : ∀ z ∈ Set.Ioo (0:ℝ) 1, HasDerivAt U (U' z) z) :
    AEStronglyMeasurable U' (volume.restrict (Set.Ioo (0:ℝ) 1)) := by
  have h1 : AEStronglyMeasurable (deriv U) (volume.restrict (Set.Ioo (0:ℝ) 1)) :=
    (aemeasurable_deriv U (volume.restrict (Set.Ioo (0:ℝ) 1))).aestronglyMeasurable
  refine (aestronglyMeasurable_congr ?_).mp h1
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
  exact (hderiv z hz).deriv

private lemma deriv_sq_integrable (U U' : ℝ → ℝ)
    (hderiv : ∀ z ∈ Set.Ioo (0:ℝ) 1, HasDerivAt U (U' z) z)
    (hint : IntegrableOn (fun z => U' z ^ 2 / z ^ 2) (Set.Ioo (0:ℝ) 1)) :
    IntegrableOn (fun z => U' z ^ 2) (Set.Ioo (0:ℝ) 1) := by
  have hm := deriv_meas U U' hderiv
  refine Integrable.mono' (f := fun z => U' z ^ 2) (g := fun z => U' z ^ 2 / z ^ 2) hint ?_ ?_
  · exact hm.pow 2
  · rw [ae_restrict_iff' measurableSet_Ioo]
    refine Eventually.of_forall (fun z hz => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hz2 : (1:ℝ) ≤ 1 / z ^ 2 := by
      rw [le_div_iff₀ (pow_pos hz.1 2)]
      nlinarith [hz.1, hz.2]
    calc U' z ^ 2 = U' z ^ 2 * 1 := by ring
      _ ≤ U' z ^ 2 * (1 / z ^ 2) := mul_le_mul_of_nonneg_left hz2 (sq_nonneg _)
      _ = U' z ^ 2 / z ^ 2 := by ring

private lemma deriv_integrable (U U' : ℝ → ℝ)
    (hderiv : ∀ z ∈ Set.Ioo (0:ℝ) 1, HasDerivAt U (U' z) z)
    (hint : IntegrableOn (fun z => U' z ^ 2 / z ^ 2) (Set.Ioo (0:ℝ) 1)) :
    IntegrableOn U' (Set.Ioo (0:ℝ) 1) := by
  have hm := deriv_meas U U' hderiv
  have hsq := deriv_sq_integrable U U' hderiv hint
  have hmLp : MemLp U' 2 (volume.restrict (Set.Ioo (0:ℝ) 1)) :=
    (memLp_two_iff_integrable_sq hm).mpr hsq
  exact hmLp.integrable (by norm_num)

private lemma U_sq_le (U U' : ℝ → ℝ)
    (hderiv : ∀ z ∈ Set.Ioo (0:ℝ) 1, HasDerivAt U (U' z) z)
    (hcont : ContinuousOn U (Set.Icc 0 1)) (h0 : U 0 = 0)
    (hint : IntegrableOn (fun z => U' z ^ 2 / z ^ 2) (Set.Ioo (0:ℝ) 1))
    {z : ℝ} (hz : z ∈ Set.Ioc (0:ℝ) 1) :
    U z ^ 2 ≤ z * ∫ t in (0:ℝ)..z, U' t ^ 2 := by
  have hzpos : (0:ℝ) < z := hz.1
  have hUint := deriv_integrable U U' hderiv hint
  have hU2int := deriv_sq_integrable U U' hderiv hint
  have hsub : Set.Ioo (0:ℝ) z ⊆ Set.Ioo (0:ℝ) 1 :=
    fun x hx => ⟨hx.1, lt_of_lt_of_le hx.2 hz.2⟩
  have hIooU : IntegrableOn U' (Set.Ioo (0:ℝ) z) := hUint.mono_set hsub
  have hIooU2 : IntegrableOn (fun t => U' t ^ 2) (Set.Ioo (0:ℝ) z) := hU2int.mono_set hsub
  have hintU : IntervalIntegrable U' volume 0 z :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hzpos.le).mpr
      ((integrableOn_Ioc_iff_integrableOn_Ioo).mpr hIooU)
  have hintU2 : IntervalIntegrable (fun t => U' t ^ 2) volume 0 z :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hzpos.le).mpr
      ((integrableOn_Ioc_iff_integrableOn_Ioo).mpr hIooU2)
  have hFTC : U z = ∫ t in (0:ℝ)..z, U' t := by
    have hcont' : ContinuousOn U (Set.Icc 0 z) :=
      hcont.mono (fun x hx => ⟨hx.1, le_trans hx.2 hz.2⟩)
    have hderiv' : ∀ x ∈ Set.Ioo (0:ℝ) z, HasDerivAt U (U' x) x :=
      fun x hx => hderiv x ⟨hx.1, lt_of_lt_of_le hx.2 hz.2⟩
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hzpos.le hcont' hderiv' hintU
    rw [h0, sub_zero] at h
    exact h.symm
  have hkey : (∫ t in (0:ℝ)..z, U' t) ^ 2 ≤ z * ∫ t in (0:ℝ)..z, U' t ^ 2 := by
    set c : ℝ := (∫ t in (0:ℝ)..z, U' t) / z with hc
    have hIntUc : IntervalIntegrable (fun t => (2 * c) * U' t) volume 0 z :=
      hintU.const_mul (2 * c)
    have hIntConst : IntervalIntegrable (fun _ : ℝ => c ^ 2) volume 0 z := intervalIntegrable_const
    have hnn : (0:ℝ) ≤ ∫ t in (0:ℝ)..z, (U' t - c) ^ 2 :=
      intervalIntegral.integral_nonneg hzpos.le (fun t _ => sq_nonneg _)
    have hexp : ∫ t in (0:ℝ)..z, (U' t - c) ^ 2
        = (∫ t in (0:ℝ)..z, U' t ^ 2) - (2 * c) * (∫ t in (0:ℝ)..z, U' t)
          + c ^ 2 * z := by
      have h1 : ∫ t in (0:ℝ)..z, (U' t - c) ^ 2
          = ∫ t in (0:ℝ)..z, (U' t ^ 2 - (2 * c) * U' t + c ^ 2) :=
        intervalIntegral.integral_congr (fun t _ => by ring)
      rw [h1, intervalIntegral.integral_add (hintU2.sub hIntUc) hIntConst,
          intervalIntegral.integral_sub hintU2 hIntUc,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
      simp only [sub_zero, smul_eq_mul]
      ring
    rw [hexp, hc] at hnn
    field_simp at hnn
    nlinarith [hnn, hzpos]
  rw [hFTC]
  exact hkey

private lemma gg_le (U U' : ℝ → ℝ)
    (hderiv : ∀ z ∈ Set.Ioo (0:ℝ) 1, HasDerivAt U (U' z) z)
    (hcont : ContinuousOn U (Set.Icc 0 1)) (h0 : U 0 = 0)
    (hint : IntegrableOn (fun z => U' z ^ 2 / z ^ 2) (Set.Ioo (0:ℝ) 1))
    {z : ℝ} (hz : z ∈ Set.Ioc (0:ℝ) 1) :
    U z ^ 2 / z ^ 3 ≤ ∫ t in Set.Ioo (0:ℝ) z, U' t ^ 2 / t ^ 2 := by
  have hzpos : (0:ℝ) < z := hz.1
  have h := U_sq_le U U' hderiv hcont h0 hint hz
  have hYint : IntervalIntegrable (fun t => U' t ^ 2 / t ^ 2) volume 0 z := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hzpos.le, integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hint.mono_set (fun x hx => ⟨hx.1, lt_of_lt_of_le hx.2 hz.2⟩)
  have hU2int : IntervalIntegrable (fun t => U' t ^ 2) volume 0 z := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hzpos.le, integrableOn_Ioc_iff_integrableOn_Ioo]
    exact (deriv_sq_integrable U U' hderiv hint).mono_set
      (fun x hx => ⟨hx.1, lt_of_lt_of_le hx.2 hz.2⟩)
  have hcmp : ∫ t in (0:ℝ)..z, U' t ^ 2 ≤ ∫ t in (0:ℝ)..z, z ^ 2 * (U' t ^ 2 / t ^ 2) :=
    intervalIntegral.integral_mono_on_of_le_Ioo hzpos.le hU2int (hYint.const_mul (z ^ 2))
      (fun t ht => by
        have ht0 : 0 < t := ht.1
        have hone : (1:ℝ) ≤ z ^ 2 / t ^ 2 := by
          rw [le_div_iff₀ (pow_pos ht0 2)]
          nlinarith [ht.1, ht.2, hzpos]
        calc U' t ^ 2 = U' t ^ 2 * 1 := by ring
          _ ≤ U' t ^ 2 * (z ^ 2 / t ^ 2) := mul_le_mul_of_nonneg_left hone (sq_nonneg _)
          _ = z ^ 2 * (U' t ^ 2 / t ^ 2) := by ring)
  rw [intervalIntegral.integral_const_mul] at hcmp
  have hYIoo : ∫ t in (0:ℝ)..z, U' t ^ 2 / t ^ 2 = ∫ t in Set.Ioo (0:ℝ) z, U' t ^ 2 / t ^ 2 := by
    rw [intervalIntegral.integral_of_le hzpos.le, MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [hYIoo] at hcmp
  have h3 : U z ^ 2 ≤ z ^ 3 * ∫ t in Set.Ioo (0:ℝ) z, U' t ^ 2 / t ^ 2 := by
    calc U z ^ 2 ≤ z * (∫ t in (0:ℝ)..z, U' t ^ 2) := h
      _ ≤ z * (z ^ 2 * ∫ t in Set.Ioo (0:ℝ) z, U' t ^ 2 / t ^ 2) :=
          mul_le_mul_of_nonneg_left hcmp hzpos.le
      _ = z ^ 3 * ∫ t in Set.Ioo (0:ℝ) z, U' t ^ 2 / t ^ 2 := by ring
  rw [div_le_iff₀ (pow_pos hzpos 3)]
  nlinarith [h3]

theorem HardyLeft (U U' : ℝ → ℝ)
    (hderiv : ∀ z ∈ Set.Ioo (0:ℝ) 1, HasDerivAt U (U' z) z)
    (hcont : ContinuousOn U (Set.Icc 0 1)) (h0 : U 0 = 0)
    (hint : MeasureTheory.IntegrableOn (fun z => U' z ^ 2 / z ^ 2) (Set.Ioo 0 1)) :
    MeasureTheory.IntegrableOn (fun z => U z ^ 2 / z ^ 4) (Set.Ioo 0 1) ∧
      ∫ z in Set.Ioo (0:ℝ) 1, U z ^ 2 / z ^ 4
        ≤ (2/3) * ∫ z in Set.Ioo (0:ℝ) 1, U' z ^ 2 / z ^ 2 := by
  set X : ℝ → ℝ := fun z => U z ^ 2 / z ^ 4 with hX
  set Y : ℝ → ℝ := fun z => U' z ^ 2 / z ^ 2 with hY
  set gg : ℝ → ℝ := fun z => U z ^ 2 * (z ^ 3)⁻¹ with hgg
  set gg' : ℝ → ℝ := fun z => 2 * U z * U' z / z ^ 3 - 3 * U z ^ 2 / z ^ 4 with hgg'
  set S : ℝ → ℝ := fun z => (U' z / z - (3/2) * U z / z ^ 2) ^ 2 with hS
  have hY0 : IntegrableOn Y (Set.Ioo (0:ℝ) 1) := by rw [hY]; exact hint
  have hYnn : ∀ z, 0 ≤ Y z := by
    intro z; rw [hY]; exact div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hgg_deriv : ∀ z ∈ Set.Ioo (0:ℝ) 1, HasDerivAt gg (gg' z) z := by
    intro z hz
    have hz0 : z ≠ 0 := hz.1.ne'
    have h1 : HasDerivAt (fun w => U w ^ 2) (2 * U z * U' z) z := by
      have hh := (hderiv z hz).pow 2
      rw [show (fun w => U w ^ 2) = U ^ 2 from by funext w; rfl]
      convert hh using 1
      ring
    have h2 : HasDerivAt (fun w => (w ^ 3)⁻¹) (-(3 * z ^ 2) / (z ^ 3) ^ 2) z :=
      (hasDerivAt_pow 3 z).inv (pow_ne_zero 3 hz0)
    have h3 := h1.mul h2
    rw [hgg, hgg']
    refine h3.congr_deriv ?_
    field_simp
    ring
  have hS_id : ∀ z, z ≠ 0 → S z = Y z - (3/2) * gg' z - (9/4) * X z := by
    intro z hz0
    rw [hS, hY, hgg', hX]
    field_simp
    ring
  have hgg1 : 0 ≤ gg 1 := by rw [hgg]; norm_num; positivity
  have hBd : ∀ ε ∈ Set.Ioo (0:ℝ) 1,
      ∫ z in ε..1, X z ≤ (4/9) * (∫ z in (0:ℝ)..1, Y z) + (2/3) * gg ε := by
    intro ε hε
    have hε1 : ε ≤ 1 := hε.2.le
    have hXc : ContinuousOn X (Set.uIcc ε 1) := by
      rw [Set.uIcc_of_le hε1, hX]
      refine ContinuousOn.div ((hcont.mono ?_).pow 2) (continuousOn_id.pow 4) ?_
      · intro z hz; exact ⟨le_trans hε.1.le hz.1, hz.2⟩
      · intro z hz; exact pow_ne_zero 4 (ne_of_gt (lt_of_lt_of_le hε.1 hz.1))
    have hXint : IntervalIntegrable X volume ε 1 := hXc.intervalIntegrable
    have hYint : IntervalIntegrable Y volume ε 1 := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hε1, integrableOn_Ioc_iff_integrableOn_Ioo]
      exact hY0.mono_set (fun x hx => ⟨lt_trans hε.1 hx.1, hx.2⟩)
    have hU'int : IntervalIntegrable U' volume ε 1 := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hε1, integrableOn_Ioc_iff_integrableOn_Ioo]
      exact (deriv_integrable U U' hderiv hint).mono_set
        (fun x hx => ⟨lt_trans hε.1 hx.1, hx.2⟩)
    have hc1 : ContinuousOn (fun z => 2 * U z / z ^ 3) (Set.uIcc ε 1) := by
      rw [Set.uIcc_of_le hε1]
      refine ContinuousOn.div ((hcont.mono ?_).const_mul 2) (continuousOn_id.pow 3) ?_
      · intro z hz; exact ⟨le_trans hε.1.le hz.1, hz.2⟩
      · intro z hz; exact pow_ne_zero 3 (ne_of_gt (lt_of_lt_of_le hε.1 hz.1))
    have hterm1 : IntervalIntegrable (fun z => 2 * U z * U' z / z ^ 3) volume ε 1 := by
      refine (hU'int.mul_continuousOn hc1).congr ?_
      intro z hz
      simp only
      ring
    have hc2 : ContinuousOn (fun z => 3 * U z ^ 2 / z ^ 4) (Set.Icc ε 1) := by
      refine ContinuousOn.div (((hcont.mono ?_).pow 2).const_mul 3) (continuousOn_id.pow 4) ?_
      · intro z hz; exact ⟨le_trans hε.1.le hz.1, hz.2⟩
      · intro z hz; exact pow_ne_zero 4 (ne_of_gt (lt_of_lt_of_le hε.1 hz.1))
    have hterm2 : IntervalIntegrable (fun z => 3 * U z ^ 2 / z ^ 4) volume ε 1 :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hε1).mpr
        ((hc2.integrableOn_compact isCompact_Icc).mono_set (fun x hx => ⟨hx.1.le, hx.2⟩))
    have hgg'int : IntervalIntegrable gg' volume ε 1 := by
      rw [hgg']
      exact hterm1.sub hterm2
    have hpt : ∀ z ∈ Set.Ioo ε 1, (9/4) * X z ≤ Y z - (3/2) * gg' z := by
      intro z hz
      have hz0 : z ≠ 0 := ne_of_gt (lt_trans hε.1 hz.1)
      have hsid := hS_id z hz0
      rw [hS] at hsid
      nlinarith [sq_nonneg (U' z / z - (3/2) * U z / z ^ 2), hsid]
    have hmono : (9/4) * (∫ z in ε..1, X z) ≤ ∫ z in ε..1, (Y z - (3/2) * gg' z) := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_mono_on_of_le_Ioo hε1 (hXint.const_mul (9/4))
        (hYint.sub (hgg'int.const_mul (3/2))) hpt
    have hsplit : ∫ z in ε..1, (Y z - (3/2) * gg' z)
        = (∫ z in ε..1, Y z) - (3/2) * (∫ z in ε..1, gg' z) := by
      rw [intervalIntegral.integral_sub hYint (hgg'int.const_mul (3/2)),
          intervalIntegral.integral_const_mul]
    have hggcont : ContinuousOn gg (Set.Icc ε 1) := by
      rw [hgg]
      refine ContinuousOn.div ((hcont.mono ?_).pow 2) (continuousOn_id.pow 3) ?_
      · intro z hz; exact ⟨le_trans hε.1.le hz.1, hz.2⟩
      · intro z hz; exact pow_ne_zero 3 (ne_of_gt (lt_of_lt_of_le hε.1 hz.1))
    have hggFTC : ∫ z in ε..1, gg' z = gg 1 - gg ε :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hε1 hggcont
        (fun x hx => hgg_deriv x ⟨lt_trans hε.1 hx.1, hx.2⟩) hgg'int
    have hcombine : (9/4) * (∫ z in ε..1, X z)
        ≤ (∫ z in ε..1, Y z) - (3/2) * gg 1 + (3/2) * gg ε := by
      rw [hsplit, hggFTC] at hmono
      linarith [hmono]
    have hYle : ∫ z in ε..1, Y z ≤ ∫ z in (0:ℝ)..1, Y z := by
      have e1 : ∫ z in ε..1, Y z = ∫ z in Set.Ioo ε 1, Y z := by
        rw [intervalIntegral.integral_of_le hε1, MeasureTheory.integral_Ioc_eq_integral_Ioo]
      have e2 : ∫ z in (0:ℝ)..1, Y z = ∫ z in Set.Ioo (0:ℝ) 1, Y z := by
        rw [intervalIntegral.integral_of_le zero_le_one, MeasureTheory.integral_Ioc_eq_integral_Ioo]
      rw [e1, e2]
      exact setIntegral_mono_set hY0 (Eventually.of_forall (fun z => hYnn z))
        (Eventually.of_forall (fun z hx => ⟨lt_trans hε.1 hx.1, hx.2⟩))
    have hfin : (9/4) * (∫ z in ε..1, X z) ≤ (∫ z in (0:ℝ)..1, Y z) + (3/2) * gg ε := by
      nlinarith [hcombine, hYle, hgg1]
    linarith [hfin]
  -- handle the limit
  set C : ℝ := (4/9) * ∫ z in (0:ℝ)..1, Y z with hCdef
  have hCnn : 0 ≤ C := by
    rw [hCdef]
    exact mul_nonneg (by norm_num) (intervalIntegral.integral_nonneg zero_le_one (fun z _ => hYnn z))
  have hXgc : ContinuousOn X (Set.Ioo (0:ℝ) 1) := by
    rw [hX]
    refine ContinuousOn.div ((hcont.mono ?_).pow 2) (continuousOn_id.pow 4) ?_
    · intro z hz; exact ⟨hz.1.le, hz.2.le⟩
    · intro z hz; exact pow_ne_zero 4 (ne_of_gt hz.1)
  set Xg : ℝ → ℝ := (Set.Ioo (0:ℝ) 1).indicator X with hXg
  have hXg_meas : AEMeasurable Xg volume := by
    rw [hXg, aemeasurable_indicator_iff measurableSet_Ioo]
    exact (hXgc.aestronglyMeasurable measurableSet_Ioo).aemeasurable
  have hXioo : ∀ ε ∈ Set.Ioo (0:ℝ) 1, IntegrableOn X (Set.Ioo ε 1) := by
    intro ε hε
    have hXc : ContinuousOn X (Set.Icc ε 1) := by
      rw [hX]
      refine ContinuousOn.div ((hcont.mono ?_).pow 2) (continuousOn_id.pow 4) ?_
      · intro z hz; exact ⟨le_trans hε.1.le hz.1, hz.2⟩
      · intro z hz; exact pow_ne_zero 4 (ne_of_gt (lt_of_lt_of_le hε.1 hz.1))
    exact (hXc.integrableOn_compact isCompact_Icc).mono_set (fun x hx => ⟨hx.1.le, hx.2.le⟩)
  have hlin : ∀ ε ∈ Set.Ioo (0:ℝ) 1,
      ∫⁻ z in Set.Ioo ε 1, ENNReal.ofReal (Xg z) ≤ ENNReal.ofReal (C + (2/3) * gg ε) := by
    intro ε hε
    have hsub : Set.Ioo ε 1 ⊆ Set.Ioo (0:ℝ) 1 := fun x hx => ⟨lt_trans hε.1 hx.1, hx.2⟩
    have hXgeq : EqOn (fun z => ENNReal.ofReal (Xg z)) (fun z => ENNReal.ofReal (X z))
        (Set.Ioo ε 1) := by
      intro z hz
      show ENNReal.ofReal (Xg z) = ENNReal.ofReal (X z)
      rw [hXg, Set.indicator_of_mem (hsub hz)]
    rw [setLIntegral_congr_fun measurableSet_Ioo hXgeq]
    have hXnnε : 0 ≤ᵐ[volume.restrict (Set.Ioo ε 1)] X :=
      Eventually.of_forall (fun z => by rw [hX]; exact div_nonneg (sq_nonneg _) (by positivity))
    rw [← ofReal_integral_eq_lintegral_ofReal (hXioo ε hε) hXnnε]
    refine ENNReal.ofReal_le_ofReal ?_
    have heq : ∫ z in Set.Ioo ε 1, X z = ∫ z in ε..1, X z := by
      rw [intervalIntegral.integral_of_le hε.2.le, MeasureTheory.integral_Ioc_eq_integral_Ioo]
    rw [heq]
    exact hBd ε hε
  have hlin_seq : ∀ n : ℕ,
      ∫⁻ z in Set.Ioo (1 / ((n:ℝ) + 2)) 1, ENNReal.ofReal (Xg z)
        ≤ ENNReal.ofReal (C + (2/3) * gg (1 / ((n:ℝ) + 2))) := by
    intro n
    apply hlin
    constructor
    · positivity
    · rw [div_lt_one (by positivity)]
      have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      linarith
  have hgg_seq0 : Tendsto (fun n : ℕ => gg (1 / ((n:ℝ) + 2))) atTop (𝓝 0) := by
    set e : ℕ → ℝ := fun n => 1 / ((n:ℝ) + 2) with he
    have hepos : ∀ n, 0 < e n := fun n => by rw [he]; positivity
    have helt1 : ∀ n, e n ≤ 1 := by
      intro n
      have h1 : (0:ℝ) < (n:ℝ) + 2 := by positivity
      rw [he, div_le_one h1]
      have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      linarith
    have heanti : Antitone e := by
      intro m n hmn
      rw [he]
      apply one_div_le_one_div_of_le (by positivity)
      have : (m:ℝ) ≤ (n:ℝ) := by exact_mod_cast hmn
      linarith
    have hetend0 : Tendsto e atTop (𝓝 (0:ℝ)) := by
      rw [he]
      have hg2 : Tendsto (fun n : ℕ => ((n:ℝ) + 2)) atTop atTop := by
        have h := (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 2)
        have h2 : (fun n : ℕ => ((n:ℝ) + 2)) = (fun n : ℕ => ((n + 2 : ℕ) : ℝ)) := by
          funext n; push_cast; ring
        rw [h2]; exact h
      exact (tendsto_const_nhds (x := (1:ℝ))).div_atTop hg2
    have hInter : (⋂ n, Set.Ioo (0:ℝ) (e n)) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      rw [Set.mem_iInter] at hx
      have hx0 : 0 < x := (hx 0).1
      have hxe : ∀ n, x ≤ e n := fun n => (hx n).2.le
      have : x ≤ 0 := le_of_tendsto_of_tendsto' tendsto_const_nhds hetend0 hxe
      linarith
    have hy0 : IntegrableOn Y (Set.Ioo (0:ℝ) (e 0)) := by
      have he0 : e 0 = 1/2 := by rw [he]; norm_num
      rw [he0]
      exact hY0.mono_set (fun x hx => ⟨hx.1, by linarith [hx.2]⟩)
    have hYs : Tendsto (fun n => ∫ z in Set.Ioo (0:ℝ) (e n), Y z) atTop
        (𝓝 (∫ z in ⋂ n, Set.Ioo (0:ℝ) (e n), Y z)) :=
      tendsto_setIntegral_of_antitone (fun n => measurableSet_Ioo)
        (fun m n hmn x hx => ⟨hx.1, lt_of_lt_of_le hx.2 (heanti hmn)⟩) ⟨0, hy0⟩
    rw [hInter] at hYs
    simp only [MeasureTheory.setIntegral_empty] at hYs
    refine squeeze_zero' ?_ ?_ hYs
    · filter_upwards with n
      rw [hgg]; positivity
    · filter_upwards with n
      rw [hgg]
      exact gg_le U U' hderiv hcont h0 hint ⟨hepos n, helt1 n⟩
  have hgg_seq : Tendsto (fun n : ℕ => (2/3) * gg (1 / ((n:ℝ) + 2))) atTop (𝓝 0) := by
    simpa using hgg_seq0.const_mul (2/3)
  have hmain := lintegral_Ioo_le_of_seq Xg hXg_meas hCnn
    (fun ε => (2/3) * gg ε) hgg_seq hlin_seq
  have hXmeas01 : AEStronglyMeasurable X (volume.restrict (Set.Ioo (0:ℝ) 1)) :=
    hXgc.aestronglyMeasurable measurableSet_Ioo
  have hXnn01 : 0 ≤ᵐ[volume.restrict (Set.Ioo (0:ℝ) 1)] X :=
    Eventually.of_forall (fun z => by rw [hX]; exact div_nonneg (sq_nonneg _) (by positivity))
  have hlincongr : ∫⁻ z in Set.Ioo (0:ℝ) 1, ENNReal.ofReal (Xg z)
      = ∫⁻ z in Set.Ioo (0:ℝ) 1, ENNReal.ofReal (X z) := by
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro z hz
    show ENNReal.ofReal (Xg z) = ENNReal.ofReal (X z)
    rw [hXg, Set.indicator_of_mem hz]
  have hfin : ∫⁻ z in Set.Ioo (0:ℝ) 1, ENNReal.ofReal (X z) < ⊤ := by
    rw [← hlincongr]
    exact lt_of_le_of_lt hmain ENNReal.ofReal_lt_top
  have hXint01 : IntegrableOn X (Set.Ioo (0:ℝ) 1) :=
    ⟨hXmeas01, (hasFiniteIntegral_iff_ofReal hXnn01).mpr hfin⟩
  refine ⟨hXint01, ?_⟩
  have hintEq : ∫ z in Set.Ioo (0:ℝ) 1, X z
      = (∫⁻ z in Set.Ioo (0:ℝ) 1, ENNReal.ofReal (X z)).toReal :=
    integral_eq_lintegral_of_nonneg_ae hXnn01 hXmeas01
  rw [hintEq]
  have h1 : (∫⁻ z in Set.Ioo (0:ℝ) 1, ENNReal.ofReal (X z)).toReal ≤ C := by
    have hle : (∫⁻ z in Set.Ioo (0:ℝ) 1, ENNReal.ofReal (X z)) ≤ ENNReal.ofReal C := by
      rw [← hlincongr]; exact hmain
    calc (∫⁻ z in Set.Ioo (0:ℝ) 1, ENNReal.ofReal (X z)).toReal
        ≤ (ENNReal.ofReal C).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
      _ = C := ENNReal.toReal_ofReal hCnn
  calc (∫⁻ z in Set.Ioo (0:ℝ) 1, ENNReal.ofReal (X z)).toReal
      ≤ C := h1
    _ = (4/9) * ∫ z in Set.Ioo (0:ℝ) 1, Y z := by
        rw [hCdef, intervalIntegral.integral_of_le zero_le_one,
          MeasureTheory.integral_Ioc_eq_integral_Ioo]
    _ ≤ (2/3) * ∫ z in Set.Ioo (0:ℝ) 1, U' z ^ 2 / z ^ 2 := by
        rw [hY]
        have hJ : 0 ≤ ∫ z in Set.Ioo (0:ℝ) 1, U' z ^ 2 / z ^ 2 :=
          integral_nonneg (fun z => div_nonneg (sq_nonneg _) (sq_nonneg _))
        nlinarith [hJ]

end Work.Elliptic
