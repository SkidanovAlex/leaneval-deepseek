import Mathlib
import Submission.Work.Beltrami.Cauchy
import Submission.Work.Beltrami.Wkernel

/-!
# The L¹ translate-difference bound for the regularised Beurling kernel `W`

`W w = (1 - bumpC w) * w⁻²` is smooth on `ℂ` (the cutoff kills the singularity at `0`,
and outside the unit disc `W w = w⁻²`).  In this file we prove that `fderiv ℝ W` is
absolutely integrable, and deduce the `L¹` translate-difference bound

`∫ u, ‖W (u - x) - W (u - y)‖ ≤ C * ‖x - y‖`.

The proof is the standard one: write the difference as the integral of `fderiv W` along
the segment from `u - x` to `u - y` (fundamental theorem of calculus in integral form),
take norms, and evaluate the resulting double integral by Tonelli together with the
translation invariance of Lebesgue measure.
-/

noncomputable section

set_option maxHeartbeats 1000000

open MeasureTheory Metric Filter Set
open scoped ContDiff Topology ENNReal

namespace Work.Beltrami

/-! ## Smoothness and derivative bounds for `W` -/

/-- The regularised kernel `W` is smooth on all of `ℂ`. -/
theorem contDiff_W : ContDiff ℝ ∞ W := by
  rw [contDiff_iff_contDiffAt]
  intro w
  by_cases hw : w = 0
  · subst hw
    have h : W =ᶠ[𝓝 (0:ℂ)] (fun _ => (0:ℂ)) := by
      filter_upwards [Metric.ball_mem_nhds (0:ℂ) (by norm_num : (0:ℝ) < 1/2)] with z hz
      rw [Metric.mem_ball, dist_zero_right] at hz
      exact W_eq_zero_of_norm_le_half (le_of_lt hz)
    exact (contDiffAt_const (c := (0:ℂ))).congr_of_eventuallyEq h
  · have hV : ContDiffAt ℝ ∞ (fun z : ℂ => 1 - (bumpC z : ℂ)) w := by
      have hb : ContDiff ℝ ∞ (fun z : ℂ => (bumpC z : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp bumpC_contDiff
      exact contDiffAt_const.sub hb.contDiffAt
    have hK : ContDiffAt ℝ ∞ (fun z : ℂ => (z^2)⁻¹) w := by
      refine ContDiffAt.inv (contDiffAt_id.pow 2) ?_
      simp [hw]
    exact hV.mul hK

/-- Outside the unit disc, `‖fderiv W‖ ≤ 2 ‖w‖⁻³`. -/
theorem norm_fderiv_W_le_of_two_le {w : ℂ} (hw : 2 ≤ ‖w‖) :
    ‖fderiv ℝ W w‖ ≤ 2 * ‖w‖ ^ (-3 : ℝ) := by
  have hwpos : 0 < ‖w‖ := by linarith
  have hw0 : w ≠ 0 := norm_pos_iff.mp hwpos
  have h1 : 1 < ‖w‖ := by linarith
  have hfdeq : fderiv ℝ W w = fderiv ℝ (fun z : ℂ => (z ^ 2)⁻¹) w :=
    (W_eventuallyEq_inv_sq h1).fderiv_eq
  rw [hfdeq]
  have hne : w ^ 2 ≠ 0 := pow_ne_zero _ hw0
  have hinv : HasFDerivAt Inv.inv
      (-(((ContinuousLinearMap.mulLeftRight ℝ ℂ) ((w^2)⁻¹)) ((w^2)⁻¹))) (w^2) :=
    hasFDerivAt_inv' hne
  have hpow : HasFDerivAt (fun z : ℂ => z ^ 2)
      (((2:ℕ) • w^(2-1)) • ContinuousLinearMap.id ℝ ℂ) w := hasFDerivAt_pow 2
  have hcomp := hinv.comp w hpow
  rw [show (fun z : ℂ => (z^2)⁻¹) = Inv.inv ∘ (fun z : ℂ => z^2) from rfl, hcomp.fderiv]
  have hQ : ‖-(((ContinuousLinearMap.mulLeftRight ℝ ℂ) ((w^2)⁻¹)) ((w^2)⁻¹))‖ ≤ ‖w‖ ^ (-4 : ℝ) := by
    rw [norm_neg]
    refine le_trans (ContinuousLinearMap.opNorm_mulLeftRight_apply_apply_le ℝ ℂ (w^2)⁻¹ (w^2)⁻¹) ?_
    rw [norm_inv, norm_pow]
    rw [show ((‖w‖ ^ 2)⁻¹) * ((‖w‖ ^ 2)⁻¹) = ‖w‖ ^ (-4 : ℝ) from by
      rw [← mul_inv]
      rw [show ((‖w‖^2) * (‖w‖^2)) = ‖w‖ ^ (4:ℕ) from by ring]
      rw [← Real.rpow_natCast ‖w‖ 4, ← Real.rpow_neg (le_of_lt hwpos)]
      norm_num]
  have hP : ‖(((2:ℕ) • w^(2-1)) • ContinuousLinearMap.id ℝ ℂ)‖ ≤ 2 * ‖w‖ := by
    rw [show ((2:ℕ) • w^(2-1)) = (2:ℂ) * w from by norm_num]
    calc ‖((2:ℂ) * w) • ContinuousLinearMap.id ℝ ℂ‖
        ≤ ‖(2:ℂ) * w‖ := by
          refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun v => ?_)
          rw [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, norm_mul]
      _ = 2 * ‖w‖ := by rw [norm_mul, Complex.norm_ofNat]
  calc ‖(-(((ContinuousLinearMap.mulLeftRight ℝ ℂ) ((w^2)⁻¹)) ((w^2)⁻¹))).comp
        ((((2:ℕ) • w^(2-1)) • ContinuousLinearMap.id ℝ ℂ))‖
      ≤ ‖-(((ContinuousLinearMap.mulLeftRight ℝ ℂ) ((w^2)⁻¹)) ((w^2)⁻¹))‖ *
          ‖(((2:ℕ) • w^(2-1)) • ContinuousLinearMap.id ℝ ℂ)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖w‖ ^ (-4 : ℝ) * (2 * ‖w‖) := by
        exact mul_le_mul hQ hP (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)
    _ = 2 * ‖w‖ ^ (-3 : ℝ) := by
        rw [show ‖w‖ ^ (-4 : ℝ) = (‖w‖^4)⁻¹ from by
          rw [← Real.rpow_natCast ‖w‖ 4, ← Real.rpow_neg (le_of_lt hwpos)]; norm_num]
        rw [show ‖w‖ ^ (-3 : ℝ) = (‖w‖^3)⁻¹ from by
          rw [← Real.rpow_natCast ‖w‖ 3, ← Real.rpow_neg (le_of_lt hwpos)]; norm_num]
        field_simp

/-! ## Integrability of `‖fderiv W‖` -/

/-- `w ↦ ‖w‖ ^ s` is integrable outside any ball, for `s < -2` (the two-dimensional
tail). -/
theorem integrableOn_norm_rpow_lt_compl {c s : ℝ} (hc : 0 < c) (hs : s < -2) :
    IntegrableOn (fun w : ℂ => ‖w‖ ^ s) {w : ℂ | c < ‖w‖} volume := by
  have h1 : Integrable (fun w : ℂ => if c < ‖w‖ then ‖w‖ ^ s else 0) volume := by
    rw [MeasureTheory.integrable_fun_norm_addHaar (μ := (volume : Measure ℂ)) (E := ℂ)
      (F := ℝ) (f := fun y : ℝ => if c < y then y ^ s else 0)]
    have hsimp : (fun y : ℝ => y ^ (Module.finrank ℝ ℂ - 1) • (if c < y then y ^ s else 0))
        = fun y : ℝ => (if c < y then y ^ (s+1) else 0) := by
      funext y
      rw [Complex.finrank_real_complex]
      norm_num
      by_cases h : c < y
      · rw [ite_eq_left h, ite_eq_left h]
        calc y * y ^ s = y ^ (1:ℝ) * y ^ s := by rw [Real.rpow_one]
          _ = y ^ ((1:ℝ) + s) := (Real.rpow_add (lt_trans hc h) 1 s).symm
          _ = y ^ (s+1) := by ring_nf
      · rw [ite_eq_right h, ite_eq_right h]
    rw [hsimp]
    have h3 : (Ioi (0:ℝ)).indicator (fun y : ℝ => (if c < y then y ^ (s+1) else 0))
        = (Ioi c).indicator (fun y : ℝ => y ^ (s+1)) := by
      funext y
      by_cases hy : c < y
      · have hy0 : (0:ℝ) < y := lt_trans hc hy
        rw [Set.indicator_of_mem (show y ∈ Ioi (0:ℝ) from hy0),
          Set.indicator_of_mem (show y ∈ Ioi c from hy), ite_eq_left hy]
      · rw [Set.indicator_of_notMem (show y ∉ Ioi c from hy)]
        by_cases h0 : y ∈ Ioi (0:ℝ)
        · rw [Set.indicator_of_mem h0, ite_eq_right hy]
        · rw [Set.indicator_of_notMem h0]
    refine (integrable_indicator_iff measurableSet_Ioi).mp ?_
    rw [h3]
    exact (integrable_indicator_iff measurableSet_Ioi).mpr
      (integrableOn_Ioi_rpow_of_lt (by linarith) hc)
  refine (integrable_indicator_iff (isOpen_lt continuous_const continuous_norm).measurableSet).mp ?_
  refine h1.congr (Filter.Eventually.of_forall fun w => ?_)
  simp only [Set.indicator, Set.mem_ofPred_eq]

/-- `fderiv W` is globally bounded: near `0` because `W` is smooth and vanishes on a
ball, and at infinity because `W = w⁻²` there.  Consequently `‖fderiv W‖` is
integrable, since `‖w‖⁻³` decays fast enough in dimension two. -/
theorem integrable_norm_fderiv_W : Integrable (fun w : ℂ => ‖fderiv ℝ W w‖) volume := by
  have hcont : Continuous (fderiv ℝ W) := contDiff_W.continuous_fderiv (by simp)
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ w : ℂ, ‖w‖ ≤ 2 → ‖fderiv ℝ W w‖ ≤ M := by
    obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn (isCompact_closedBall (0:ℂ) 2)
        hcont.continuousOn (f := fun w : ℂ => fderiv ℝ W w)
    exact ⟨M, fun w hw => hM w (by simpa [Metric.mem_closedBall, dist_eq_norm] using hw)⟩
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 (by norm_num))
  have hfin : volume {w : ℂ | ‖w‖ ≤ 2} < ⊤ := by
    refine lt_of_le_of_lt (measure_mono ?_) (isCompact_closedBall (0:ℂ) 2).measure_lt_top
    intro w hw
    simpa [Metric.mem_closedBall, dist_eq_norm] using hw
  have hmeas1 : MeasurableSet {w : ℂ | ‖w‖ ≤ 2} :=
    (isClosed_le continuous_norm continuous_const).measurableSet
  have hmeas2 : MeasurableSet {w : ℂ | 2 < ‖w‖} :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  have hg : Integrable (fun w : ℂ => if ‖w‖ ≤ 2 then M else 2 * ‖w‖ ^ (-3 : ℝ)) volume := by
    have hgm : Measurable (fun w : ℂ => if ‖w‖ ≤ 2 then M else 2 * ‖w‖ ^ (-3 : ℝ)) := by
      refine Measurable.ite hmeas1 measurable_const ?_
      have hpow : Measurable (fun w : ℂ => ‖w‖ ^ (-3 : ℝ)) := by measurability
      exact measurable_const.mul hpow
    have hg1 : IntegrableOn (fun w : ℂ => if ‖w‖ ≤ 2 then M else 2 * ‖w‖ ^ (-3 : ℝ))
        {w : ℂ | ‖w‖ ≤ 2} volume := by
      refine MeasureTheory.IntegrableOn.of_bound hfin hgm.aestronglyMeasurable M ?_
      filter_upwards [ae_restrict_mem hmeas1] with w hw
      rw [ite_eq_left hw, Real.norm_of_nonneg hM0]
    have hg2 : IntegrableOn (fun w : ℂ => if ‖w‖ ≤ 2 then M else 2 * ‖w‖ ^ (-3 : ℝ))
        {w : ℂ | ‖w‖ ≤ 2}ᶜ volume := by
      have hbase : IntegrableOn (fun w : ℂ => 2 * ‖w‖ ^ (-3 : ℝ)) {w : ℂ | ‖w‖ ≤ 2}ᶜ volume := by
        have h0 := (integrableOn_norm_rpow_lt_compl (c := 2) (s := -3)
          (by norm_num) (by norm_num)).const_mul 2
        rw [show {w : ℂ | ‖w‖ ≤ 2}ᶜ = {w : ℂ | 2 < ‖w‖} from by
          ext w; simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]]
        exact h0
      refine hbase.congr_fun ?_ hmeas1.compl
      intro w hw
      change 2 * ‖w‖ ^ (-3 : ℝ) = (if ‖w‖ ≤ 2 then M else 2 * ‖w‖ ^ (-3 : ℝ))
      rw [ite_eq_right (by simpa only [Set.mem_compl_iff, Set.mem_ofPred_eq] using hw)]
    have hU : IntegrableOn (fun w : ℂ => if ‖w‖ ≤ 2 then M else 2 * ‖w‖ ^ (-3 : ℝ))
        ({w : ℂ | ‖w‖ ≤ 2} ∪ {w : ℂ | ‖w‖ ≤ 2}ᶜ) volume := hg1.union hg2
    rwa [Set.union_compl_self, MeasureTheory.integrableOn_univ] at hU
  refine Integrable.mono' hg hcont.norm.aestronglyMeasurable ?_
  filter_upwards with w
  rcases lt_or_ge ‖w‖ 2 with h | h
  · rw [ite_eq_left (le_of_lt h)]
    simpa only [Real.norm_of_nonneg (norm_nonneg _)] using hM w (le_of_lt h)
  · rcases eq_or_lt_of_le h with h' | h'
    · rw [ite_eq_left (le_of_eq h'.symm)]
      simpa only [Real.norm_of_nonneg (norm_nonneg _)] using hM w (le_of_eq h'.symm)
    · rw [ite_eq_right (not_le.mpr h')]
      simpa only [Real.norm_of_nonneg (norm_nonneg _)] using norm_fderiv_W_le_of_two_le (le_of_lt h')

/-! ## The fundamental-theorem-of-calculus identity along a segment -/

/-- Pointwise `L¹`-type bound: the translate difference of `W` is controlled by the
integral of `‖fderiv W‖` along the segment joining the two translates. -/
theorem norm_W_sub_le (x y u : ℂ) :
    ‖W (u - x) - W (u - y)‖
      ≤ ‖x - y‖ * ∫ t in (0:ℝ)..1, ‖fderiv ℝ W (u - x + t • (x - y))‖ := by
  have hW : Differentiable ℝ W := contDiff_W.differentiable (by simp)
  have hcontW : Continuous (fderiv ℝ W) := contDiff_W.continuous_fderiv (by simp)
  have hpath : ∀ t : ℝ, HasDerivAt (fun t : ℝ => u - x + t • (x - y)) (x - y) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => s • (x - y)) (x - y) t := by
      simpa using (hasDerivAt_id t).smul_const (x - y)
    exact h1.const_add (u - x)
  have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun t => W (u - x + t • (x - y)))
        ((fderiv ℝ W (u - x + t • (x - y))) (x - y)) t := by
    intro t ht
    exact ((hW (u - x + t • (x - y))).hasFDerivAt).comp_hasDerivAt t (hpath t)
  have hcontpath : Continuous (fun t : ℝ => u - x + t • (x - y)) := by fun_prop
  have hcont : Continuous (fun t : ℝ => fderiv ℝ W (u - x + t • (x - y))) :=
    hcontW.comp hcontpath
  have hint : IntervalIntegrable
      (fun t : ℝ => (fderiv ℝ W (u - x + t • (x - y))) (x - y)) volume 0 1 :=
    (hcont.clm_apply continuous_const).intervalIntegrable 0 1
  have hkey : W (u - x) - W (u - y)
      = - ∫ t in (0:ℝ)..1, (fderiv ℝ W (u - x + t • (x - y))) (x - y) := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    rw [show W (u - x + (1:ℝ) • (x - y)) = W (u - y) from by
          simp only [one_smul]; congr 1; ring,
        show W (u - x + (0:ℝ) • (x - y)) = W (u - x) from by simp] at h
    rw [h]; abel
  rw [hkey, norm_neg]
  calc ‖∫ t in (0:ℝ)..1, (fderiv ℝ W (u - x + t • (x - y))) (x - y)‖
      ≤ ∫ t in (0:ℝ)..1, ‖(fderiv ℝ W (u - x + t • (x - y))) (x - y)‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ ∫ t in (0:ℝ)..1, ‖fderiv ℝ W (u - x + t • (x - y))‖ * ‖x - y‖ := by
        refine intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ ?_
        · exact ((hcont.clm_apply continuous_const).norm).intervalIntegrable 0 1
        · exact ((hcont.norm).mul_const _).intervalIntegrable 0 1
        · intro t ht
          exact ContinuousLinearMap.le_opNorm _ _
    _ = (∫ t in (0:ℝ)..1, ‖fderiv ℝ W (u - x + t • (x - y))‖) * ‖x - y‖ :=
        intervalIntegral.integral_mul_const _ _
    _ = ‖x - y‖ * ∫ t in (0:ℝ)..1, ‖fderiv ℝ W (u - x + t • (x - y))‖ := by ring

/-! ## The main theorem -/

/-- The L¹ version of the fundamental-identity bound for the kernel
`W w = (1 - bumpC w) * w⁻²`: the translate difference is absolutely integrable with total mass
`O(‖x - y‖)`.  Suggested route: `W (u-x) - W (u-y) = ∫_0^1 fderiv W (u-x+t(x-y)) (x-y) dt`,
Tonelli, and `∫_ℂ ‖fderiv W‖ < ∞` (`fderiv W` vanishes near `0`, is bounded on
`{1/2 ≤ ‖w‖ ≤ 1}` and is `≤ 2‖w‖^{-3}` for `‖w‖ ≥ 1`). -/
theorem exists_integral_norm_W_sub_le :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : ℂ,
      (∫ u : ℂ, ‖(1 - (Work.Beltrami.bumpC (u - x) : ℂ)) * ((u - x) ^ 2)⁻¹
                - (1 - (Work.Beltrami.bumpC (u - y) : ℂ)) * ((u - y) ^ 2)⁻¹‖
          ∂MeasureTheory.volume) ≤ C * ‖x - y‖ := by
  have hInt : Integrable (fun w : ℂ => ‖fderiv ℝ W w‖) volume := integrable_norm_fderiv_W
  have hcontW : Continuous (fderiv ℝ W) := contDiff_W.continuous_fderiv (by simp)
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = ∫ w : ℂ, ‖fderiv ℝ W w‖ := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hK]; exact integral_nonneg (fun w => norm_nonneg (fderiv ℝ W w))
  refine ⟨K + 1, by linarith, ?_⟩
  intro x y
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = ‖x - y‖ := ⟨_, rfl⟩
  have hd0 : 0 ≤ d := by rw [hd]; exact norm_nonneg _
  have hgoal : (∫ u : ℂ, ‖W (u - x) - W (u - y)‖) ≤ (K + 1) * d := by
    -- pointwise bound, as an inequality of Lebesgue integrals
    have hstep : ∀ u : ℂ, ENNReal.ofReal ‖W (u - x) - W (u - y)‖
        ≤ ∫⁻ t in Ioc (0:ℝ) (1:ℝ),
            ENNReal.ofReal (d * ‖fderiv ℝ W (u - x + t • (x - y))‖) := by
      intro u
      have h1 : ‖W (u - x) - W (u - y)‖
          ≤ ∫ t in (0:ℝ)..1, d * ‖fderiv ℝ W (u - x + t • (x - y))‖ := by
        simpa [hd, intervalIntegral.integral_const_mul] using norm_W_sub_le x y u
      have hpathc : Continuous (fun t : ℝ => u - x + t • (x - y)) := by fun_prop
      have hcont_t : Continuous (fun t : ℝ => d * ‖fderiv ℝ W (u - x + t • (x - y))‖) :=
        ((hcontW.comp hpathc).norm).const_mul d
      have hfi : IntegrableOn (fun t : ℝ => d * ‖fderiv ℝ W (u - x + t • (x - y))‖)
          (Ioc (0:ℝ) (1:ℝ)) volume :=
        (ContinuousOn.integrableOn_compact isCompact_Icc hcont_t.continuousOn).mono_set
          Ioc_subset_Icc_self
      calc ENNReal.ofReal ‖W (u - x) - W (u - y)‖
          ≤ ENNReal.ofReal (∫ t in (0:ℝ)..1, d * ‖fderiv ℝ W (u - x + t • (x - y))‖) :=
            ENNReal.ofReal_le_ofReal h1
        _ = ENNReal.ofReal (∫ t in Ioc (0:ℝ) (1:ℝ),
              d * ‖fderiv ℝ W (u - x + t • (x - y))‖) := by
            rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
        _ = ∫⁻ t in Ioc (0:ℝ) (1:ℝ),
              ENNReal.ofReal (d * ‖fderiv ℝ W (u - x + t • (x - y))‖) := by
            rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfi
              (Filter.Eventually.of_forall fun t => mul_nonneg hd0 (norm_nonneg _))]
    -- Tonelli
    have huncurry : AEMeasurable
        (Function.uncurry fun u : ℂ => fun t : ℝ =>
          ENNReal.ofReal (d * ‖fderiv ℝ W (u - x + t • (x - y))‖))
        (volume.prod (volume.restrict (Ioc (0:ℝ) (1:ℝ)))) := by
      apply Continuous.aemeasurable
      show Continuous (fun p : ℂ × ℝ =>
        ENNReal.ofReal (d * ‖fderiv ℝ W (p.1 - x + p.2 • (x - y))‖))
      have hpc : Continuous (fun p : ℂ × ℝ => p.1 - x + p.2 • (x - y)) := by fun_prop
      exact ENNReal.continuous_ofReal.comp (continuous_const.mul ((hcontW.comp hpc).norm))
    have hswap : (∫⁻ u : ℂ, ∫⁻ t in Ioc (0:ℝ) (1:ℝ),
          ENNReal.ofReal (d * ‖fderiv ℝ W (u - x + t • (x - y))‖))
        = ∫⁻ t in Ioc (0:ℝ) (1:ℝ), ∫⁻ u : ℂ,
          ENNReal.ofReal (d * ‖fderiv ℝ W (u - x + t • (x - y))‖) :=
      MeasureTheory.lintegral_lintegral_swap huncurry
    -- the inner integral does not depend on `t`
    have hper : ∀ t : ℝ, (∫⁻ u : ℂ,
          ENNReal.ofReal (d * ‖fderiv ℝ W (u - x + t • (x - y))‖))
        = ENNReal.ofReal d * ENNReal.ofReal K := by
      intro t
      have hmm : Measurable (fun u : ℂ =>
          ENNReal.ofReal (‖fderiv ℝ W (u - x + t • (x - y))‖)) := by
        have hc : Continuous (fun u : ℂ => fderiv ℝ W (u - x + t • (x - y))) :=
          hcontW.comp (by fun_prop)
        exact (ENNReal.continuous_ofReal.comp hc.norm).measurable
      simp_rw [ENNReal.ofReal_mul hd0]
      rw [MeasureTheory.lintegral_const_mul _ hmm]
      congr 1
      rw [show (fun u : ℂ => ENNReal.ofReal (‖fderiv ℝ W (u - x + t • (x - y))‖))
            = fun u : ℂ => (fun v : ℂ => ENNReal.ofReal (‖fderiv ℝ W v‖))
                (u + (t • (x - y) - x)) from by
          funext u; congr 3; ring]
      rw [MeasureTheory.lintegral_add_right_eq_self
        (fun v : ℂ => ENNReal.ofReal (‖fderiv ℝ W v‖)) (t • (x - y) - x)]
      exact ((MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt
        (Filter.Eventually.of_forall fun v => norm_nonneg _)).symm).trans (by rw [hK])
    have hmain : (∫⁻ u : ℂ, ENNReal.ofReal ‖W (u - x) - W (u - y)‖)
        ≤ ENNReal.ofReal d * ENNReal.ofReal K := by
      calc (∫⁻ u : ℂ, ENNReal.ofReal ‖W (u - x) - W (u - y)‖)
          ≤ ∫⁻ u : ℂ, ∫⁻ t in Ioc (0:ℝ) (1:ℝ),
              ENNReal.ofReal (d * ‖fderiv ℝ W (u - x + t • (x - y))‖) :=
            lintegral_mono hstep
        _ = ∫⁻ t in Ioc (0:ℝ) (1:ℝ), ∫⁻ u : ℂ,
              ENNReal.ofReal (d * ‖fderiv ℝ W (u - x + t • (x - y))‖) := hswap
        _ = ∫⁻ t in Ioc (0:ℝ) (1:ℝ), ENNReal.ofReal d * ENNReal.ofReal K := by
            simp_rw [hper]
        _ = ENNReal.ofReal d * ENNReal.ofReal K := by
            rw [MeasureTheory.setLIntegral_const, Real.volume_Ioc, sub_zero,
              ENNReal.ofReal_one, mul_one]
    have hfinal : (∫⁻ u : ℂ, ENNReal.ofReal ‖W (u - x) - W (u - y)‖)
        ≤ ENNReal.ofReal (K * d) := by
      rw [ENNReal.ofReal_mul hK0]
      exact hmain.trans (le_of_eq (mul_comm _ _))
    have hcontF : Continuous (fun u : ℂ => ‖W (u - x) - W (u - y)‖) :=
      (((contDiff_W.continuous.comp (continuous_id.sub continuous_const)).sub
        (contDiff_W.continuous.comp (continuous_id.sub continuous_const))).norm)
    have hnn : 0 ≤ᵐ[volume] (fun u : ℂ => ‖W (u - x) - W (u - y)‖) :=
      Filter.Eventually.of_forall fun u => norm_nonneg _
    have hmeas : AEStronglyMeasurable (fun u : ℂ => ‖W (u - x) - W (u - y)‖) volume :=
      hcontF.aestronglyMeasurable
    calc (∫ u : ℂ, ‖W (u - x) - W (u - y)‖)
        = (∫⁻ u : ℂ, ENNReal.ofReal ‖W (u - x) - W (u - y)‖).toReal :=
          MeasureTheory.integral_eq_lintegral_of_nonneg_ae hnn hmeas
      _ ≤ (ENNReal.ofReal (K * d)).toReal := ENNReal.toReal_mono (by simp) hfinal
      _ = K * d := ENNReal.toReal_ofReal (mul_nonneg hK0 hd0)
      _ ≤ (K + 1) * d := by nlinarith [hd0]
  simpa only [W_apply, hd] using hgoal

end Work.Beltrami
