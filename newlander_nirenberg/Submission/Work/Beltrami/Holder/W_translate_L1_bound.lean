import Mathlib
import Submission.Work.Beltrami.Wkernel
import Submission.Work.Beltrami.W_fderiv_bound
import Submission.Work.Beltrami.exists_integral_norm_W_sub_le

noncomputable section

set_option maxHeartbeats 1000000

open MeasureTheory Metric Filter Set
open scoped Topology ContDiff ENNReal

namespace Work.Beltrami.Holder

/-! ## An integrable radial step majorant

The function `w ↦ if ‖w‖ ≤ R then 1 else 8 ‖w‖⁻³` (for `R ≥ 1`) is integrable: it is bounded
on the disc of radius `R` and decays cubically outside, which is summable in dimension two. -/

theorem integrable_radial_inv_cube_step {R : ℝ} (hR : 1 ≤ R) :
    Integrable (fun w : ℂ => if ‖w‖ ≤ R then (1 : ℝ) else 8 * (‖w‖⁻¹) ^ 3) volume := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hmeas1 : MeasurableSet {w : ℂ | ‖w‖ ≤ R} :=
    (isClosed_le continuous_norm continuous_const).measurableSet
  have hmeas2 : MeasurableSet {w : ℂ | R < ‖w‖} :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  have hm : Measurable (fun w : ℂ => if ‖w‖ ≤ R then (1 : ℝ) else 8 * (‖w‖⁻¹) ^ 3) :=
    Measurable.ite hmeas1 measurable_const
      (Measurable.const_mul (Measurable.pow_const (Measurable.inv measurable_norm) 3) 8)
  have hfin : volume {w : ℂ | ‖w‖ ≤ R} < ⊤ := by
    have hset : {w : ℂ | ‖w‖ ≤ R} = Metric.closedBall (0 : ℂ) R := by
      ext w
      simp [Metric.mem_closedBall, dist_eq_norm]
    rw [hset]
    exact (isCompact_closedBall (0 : ℂ) R).measure_lt_top
  have h1 : IntegrableOn (fun w : ℂ => if ‖w‖ ≤ R then (1 : ℝ) else 8 * (‖w‖⁻¹) ^ 3)
      {w : ℂ | ‖w‖ ≤ R} volume := by
    refine IntegrableOn.of_bound hfin hm.aestronglyMeasurable 1 ?_
    filter_upwards [ae_restrict_mem hmeas1] with w hw
    rw [ite_eq_left hw]
    simp
  have h2 : IntegrableOn (fun w : ℂ => if ‖w‖ ≤ R then (1 : ℝ) else 8 * (‖w‖⁻¹) ^ 3)
      {w : ℂ | R < ‖w‖} volume := by
    have hbase : IntegrableOn (fun w : ℂ => 8 * (‖w‖⁻¹) ^ 3) {w : ℂ | R < ‖w‖} volume := by
      have h0 : IntegrableOn (fun w : ℂ => ‖w‖ ^ (-3 : ℝ)) {w : ℂ | R < ‖w‖} volume :=
        integrableOn_norm_rpow_lt_compl hR0 (by norm_num)
      refine IntegrableOn.congr_fun (h0.const_mul 8) ?_ hmeas2
      intro w hw
      have hw0 : 0 < ‖w‖ := lt_trans hR0 hw
      show 8 * ‖w‖ ^ (-3 : ℝ) = 8 * (‖w‖⁻¹) ^ 3
      rw [show (-3 : ℝ) = -((3 : ℕ) : ℝ) from by norm_num]
      rw [Real.rpow_neg hw0.le (3 : ℕ), Real.rpow_natCast, inv_pow]
    refine IntegrableOn.congr_fun hbase ?_ hmeas2
    intro w hw
    show 8 * (‖w‖⁻¹) ^ 3 = (if ‖w‖ ≤ R then (1 : ℝ) else 8 * (‖w‖⁻¹) ^ 3)
    rw [ite_eq_right (not_le.mpr hw)]
  have h2' : IntegrableOn (fun w : ℂ => if ‖w‖ ≤ R then (1 : ℝ) else 8 * (‖w‖⁻¹) ^ 3)
      {w : ℂ | ‖w‖ ≤ R}ᶜ volume := by
    rw [show {w : ℂ | ‖w‖ ≤ R}ᶜ = {w : ℂ | R < ‖w‖} from by
      ext w
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]]
    exact h2
  have hU := h1.union h2'
  rwa [Set.union_compl_self, integrableOn_univ] at hU

/-! ## Pointwise bound for the translate difference

The translate difference of `W` is controlled by the derivative of `W` along the segment
joining the two translates; using `‖fderiv W v‖ ≤ M (1 + ‖v‖)⁻³`, the interval integral is
bounded by `M (1 + max 0 (‖u - x‖ - ‖x - y‖))⁻³`, and this is in turn bounded by the radial
step majorant (with the step at `R = max 1 (2 ‖x - y‖)`). -/

theorem norm_W_translate_sub_le {M : ℝ} (hM0 : 0 < M)
    (hM : ∀ v : ℂ, ‖fderiv ℝ W v‖ ≤ M * (1 + ‖v‖)⁻¹ ^ 3) (x y u : ℂ) :
    ‖W (u - x) - W (u - y)‖ ≤ M * ‖x - y‖ *
      (if ‖u - x‖ ≤ max 1 (2 * ‖x - y‖) then (1 : ℝ) else 8 * (‖u - x‖⁻¹) ^ 3) := by
  have hle0 : (0 : ℝ) ≤ ‖x - y‖ := norm_nonneg _
  have hs_pos : 0 < 1 + max 0 (‖u - x‖ - ‖x - y‖) := by
    have := le_max_left (0 : ℝ) (‖u - x‖ - ‖x - y‖)
    linarith
  -- pointwise domination of the integrand
  have hstep : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ W (u - x + t • (x - y))‖ ≤ M * (1 + max 0 (‖u - x‖ - ‖x - y‖))⁻¹ ^ 3 := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have hnorm : max 0 (‖u - x‖ - ‖x - y‖) ≤ ‖u - x + t • (x - y)‖ := by
      refine max_le (norm_nonneg _) ?_
      have htri : ‖u - x‖ ≤ ‖u - x + t • (x - y)‖ + ‖t • (x - y)‖ := by
        have heq : u - x = (u - x + t • (x - y)) - t • (x - y) := by ring
        calc ‖u - x‖ = ‖(u - x + t • (x - y)) - t • (x - y)‖ := congrArg norm heq
          _ ≤ ‖u - x + t • (x - y)‖ + ‖t • (x - y)‖ := norm_sub_le _ _
      have htn : ‖t • (x - y)‖ ≤ ‖x - y‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
        exact mul_le_of_le_one_left (norm_nonneg _) ht.2
      linarith
    have hle : (1 + ‖u - x + t • (x - y)‖)⁻¹ ^ 3 ≤ (1 + max 0 (‖u - x‖ - ‖x - y‖))⁻¹ ^ 3 := by
      have h2 : 1 + max 0 (‖u - x‖ - ‖x - y‖) ≤ 1 + ‖u - x + t • (x - y)‖ := by linarith
      have h3 : (1 + ‖u - x + t • (x - y)‖)⁻¹ ≤ (1 + max 0 (‖u - x‖ - ‖x - y‖))⁻¹ :=
        (inv_le_inv₀ (by linarith) hs_pos).mpr h2
      exact pow_le_pow_left₀ (by positivity) h3 3
    calc ‖fderiv ℝ W (u - x + t • (x - y))‖
        ≤ M * (1 + ‖u - x + t • (x - y)‖)⁻¹ ^ 3 := hM _
      _ ≤ M * (1 + max 0 (‖u - x‖ - ‖x - y‖))⁻¹ ^ 3 :=
          mul_le_mul_of_nonneg_left hle hM0.le
  -- the interval integral
  have hInt : (∫ t in (0 : ℝ)..1, ‖fderiv ℝ W (u - x + t • (x - y))‖)
      ≤ M * (1 + max 0 (‖u - x‖ - ‖x - y‖))⁻¹ ^ 3 := by
    have hcontW : Continuous (fderiv ℝ W) := contDiff_W.continuous_fderiv (by simp)
    have hcont : Continuous (fun t : ℝ => ‖fderiv ℝ W (u - x + t • (x - y))‖) :=
      (hcontW.comp (by fun_prop)).norm
    refine le_trans (intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ hstep) ?_
    · exact hcont.intervalIntegrable 0 1
    · exact intervalIntegrable_const
    · rw [intervalIntegral.integral_const]
      simp
  have hmain : ‖W (u - x) - W (u - y)‖
      ≤ ‖x - y‖ * (M * (1 + max 0 (‖u - x‖ - ‖x - y‖))⁻¹ ^ 3) :=
    le_trans (norm_W_sub_le x y u) (mul_le_mul_of_nonneg_left hInt hle0)
  by_cases hA : ‖u - x‖ ≤ max 1 (2 * ‖x - y‖)
  · rw [ite_eq_left hA]
    have hcube : (1 + max 0 (‖u - x‖ - ‖x - y‖))⁻¹ ^ 3 ≤ 1 := by
      have h4 : (1 + max 0 (‖u - x‖ - ‖x - y‖))⁻¹ ≤ 1 := by
        have := (inv_le_inv₀ hs_pos (by norm_num : (0 : ℝ) < 1)).mpr
          (by linarith [le_max_left (0 : ℝ) (‖u - x‖ - ‖x - y‖)] : (1 : ℝ) ≤ 1 + max 0 (‖u - x‖ - ‖x - y‖))
        simpa using this
      calc (1 + max 0 (‖u - x‖ - ‖x - y‖))⁻¹ ^ 3
          ≤ 1 ^ 3 := pow_le_pow_left₀ (by positivity) h4 3
        _ = 1 := by norm_num
    calc ‖W (u - x) - W (u - y)‖
        ≤ ‖x - y‖ * (M * (1 + max 0 (‖u - x‖ - ‖x - y‖))⁻¹ ^ 3) := hmain
      _ ≤ ‖x - y‖ * (M * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcube hM0.le) hle0
      _ = M * ‖x - y‖ * 1 := by ring
  · rw [ite_eq_right hA]
    have hx2 : ‖x - y‖ < ‖u - x‖ / 2 := by
      have hlt : max 1 (2 * ‖x - y‖) < ‖u - x‖ := not_le.mp hA
      have := lt_of_le_of_lt (le_max_right (1 : ℝ) (2 * ‖x - y‖)) hlt
      linarith
    have hmax : max 0 (‖u - x‖ - ‖x - y‖) = ‖u - x‖ - ‖x - y‖ :=
      max_eq_right (by linarith)
    have hcube : (1 + max 0 (‖u - x‖ - ‖x - y‖))⁻¹ ^ 3 ≤ 8 * (‖u - x‖⁻¹) ^ 3 := by
      rw [hmax]
      have hu2 : (0 : ℝ) < ‖u - x‖ / 2 := by linarith [norm_nonneg (x - y)]
      have h1 : ‖u - x‖ / 2 ≤ 1 + (‖u - x‖ - ‖x - y‖) := by linarith
      have h2 : (1 + (‖u - x‖ - ‖x - y‖))⁻¹ ≤ (‖u - x‖ / 2)⁻¹ :=
        (inv_le_inv₀ (by linarith) hu2).mpr h1
      have h3 : (1 + (‖u - x‖ - ‖x - y‖))⁻¹ ^ 3 ≤ ((‖u - x‖ / 2)⁻¹) ^ 3 :=
        pow_le_pow_left₀ (inv_nonneg.mpr (by linarith [norm_nonneg (x - y)])) h2 3
      have h4 : ((‖u - x‖ / 2)⁻¹) ^ 3 = 8 * (‖u - x‖⁻¹) ^ 3 := by
        rw [show (‖u - x‖ / 2)⁻¹ = 2 * (‖u - x‖⁻¹) by
          rw [div_eq_mul_inv, mul_inv, inv_inv]
          ring]
        ring
      linarith [h3, h4.le]
    calc ‖W (u - x) - W (u - y)‖
        ≤ ‖x - y‖ * (M * (1 + max 0 (‖u - x‖ - ‖x - y‖))⁻¹ ^ 3) := hmain
      _ ≤ ‖x - y‖ * (M * (8 * (‖u - x‖⁻¹) ^ 3)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcube hM0.le) hle0
      _ = M * ‖x - y‖ * (8 * (‖u - x‖⁻¹) ^ 3) := by ring

/-! ## Integrability of the translate difference -/

theorem integrable_W_translate_sub (x y : ℂ) :
    Integrable (fun u : ℂ => W (u - x) - W (u - y)) volume := by
  obtain ⟨M, hM0, hM⟩ := W_fderiv_bound
  have hR : (1 : ℝ) ≤ max 1 (2 * ‖x - y‖) := le_max_left _ _
  have hstep : Integrable (fun u : ℂ =>
      (if ‖u - x‖ ≤ max 1 (2 * ‖x - y‖) then (1 : ℝ) else 8 * (‖u - x‖⁻¹) ^ 3)) volume :=
    (integrable_radial_inv_cube_step hR).comp_sub_right x
  have hdom : Integrable (fun u : ℂ => M * ‖x - y‖ *
      (if ‖u - x‖ ≤ max 1 (2 * ‖x - y‖) then (1 : ℝ) else 8 * (‖u - x‖⁻¹) ^ 3)) volume :=
    hstep.const_mul (M * ‖x - y‖)
  have hWc : Continuous W := contDiff_W.continuous
  have hcont : Continuous (fun u : ℂ => W (u - x) - W (u - y)) :=
    ((hWc.comp (continuous_id.sub continuous_const)).sub
      (hWc.comp (continuous_id.sub continuous_const)))
  refine Integrable.mono' hdom hcont.aestronglyMeasurable ?_
  filter_upwards with u
  exact norm_W_translate_sub_le hM0 hM x y u

/-- L¹ bound and integrability for the translate difference of the regularised kernel
`W w = (1 - bumpC w) * w⁻²`: there is `C > 0` such that for all `x y : ℂ` the function
`u ↦ W (u - x) - W (u - y)` is integrable and has `∫_ℂ ‖W (u-x) - W (u-y)‖ ≤ C ‖x-y‖`.

This is the Calderón–Zygmund bound for the difference of translates of `W`, needed to control
the term `f x · (W (u-x) - W (u-y))` in the Hölder estimate for `Work.Beltrami.beurling`.

Notes for the proof.  The quantitative part (without the `Integrable` conjunct, and with the
integrand written out as `(1 - bumpC (u-x)) * (u-x)⁻² - (1 - bumpC (u-y)) * (u-y)⁻²`, which is
`W (u-x) - W (u-y)` by `Work.Beltrami.W_apply`) is already proved in the workspace as
`Work.Beltrami.exists_integral_norm_W_sub_le`; the same file also contains
`Work.Beltrami.integrable_norm_fderiv_W` (`Integrable (fun w => ‖fderiv ℝ W w‖)`),
`Work.Beltrami.contDiff_W`, `Work.Beltrami.norm_W_sub_le` (the fundamental-identity bound) and
`Work.Beltrami.norm_fderiv_W_le_of_two_le`.  For the missing integrability one may either run
the Tonelli argument of that file again (the difference of translates of `W` is dominated by
`‖x-y‖ ∫_0^1 ‖fderiv ℝ W (u-x+t(x-y))‖ dt`, which is integrable in `u` by Tonelli and
`integrable_norm_fderiv_W`), or use the Lipschitz bound for `W` (from
`Work.Beltrami.W_fderiv_bound`, `‖fderiv ℝ W v‖ ≤ M (1+‖v‖)⁻³ ≤ M`) together with
`Work.Beltrami.W_eq_inv_sq_of_one_le` (`W w = w⁻²` for `‖w‖ ≥ 1`) and
`Work.Beltrami.norm_inv_sq_sub_inv_sq_le`: off the union of the two discs of radii `1` and
`max 1 (2‖x-y‖)` the difference is `≤ 6‖x-y‖‖u-x‖⁻³` (whose tail integral is finite by
`Work.Beltrami.integral_norm_rpow_exterior` with `s = -3`, giving `∫_{‖w‖ ≥ 1}‖w‖⁻³ = 2π`),
while on that union it is `≤ L‖x-y‖`; this majorant is integrable, so `Integrable.mono'` yields
integrability (and the same computation yields the bound). -/
theorem W_translate_L1_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : ℂ,
      MeasureTheory.Integrable (fun u : ℂ => Work.Beltrami.W (u - x) - Work.Beltrami.W (u - y))
        MeasureTheory.volume ∧
      (∫ u : ℂ, ‖Work.Beltrami.W (u - x) - Work.Beltrami.W (u - y)‖ ∂MeasureTheory.volume)
        ≤ C * ‖x - y‖ := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := exists_integral_norm_W_sub_le
  refine ⟨C₀, hC₀0, fun x y => ⟨integrable_W_translate_sub x y, ?_⟩⟩
  simpa only [W_apply] using hC₀ x y

end Work.Beltrami.Holder
