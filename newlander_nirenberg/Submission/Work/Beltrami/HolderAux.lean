/-
# Auxiliary lemmas for the Hölder (Schauder) estimate for the Beurling transform

This file collects the elementary facts about the cutoff `bumpC`, the regularised kernel
`W w = (1 - bumpC w) * w⁻²` (`Submission/Work/Beltrami/Wkernel.lean`) and the radial integrals
of `‖w‖ ^ s` needed for the Calderón–Zygmund estimate for

  `beurling f z = -π⁻¹ ∫ (f ζ - bumpC (ζ - z) * f z) * (ζ - z)⁻² dA(ζ)`.

The two non-trivial facts are

* `annulus_inv_sq_zero` : the pure kernel `w ↦ w⁻²` has mean zero on any annulus with inner
  radius `a > 0` (rotation argument: `(I*w)⁻² = -w⁻²`), and
* `exterior_rpow_integral` : `∫_{a ≤ ‖w‖} ‖w‖^s = 2π a^{s+2}/(-(s+2))` for `s < -2`, which is
  the far-field integral appearing in the Calderón–Zygmund estimate.
-/
import Mathlib
import Submission.Work.Beltrami.Cauchy
import Submission.Work.Beltrami.Wkernel
import Submission.Work.Beltrami.integral_radial_weight_inv_sq_eq_zero
import Submission.Work.CR.Flat.Cauchy.integral_norm_rpow_ball

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace Work.Beltrami

/-- The cutoff `bumpC` is even: `bumpC (-w) = bumpC w`. -/
theorem bumpC_neg (w : ℂ) : bumpC (-w) = bumpC w := by rw [bumpC, bumpC, norm_neg]

/-- The regularised kernel `W` is even. -/
theorem W_neg (w : ℂ) : W (-w) = W w := by
  rw [W_apply, W_apply, bumpC_neg, neg_sq]

/-- The pure kernel `w ↦ w⁻²` has mean zero on annuli with inner radius `a > 0`: the rotation
`w ↦ i·w` maps the annulus to itself and is measure preserving, while `(i·w)⁻² = -w⁻²`. -/
theorem annulus_inv_sq_zero {a b : ℝ} (ha : 0 < a) :
    ∫ w in {w : ℂ | a ≤ ‖w‖ ∧ ‖w‖ < b}, (w ^ 2)⁻¹ = 0 := by
  have hmem : ∀ (c : Circle) (w : ℂ),
      w ∈ {w : ℂ | a ≤ ‖w‖ ∧ ‖w‖ < b} ↔ (c : ℂ) * w ∈ {w : ℂ | a ≤ ‖w‖ ∧ ‖w‖ < b} := by
    intro c w
    simp only [Set.mem_ofPred_eq, norm_mul, Circle.norm_coe, one_mul]
  have hmeas : MeasurableSet {w : ℂ | a ≤ ‖w‖ ∧ ‖w‖ < b} :=
    (isClosed_le continuous_const continuous_norm).measurableSet.inter
      (isOpen_lt continuous_norm continuous_const).measurableSet
  have hfin : volume {w : ℂ | a ≤ ‖w‖ ∧ ‖w‖ < b} < ⊤ := by
    refine lt_of_le_of_lt (measure_mono (t := Metric.ball (0 : ℂ) (|b| + 1)) ?_)
      (measure_ball_lt_top (μ := volume))
    intro w hw
    rw [Metric.mem_ball, dist_zero_right]
    have h2 : b ≤ |b| := le_abs_self b
    linarith [hw.2]
  have hint : IntegrableOn (fun w : ℂ => (w ^ 2)⁻¹) {w : ℂ | a ≤ ‖w‖ ∧ ‖w‖ < b} volume := by
    refine IntegrableOn.of_bound hfin ?_ (a⁻¹ ^ 2) ?_
    · exact ((measurable_id.pow_const 2).inv).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem hmeas] with w hw
      have hwa : a ≤ ‖w‖ := hw.1
      have hpos : 0 < ‖w‖ := lt_of_lt_of_le ha hwa
      rw [norm_inv, norm_pow, inv_pow]
      exact (inv_le_inv₀ (pow_pos hpos 2) (pow_pos ha 2)).mpr (pow_le_pow_left₀ ha.le hwa 2)
  have h := integral_radial_weight_inv_sq_eq_zero (fun _ : ℝ => (1 : ℝ)) hmem (by simpa using hint)
  simpa using h

/-- The radial integral over the exterior of a disc: for `a > 0` and `s < -2`,
`∫_{a ≤ ‖w‖} ‖w‖ ^ s dA(w) = 2π a ^ (s + 2) / (-(s + 2))`, and `w ↦ ‖w‖ ^ s` is integrable
there.  (Polar coordinates reduce the integral to `2π ∫_a^∞ y^{s+1} dy`, which converges
because `s + 1 < -1`.) -/
theorem exterior_rpow_integral {a s : ℝ} (ha : 0 < a) (hs : s < -2) :
    IntegrableOn (fun w : ℂ => ‖w‖ ^ s) {w : ℂ | a ≤ ‖w‖} volume ∧
      ∫ w in {w : ℂ | a ≤ ‖w‖}, ‖w‖ ^ s = 2 * Real.pi * a ^ (s + 2) / (-(s + 2)) := by
  have hs1 : s + 1 < -1 := by linarith
  have hs2 : s + 2 ≠ 0 := by linarith
  have hT : MeasurableSet {w : ℂ | a ≤ ‖w‖} :=
    (isClosed_le continuous_const continuous_norm).measurableSet
  -- the radial profile of the integrand
  set G : ℝ → ℝ := fun y => (Ici a).indicator (fun y : ℝ => y ^ s) y with hG
  have hprof : ∀ w : ℂ, G ‖w‖ = {w : ℂ | a ≤ ‖w‖}.indicator (fun w : ℂ => ‖w‖ ^ s) w := by
    intro w
    by_cases hw : a ≤ ‖w‖
    · simp only [hG, Set.indicator_of_mem (show ‖w‖ ∈ Ici a from hw),
        Set.indicator_of_mem (show w ∈ {w : ℂ | a ≤ ‖w‖} from hw)]
    · simp only [hG, Set.indicator_of_notMem (show ‖w‖ ∉ Ici a from hw),
        Set.indicator_of_notMem (show w ∉ {w : ℂ | a ≤ ‖w‖} from hw)]
  -- the one-dimensional integral produced by polar coordinates
  have hnorm : ∀ y : ℝ, y ^ (Module.finrank ℝ ℂ - 1) = y := by
    intro y
    rw [Complex.finrank_real_complex]
    norm_num
  have hGmul : ∀ y : ℝ, y ^ (Module.finrank ℝ ℂ - 1) • G y
      = (Ici a).indicator (fun y : ℝ => y ^ (s + 1)) y := by
    intro y
    rw [hnorm]
    by_cases hy : a ≤ y
    · have hypos : 0 < y := lt_of_lt_of_le ha hy
      simp only [hG, Set.indicator_of_mem (show y ∈ Ici a from hy), smul_eq_mul]
      calc y * y ^ s = y ^ s * y := by ring
        _ = y ^ (s + 1) := by rw [Real.rpow_add hypos, Real.rpow_one]
    · simp only [hG, Set.indicator_of_notMem (show y ∉ Ici a from hy), smul_eq_mul, mul_zero]
  have h1d_eval : ∫ y : ℝ in Ioi (0 : ℝ), y ^ (Module.finrank ℝ ℂ - 1) • G y
      = -a ^ (s + 2) / (s + 2) := by
    simp_rw [hGmul]
    rw [setIntegral_indicator measurableSet_Ici,
      show Ioi (0 : ℝ) ∩ Ici a = Ici a from by
        ext y
        simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ici]
        exact ⟨fun h => h.2, fun h => ⟨lt_of_lt_of_le ha h, h⟩⟩,
      integral_Ici_eq_integral_Ioi]
    rw [show s + 2 = s + 1 + 1 from by ring]
    exact integral_Ioi_rpow_of_lt hs1 ha
  have h1d_int : IntegrableOn (fun y : ℝ => y ^ (Module.finrank ℝ ℂ - 1) • G y) (Ioi 0) := by
    have hcongr : (fun y : ℝ => y ^ (Module.finrank ℝ ℂ - 1) • G y)
        = fun y : ℝ => (Ici a).indicator (fun y : ℝ => y ^ (s + 1)) y := funext hGmul
    rw [hcongr]
    have hIci : IntegrableOn (fun y : ℝ => y ^ (s + 1)) (Ici a) :=
      (integrableOn_Ici_iff_integrableOn_Ioi).mpr (integrableOn_Ioi_rpow_of_lt hs1 ha)
    exact (hIci.integrable_indicator measurableSet_Ici).integrableOn
  have hint : Integrable (fun w : ℂ => G ‖w‖) :=
    (integrable_fun_norm_addHaar (μ := volume) (F := ℝ) (f := G)).mpr h1d_int
  have hval : ∫ w in {w : ℂ | a ≤ ‖w‖}, ‖w‖ ^ s = ∫ w : ℂ, G ‖w‖ := by
    rw [← integral_indicator hT (f := fun w : ℂ => ‖w‖ ^ s)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun w => hprof w)
  refine ⟨?_, ?_⟩
  · rw [← integrable_indicator_iff hT]
    exact hint.congr (Filter.Eventually.of_forall fun w => hprof w)
  · rw [hval, integral_fun_norm_addHaar (μ := volume) (f := G), h1d_eval,
      Complex.finrank_real_complex]
    have hreal : (volume : Measure ℂ).real (Metric.ball (0 : ℂ) 1) = Real.pi := by
      simp [MeasureTheory.Measure.real, Complex.volume_ball]
    rw [hreal, nsmul_eq_mul, smul_eq_mul]
    field_simp
    ring

/-- Integrability of `ζ ↦ ‖ζ - c‖ ^ s` on the exterior of the disc of radius `a` around `c`
(`s < -2`, `a > 0`), obtained from `exterior_rpow_integral` by translation. -/
theorem integrableOn_exterior_rpow_shift (c : ℂ) {a s : ℝ} (ha : 0 < a) (hs : s < -2) :
    IntegrableOn (fun ζ : ℂ => ‖ζ - c‖ ^ s) {ζ : ℂ | a ≤ ‖ζ - c‖} volume := by
  have hA : MeasurableSet {w : ℂ | a ≤ ‖w‖} :=
    (isClosed_le continuous_const continuous_norm).measurableSet
  have hB : MeasurableSet {ζ : ℂ | a ≤ ‖ζ - c‖} :=
    (isClosed_le continuous_const (continuous_id.sub continuous_const).norm).measurableSet
  have h1 : Integrable ({w : ℂ | a ≤ ‖w‖}.indicator (fun w : ℂ => ‖w‖ ^ s)) volume :=
    (exterior_rpow_integral ha hs).1.integrable_indicator hA
  have h2 : Integrable
      (fun ζ : ℂ => {w : ℂ | a ≤ ‖w‖}.indicator (fun w : ℂ => ‖w‖ ^ s) (ζ - c)) volume :=
    h1.comp_sub_right c
  have hfun : (fun ζ : ℂ => {w : ℂ | a ≤ ‖w‖}.indicator (fun w : ℂ => ‖w‖ ^ s) (ζ - c))
      = {ζ : ℂ | a ≤ ‖ζ - c‖}.indicator (fun ζ : ℂ => ‖ζ - c‖ ^ s) := by
    funext ζ
    by_cases hζ : a ≤ ‖ζ - c‖
    · rw [Set.indicator_of_mem (show ζ ∈ {ζ : ℂ | a ≤ ‖ζ - c‖} from hζ),
        Set.indicator_of_mem (show ζ - c ∈ {w : ℂ | a ≤ ‖w‖} from by
          simpa only [Set.mem_ofPred_eq, sub_eq_add_neg] using hζ)]
    · rw [Set.indicator_of_notMem (show ζ ∉ {ζ : ℂ | a ≤ ‖ζ - c‖} from hζ),
        Set.indicator_of_notMem (show ζ - c ∉ {w : ℂ | a ≤ ‖w‖} from by
          simpa only [Set.mem_ofPred_eq, sub_eq_add_neg] using hζ)]
  have h3 : Integrable ({ζ : ℂ | a ≤ ‖ζ - c‖}.indicator (fun ζ : ℂ => ‖ζ - c‖ ^ s)) volume := by
    rw [← hfun]; exact h2
  exact (integrable_indicator_iff hB).mp h3

end Work.Beltrami
