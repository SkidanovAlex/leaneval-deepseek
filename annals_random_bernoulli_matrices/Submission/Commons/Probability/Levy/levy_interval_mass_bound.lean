import Mathlib.MeasureTheory.Function.SpecialFunctions.Sinc
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.Topology.UniformSpace.Uniformizable

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace Commons.Probability.Levy

/-! # Classical Lévy inequality: interval mass vs. integral of |charFun| -/

-- ================================================================
-- Part A: elementary trig estimates
-- ================================================================

/-- For `0 ≤ v ≤ 1`, `sin v ≥ 5v/6`. -/
lemma sin_ge_five_six (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) : (5 / 6 : ℝ) * v ≤ Real.sin v := by
  have hsub := Real.sin_ge_sub_cube hv0
  have hge : (5 / 6 : ℝ) * v ≤ v - v ^ 3 / 6 := by
    nlinarith [sq_nonneg v, hv1]
  exact le_trans hge hsub

/-- For `|u| ≤ 1`, `2 sin²u ≥ u²`. -/
lemma sin_sq_ge_half_sq {u : ℝ} (hu : |u| ≤ 1) : (2 : ℝ) * Real.sin u ^ 2 ≥ u ^ 2 := by
  have hnonneg : (5 / 6 : ℝ) * |u| ≤ |Real.sin u| := by
    have h56 : ∀ {v : ℝ}, 0 ≤ v → v ≤ 1 → (5 / 6 : ℝ) * v ≤ Real.sin v := by
      intro v hv0 hv1
      exact sin_ge_five_six v hv0 hv1
    by_cases hu0 : 0 ≤ u
    · have h1 : (5 / 6 : ℝ) * u ≤ Real.sin u := h56 hu0 (by nlinarith [abs_le.mp hu])
      have hpos : 0 ≤ Real.sin u := by nlinarith [h1, hu0]
      calc
        (5 / 6 : ℝ) * |u| = (5 / 6 : ℝ) * u := by rw [abs_of_nonneg hu0]
        _ ≤ Real.sin u := h1
        _ = |Real.sin u| := (abs_of_nonneg hpos).symm
    · have hu0' : u ≤ 0 := le_of_not_ge hu0
      let w := -u
      have hw0 : 0 ≤ w := by dsimp [w]; linarith
      have hw1 : w ≤ 1 := by dsimp [w]; nlinarith [abs_le.mp hu]
      have h1 : (5 / 6 : ℝ) * w ≤ Real.sin w := h56 hw0 hw1
      have hpos : 0 ≤ Real.sin w := by nlinarith [h1, hw0]
      calc
        (5 / 6 : ℝ) * |u| = (5 / 6 : ℝ) * w := by dsimp [w]; rw [abs_of_neg]; linarith
        _ ≤ Real.sin w := h1
        _ = |Real.sin u| := by
          have hs : Real.sin u = -Real.sin w := by
            dsimp [w]
            rw [Real.sin_neg]
            ring
          rw [hs, abs_neg]
          exact (abs_of_nonneg hpos).symm
  have hsq0 : ((5 / 6 : ℝ) * u) ^ 2 ≤ Real.sin u ^ 2 := by
    exact sq_le_sq.mpr (by simpa [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 5 / 6)] using hnonneg)
  have hsq : (25 / 36 : ℝ) * u ^ 2 ≤ Real.sin u ^ 2 := by nlinarith [hsq0]
  nlinarith

/-- `1 - cos(2θ) = 2 sin²θ`. -/
lemma one_sub_cos_two_mul_sq (θ : ℝ) : 1 - Real.cos (2 * θ) = 2 * Real.sin θ ^ 2 := by
  rw [Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq θ]

-- ================================================================
-- Part B: the bump and its elementary integral identities
-- ================================================================

/-- derivative of `t ↦ sin (t·v)/v` (used in FTC computations). -/
lemma hasDerivAt_sin_div (v : ℝ) (hv : v ≠ 0) (x : ℝ) :
    HasDerivAt (fun t : ℝ => Real.sin (t * v) / v) (Real.cos (x * v)) x := by
  have hc : HasDerivAt (Real.sin ∘ fun t : ℝ => t * v) (Real.cos (x * v) * v) x :=
    (Real.hasDerivAt_sin (x * v)).comp x (hasDerivAt_mul_const v (x := x))
  exact hc.div_const v |>.congr_deriv (by field_simp [hv])

/-- derivative of `t ↦ cos (t·v)/v²`. -/
lemma hasDerivAt_cos_div (v : ℝ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => Real.cos (t * v) / v ^ 2) ((-Real.sin (x * v)) * v / v ^ 2) x := by
  have hc : HasDerivAt (Real.cos ∘ fun t : ℝ => t * v) ((-Real.sin (x * v)) * v) x :=
    (Real.hasDerivAt_cos (x * v)).comp x (hasDerivAt_mul_const v (x := x))
  exact hc.div_const (v ^ 2)

/-- derivative of the antiderivative of the bump integrand. -/
lemma hasDerivAt_bump_antideriv (w v : ℝ) (hv : v ≠ 0) (x : ℝ) :
    HasDerivAt (fun t : ℝ => (1 - (w / 2) * t) * (Real.sin (t * v) / v)
        - (w / 2) * (Real.cos (t * v) / v ^ 2))
      ((1 - (w / 2) * x) * Real.cos (x * v)) x := by
  have hlin : HasDerivAt (fun t : ℝ => (w / 2) * t) (w / 2) x := by
    exact hasDerivAt_const_mul (w / 2) (x := x)
  have hc1 : HasDerivAt (fun t : ℝ => 1 - (w / 2) * t) (0 - (w / 2)) x := by
    exact (hasDerivAt_const x (1 : ℝ)).sub hlin
  have hmul := hc1.mul (hasDerivAt_sin_div v hv x)
  have hd2 : HasDerivAt (fun t : ℝ => (w / 2) * (Real.cos (t * v) / v ^ 2))
      ((w / 2) * ((-Real.sin (x * v)) * v / v ^ 2)) x := by
    exact (hasDerivAt_cos_div v x).const_mul (w / 2)
  exact (hmul.sub hd2) |>.congr_deriv (by field_simp [hv]; ring)

/-- `∫_0^{2/w} (1 - (w/2)t) cos (t·v) dt = (w/2)(1 − cos(v·(2/w)))/v²` for `v ≠ 0`. -/
lemma integral_tapered_cos (w v : ℝ) (hw : 0 < w) (hv : v ≠ 0) :
    (∫ t in (0:ℝ)..(2 / w), (1 - (w / 2) * t) * Real.cos (t * v)) =
      (w / 2) * (1 - Real.cos (v * (2 / w))) / v ^ 2 := by
  let F : ℝ → ℝ := fun t => (1 - (w / 2) * t) * (Real.sin (t * v) / v)
      - (w / 2) * (Real.cos (t * v) / v ^ 2)
  have hderiv : deriv F = fun t : ℝ => (1 - (w / 2) * t) * Real.cos (t * v) := by
    funext t
    exact (hasDerivAt_bump_antideriv w v hv t).deriv
  have hdiff : ∀ x ∈ Set.uIcc (0 : ℝ) (2 / w), DifferentiableAt ℝ F x := by
    intro x hx
    exact (hasDerivAt_bump_antideriv w v hv x).differentiableAt
  have hcont : ContinuousOn (fun t : ℝ => (1 - (w / 2) * t) * Real.cos (t * v)) (Set.uIcc (0 : ℝ) (2 / w)) := by
    fun_prop
  rw [intervalIntegral.integral_deriv_eq_sub' F hderiv hdiff hcont]
  dsimp [F]
  field_simp [hv]
  ring_nf
  simp
  ring

/-- `∫_0^{2/w} (2w)(1 − (w/2)t) dt = 2`. -/
lemma integral_tapered_const (w : ℝ) (hw : 0 < w) :
    (∫ t in (0:ℝ)..(2 / w), (2 * w) * (1 - (w / 2) * t)) = 2 := by
  have hrew : (fun t : ℝ => (2 * w) * (1 - (w / 2) * t)) = fun t => (2 * w) - w ^ 2 * t := by
    funext t
    ring
  rw [hrew]
  have hf : IntervalIntegrable (fun _ : ℝ => (2 * w)) volume 0 (2 / w) :=
    Continuous.intervalIntegrable continuous_const 0 (2 / w)
  have hg : IntervalIntegrable (fun t : ℝ => w ^ 2 * t) volume 0 (2 / w) :=
    Continuous.intervalIntegrable (continuous_const.mul continuous_id) 0 (2 / w)
  calc
    (∫ t in (0:ℝ)..(2 / w), (2 * w) - w ^ 2 * t)
        = (∫ t in (0:ℝ)..(2 / w), (2 * w)) - (∫ t in (0:ℝ)..(2 / w), w ^ 2 * t) := by
          exact intervalIntegral.integral_sub hf hg
    _ = (2 / w) * (2 * w) - (w ^ 2) * ((2 / w) ^ 2 / 2) := by
          rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
          ring
    _ = 2 := by
          field_simp [hw.ne']
          ring

/-- The bump, in closed form: `B(x) = 2·sinc((x−a)/w)²`. -/
def levyBump (a w : ℝ) (x : ℝ) : ℝ := 2 * (Real.sinc ((x - a) / w)) ^ 2

/-- The bump equals the interval-integral expression pointwise. -/
lemma levyBump_eq_integral (a w x : ℝ) (hw : 0 < w) :
    levyBump a w x = ∫ t in (0:ℝ)..(2 / w), (2 * w) * (1 - (w / 2) * t) * Real.cos (t * (x - a)) := by
  unfold levyBump
  by_cases hv0 : x - a = 0
  · have hxa : x = a := sub_eq_zero.mp hv0
    subst x
    -- value at a: both sides are 2
    have hzero : (∫ t in (0:ℝ)..(2 / w), (2 * w) * (1 - (w / 2) * t) * Real.cos (t * (a - a))) = 2 := by
      calc
        (∫ t in (0:ℝ)..(2 / w), (2 * w) * (1 - (w / 2) * t) * Real.cos (t * (a - a)))
            = (∫ t in (0:ℝ)..(2 / w), (2 * w) * (1 - (w / 2) * t)) := by
              apply intervalIntegral.integral_congr
              intro t ht
              simp
        _ = 2 := integral_tapered_const w hw
    rw [hzero]
    simp
  · -- v ≠ 0: use integral_tapered_cos
    have hv : x - a ≠ 0 := hv0
    have hval := integral_tapered_cos w (x - a) hw hv
    have hmain : (∫ t in (0:ℝ)..(2 / w), (2 * w) * (1 - (w / 2) * t) * Real.cos (t * (x - a)))
        = w ^ 2 * (1 - Real.cos (2 * (x - a) / w)) / (x - a) ^ 2 := by
      calc
        (∫ t in (0:ℝ)..(2 / w), (2 * w) * (1 - (w / 2) * t) * Real.cos (t * (x - a)))
            = (∫ t in (0:ℝ)..(2 / w), (2 * w) * ((1 - (w / 2) * t) * Real.cos (t * (x - a)))) := by
              apply intervalIntegral.integral_congr
              intro t ht
              ring
        _ = (2 * w) * (∫ t in (0:ℝ)..(2 / w), (1 - (w / 2) * t) * Real.cos (t * (x - a))) := by
              rw [intervalIntegral.integral_const_mul]
        _ = (2 * w) * ((w / 2) * (1 - Real.cos ((x - a) * (2 / w))) / (x - a) ^ 2) := by rw [hval]
        _ = w ^ 2 * (1 - Real.cos (2 * (x - a) / w)) / (x - a) ^ 2 := by
              ring_nf
    have hu : (x - a) / w ≠ 0 := by
      exact div_ne_zero hv (ne_of_gt hw)
    calc
      2 * (Real.sinc ((x - a) / w)) ^ 2
          = 2 * (Real.sin ((x - a) / w) / ((x - a) / w)) ^ 2 := by
            rw [Real.sinc_of_ne_zero hu]
      _ = w ^ 2 * (1 - Real.cos (2 * (x - a) / w)) / (x - a) ^ 2 := by
            have hθ : 2 * (x - a) / w = 2 * ((x - a) / w) := by ring
            rw [hθ, one_sub_cos_two_mul_sq]
            field_simp [hv]
      _ = (∫ t in (0:ℝ)..(2 / w), (2 * w) * (1 - (w / 2) * t) * Real.cos (t * (x - a))) := hmain.symm

/-- The bump is nonnegative. -/
lemma levyBump_nonneg (a w x : ℝ) : 0 ≤ levyBump a w x := by
  unfold levyBump
  positivity

/-- The bump is at least 1 on the interval `Icc (a-w) (a+w)`. -/
lemma levyBump_ge_one (a w x : ℝ) (hw : 0 < w) (hx : x ∈ Set.Icc (a - w) (a + w)) :
    (1 : ℝ) ≤ levyBump a w x := by
  unfold levyBump
  have hu_le : |(x - a) / w| ≤ 1 := by
    have hva : |x - a| ≤ w := by
      rw [abs_le]
      constructor <;> nlinarith [(Set.mem_Icc.mp hx).1, (Set.mem_Icc.mp hx).2]
    rw [abs_div, abs_of_pos hw]
    rw [div_le_iff₀ hw]
    simpa using hva
  have h2 : (2 : ℝ) * Real.sin ((x - a) / w) ^ 2 ≥ ((x - a) / w) ^ 2 := sin_sq_ge_half_sq hu_le
  by_cases hu0 : (x - a) / w = 0
  · rw [hu0]
    simp [Real.sinc]
  · rw [Real.sinc_of_ne_zero hu0]
    have hu2pos : 0 < ((x - a) / w) ^ 2 := sq_pos_of_ne_zero hu0
    have hdiv : (1 : ℝ) ≤ 2 * Real.sin ((x - a) / w) ^ 2 / ((x - a) / w) ^ 2 := by
      rw [le_div_iff₀ hu2pos]
      simpa using h2
    rw [div_pow]
    simpa [mul_div_assoc] using hdiv

/-- Integral of the indicator function equals the measure. -/
lemma integral_indicator_one (μ : Measure ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    (∫ x, (Set.indicator s (fun _ => (1 : ℝ))) x ∂μ) = μ.real s := by
  rw [integral_indicator hs]
  simpa using (setIntegral_const (s := s) (μ := μ) (1 : ℝ))

/-- The bump is bounded above by 2. -/
lemma levyBump_le_two (a w x : ℝ) : levyBump a w x ≤ 2 := by
  unfold levyBump
  have hs : |Real.sinc ((x - a) / w)| ≤ (1 : ℝ) := by
    simpa using Real.abs_sinc_le_one ((x - a) / w)
  have hsq : (Real.sinc ((x - a) / w)) ^ 2 ≤ 1 := by
    rcases abs_le.mp hs with ⟨hn, hp⟩
    nlinarith
  nlinarith [sq_nonneg (Real.sinc ((x - a) / w))]

/-- Interval mass bounded by the integral of the bump. -/
lemma measureReal_Icc_le_integral_bump (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a w : ℝ) (hw : 0 < w) :
    μ.real (Set.Icc (a - w) (a + w)) ≤ ∫ x, levyBump a w x ∂μ := by
  let I : Set ℝ := Set.Icc (a - w) (a + w)
  let ch : ℝ → ℝ := fun x => if x ∈ I then (1 : ℝ) else 0
  have hch_eq : ch = Set.indicator I (fun _ => (1 : ℝ)) := by
    funext x
    by_cases hx : x ∈ I <;> simp [ch, hx]
  have hle : ch ≤ levyBump a w := by
    intro x
    by_cases hx : x ∈ I
    · have hge : (1 : ℝ) ≤ levyBump a w x := levyBump_ge_one a w x hw hx
      simp [ch, hx, hge]
    · have hnon := levyBump_nonneg a w x
      simp [ch, hx]
      exact hnon
  have h_int_ch : (∫ x, ch x ∂μ) = μ.real I := by
    rw [hch_eq]
    rw [integral_indicator_one μ measurableSet_Icc]
  have hch_meas : Measurable ch := by
    rw [hch_eq]
    exact measurable_const.indicator (by simpa [I] using measurableSet_Icc)
  have hch_int : Integrable ch μ := by
    refine Integrable.of_bound hch_meas.aestronglyMeasurable 1 ?_
    apply ae_of_all
    intro x
    unfold ch
    by_cases hx : x ∈ I <;> simp [hx]
  have hB_meas : Measurable (levyBump a w) := by
    unfold levyBump
    fun_prop
  have hB_int : Integrable (levyBump a w) μ := by
    refine Integrable.of_bound hB_meas.aestronglyMeasurable 2 ?_
    apply ae_of_all
    intro x
    have hb : 0 ≤ levyBump a w x := levyBump_nonneg a w x
    rw [Real.norm_eq_abs, abs_of_nonneg hb]
    exact levyBump_le_two a w x
  have hmono : (∫ x, ch x ∂μ) ≤ ∫ x, levyBump a w x ∂μ := integral_mono hch_int hB_int hle
  rwa [h_int_ch] at hmono

/-- Bound for the taper function. -/
lemma taper_bound (w t c : ℝ) (hw : 0 < w) (ht0 : 0 ≤ t) (ht2 : t ≤ 2 / w) (hc : |c| ≤ 1) :
    |(2 * w) * (1 - (w / 2) * t) * c| ≤ 2 * w := by
  have hwt : (w / 2) * t ≤ 1 := by
    have hstep : (w / 2) * t ≤ (w / 2) * (2 / w) := mul_le_mul_of_nonneg_left ht2 (by positivity)
    have hfin : (w / 2) * (2 / w) = 1 := by field_simp [ne_of_gt hw]
    nlinarith
  have h01 : 0 ≤ 1 - (w / 2) * t := by nlinarith
  have h02 : 1 - (w / 2) * t ≤ 1 := by nlinarith
  calc
    |(2 * w) * (1 - (w / 2) * t) * c| = |(2 * w)| * |(1 - (w / 2) * t)| * |c| := by
      rw [abs_mul, abs_mul]
    _ = (2 * w) * (1 - (w / 2) * t) * |c| := by
      rw [abs_of_pos (by positivity : (0 : ℝ) < 2 * w), abs_of_nonneg h01]
    _ ≤ (2 * w) * 1 * |c| := by
      gcongr
    _ ≤ (2 * w) * 1 * 1 := by
      gcongr
    _ = 2 * w := by
      ring

/-- Fubini-based spectral identity for the bump. -/
lemma integral_bump_eq_spectral (μ : Measure ℝ) [IsProbabilityMeasure μ] (a w : ℝ) (hw : 0 < w) :
    (∫ x, levyBump a w x ∂μ) =
      ∫ t in (0:ℝ)..(2 / w), (2 * w) * (1 - (w / 2) * t) *
        (∫ x, Real.cos (t * (x - a)) ∂μ) := by
  haveI : IsFiniteMeasure μ := ⟨by rw [IsProbabilityMeasure.measure_univ]; exact ENNReal.one_lt_top⟩
  let T : ℝ := 2 / w
  let c : ℝ → ℝ := fun t => (2 * w) * (1 - (w / 2) * t)
  have hT : 0 < T := by dsimp [T]; positivity
  have hT0 : 0 ≤ T := le_of_lt hT
  have hc_eq : c = fun t => (2 * w) * (1 - (w / 2) * t) := rfl
  let ν : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) T)
  haveI hν : IsFiniteMeasure ν := by
    dsimp [ν]
    constructor
    rw [Measure.restrict_apply MeasurableSet.univ]
    simp
  let F : ℝ → ℝ → ℝ := fun x t => c t * Real.cos (t * (x - a))
  have hF_meas : AEStronglyMeasurable (Function.uncurry F) (μ.prod ν) := by
    apply Continuous.aestronglyMeasurable
    fun_prop
  have hF_int : Integrable (Function.uncurry F) (μ.prod ν) := by
    refine Integrable.of_bound hF_meas (2 * w) ?_
    -- bound on product
    have hb : ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ x : ℝ, ‖F x t‖ ≤ 2 * w := by
      intro t ht x
      have ht2 : t ≤ 2 / w := by dsimp [T] at ht; exact ht.2
      simpa [F, c] using taper_bound w t (Real.cos (t * (x - a))) hw (le_of_lt ht.1) ht2
        (Real.abs_cos_le_one _)
    -- ∀ᵐ t ∂ν: ∀ x bound  -- then to product
    have hνb : ∀ᵐ t ∂ν, ∀ x : ℝ, ‖F x t‖ ≤ 2 * w := by
      filter_upwards [ae_restrict_mem (s := Set.Ioc (0 : ℝ) T) measurableSet_Ioc] with t ht
      exact hb t ht
    have hμν : ∀ᵐ p : ℝ × ℝ ∂(μ.prod ν), ‖Function.uncurry F p‖ ≤ 2 * w := by
      -- ∀ᵐ x ∂μ: ∀ᵐ t ∂ν: bound p (x,t)
      rw [MeasureTheory.Measure.ae_prod_iff_ae_ae]
      · apply ae_of_all
        intro x
        exact hνb.mono (fun t ht => ht x)
      · -- measurable set {p | ‖F p.1 p.2‖ ≤ 2w}
        have hcontF : Continuous (fun p : ℝ × ℝ => ‖Function.uncurry F p‖) := by
          dsimp [F, c]
          fun_prop
        exact (measurableSet_Iic : MeasurableSet (Set.Iic (2 * w))).preimage hcontF.measurable
    exact hμν
  -- Step 1
  have step1 : (∫ x, levyBump a w x ∂μ) = ∫ x, (∫ t in (0:ℝ)..T, F x t) ∂μ := by
    refine MeasureTheory.integral_congr_ae ?_
    apply ae_of_all
    intro x
    dsimp [F, c, T]
    exact levyBump_eq_integral a w x hw
  -- Step 2: interval → ν
  have step2 : (∫ x, (∫ t in (0:ℝ)..T, F x t) ∂μ) = ∫ x, (∫ t, F x t ∂ν) ∂μ := by
    refine MeasureTheory.integral_congr_ae ?_
    apply ae_of_all
    intro x
    dsimp [ν]
    rw [intervalIntegral.integral_of_le hT0]
  -- Step 3: Fubini
  have step3 : (∫ x, (∫ t, F x t ∂ν) ∂μ) = ∫ t, (∫ x, F x t ∂μ) ∂ν := by
    rw [MeasureTheory.integral_integral (f := F) hF_int]
    exact MeasureTheory.integral_prod_symm (fun p : ℝ × ℝ => F p.1 p.2) hF_int
  -- Step 4: back
  have step4 : (∫ t, (∫ x, F x t ∂μ) ∂ν) = ∫ t in (0:ℝ)..T, (∫ x, F x t ∂μ) := by
    dsimp [ν]
    rw [← intervalIntegral.integral_of_le hT0]
  -- Step 5: inner integral
  have step5 : ∀ t : ℝ, (∫ x, F x t ∂μ) = c t * (∫ x, Real.cos (t * (x - a)) ∂μ) := by
    intro t
    dsimp [F, c]
    rw [MeasureTheory.integral_const_mul]
  calc
    (∫ x, levyBump a w x ∂μ)
        = ∫ x, (∫ t in (0:ℝ)..T, F x t) ∂μ := step1
    _ = ∫ x, (∫ t, F x t ∂ν) ∂μ := step2
    _ = ∫ t, (∫ x, F x t ∂μ) ∂ν := step3
    _ = ∫ t in (0:ℝ)..T, (∫ x, F x t ∂μ) := step4
    _ = ∫ t in (0:ℝ)..T, c t * (∫ x, Real.cos (t * (x - a)) ∂μ) := by
          apply intervalIntegral.integral_congr
          intro t ht
          exact step5 t
    _ = ∫ t in (0:ℝ)..(2 / w), (2 * w) * (1 - (w / 2) * t) *
          (∫ x, Real.cos (t * (x - a)) ∂μ) := by
          dsimp [T, c]

/-- Real part of `exp(θ·I)` is `cos θ`. -/
lemma exp_I_re (θ : ℝ) : (Complex.exp (↑θ * Complex.I)).re = Real.cos θ := by
  rw [Complex.exp_mul_I]
  simp [Complex.add_re, Complex.mul_re, Complex.cos_ofReal_re, Complex.sin_ofReal_im]

/-- Real part of the characteristic function against `cos`. -/
lemma integral_cos_eq_re_char (μ : Measure ℝ) [IsProbabilityMeasure μ] (t a : ℝ) :
    (∫ x, Real.cos (t * (x - a)) ∂μ) =
      (Complex.exp (↑(-(t * a)) * Complex.I) * charFun μ t).re := by
  haveI : IsFiniteMeasure μ := ⟨by rw [IsProbabilityMeasure.measure_univ]; exact ENNReal.one_lt_top⟩
  have hf_int : Integrable (fun x : ℝ => Complex.exp (↑(t * (x - a)) * Complex.I)) μ := by
    refine Integrable.of_bound (by fun_prop) 1 ?_
    apply ae_of_all
    intro x
    simpa using (Complex.norm_exp_ofReal_mul_I (t * (x - a)) : ‖Complex.exp (↑(t * (x - a)) * Complex.I)‖ = 1).le
  calc
    (∫ x, Real.cos (t * (x - a)) ∂μ)
        = (∫ x, (Complex.exp (↑(t * (x - a)) * Complex.I)).re ∂μ) := by
          refine MeasureTheory.integral_congr_ae ?_
          apply ae_of_all
          intro x
          exact (exp_I_re (t * (x - a))).symm
    _ = (∫ x, Complex.exp (↑(t * (x - a)) * Complex.I) ∂μ).re := by
          change (∫ x, RCLike.re (Complex.exp (↑(t * (x - a)) * Complex.I)) ∂μ) =
              RCLike.re (∫ x, Complex.exp (↑(t * (x - a)) * Complex.I) ∂μ)
          exact integral_re hf_int
    _ = (Complex.exp (↑(-(t * a)) * Complex.I) * charFun μ t).re := by
          congr 1
          have hsplit : (fun x : ℝ => Complex.exp (↑(t * (x - a)) * Complex.I)) =
              fun x => Complex.exp (↑(-(t * a)) * Complex.I) *
                Complex.exp (↑(t * x) * Complex.I) := by
            funext x
            rw [← Complex.exp_add]
            congr 1
            have harg : (↑(-(t * a)) + ↑(t * x) : ℂ) = ↑(t * (x - a)) := by
              rw [← Complex.ofReal_add]
              congr 1
              ring
            rw [← harg]
            ring
          rw [hsplit]
          have hXφ : (∫ x : ℝ, Complex.exp (↑(t * x) * Complex.I) ∂μ) = charFun μ t := by
            have hrew2 : (fun x : ℝ => Complex.exp (↑(t * x) * Complex.I)) =
                (fun x : ℝ => Complex.exp (↑t * ↑x * Complex.I)) := by
              funext x
              congr 1
              rw [Complex.ofReal_mul]
            rw [hrew2]
            rw [← charFun_apply_real]
          rw [MeasureTheory.integral_const_mul]
          rw [hXφ]

lemma cos_integral_le_charFun_norm (μ : Measure ℝ) [IsProbabilityMeasure μ] (t a : ℝ) :
    (∫ x, Real.cos (t * (x - a)) ∂μ) ≤ ‖charFun μ t‖ := by
  calc
    (∫ x, Real.cos (t * (x - a)) ∂μ)
        = (Complex.exp (↑(-(t * a)) * Complex.I) * charFun μ t).re :=
          integral_cos_eq_re_char μ t a
    _ ≤ ‖Complex.exp (↑(-(t * a)) * Complex.I) * charFun μ t‖ := Complex.re_le_norm _
    _ = ‖charFun μ t‖ := by
          rw [Complex.norm_mul, Complex.norm_exp_ofReal_mul_I]
          simp

/-- `∫_0^T f ≤ ∫_{-T}^T f` for globally nonnegative `f`. -/
lemma interval_integral_zero_le_symm {f : ℝ → ℝ} {T : ℝ} (hT0 : 0 ≤ T)
    (hf0 : IntervalIntegrable f volume 0 T) (hfneg : IntervalIntegrable f volume (-T) 0)
    (hfpos : ∀ t, 0 ≤ f t) :
    (∫ t in (0:ℝ)..T, f t) ≤ ∫ t in -T..T, f t := by
  have hsplit : (∫ t in -T..T, f t) = (∫ t in -T..(0:ℝ), f t) + ∫ t in (0:ℝ)..T, f t := by
    rw [intervalIntegral.integral_add_adjacent_intervals hfneg hf0]
  have h1 : 0 ≤ ∫ t in -T..(0:ℝ), f t := by
    refine intervalIntegral.integral_nonneg_of_ae ?_ ?_
    · linarith
    · apply ae_of_all
      intro t
      exact hfpos t
  linarith

/-- Classical Lévy inequality: interval mass bounded by a universal constant times the integral
of |charFun| over the dual window. -/
theorem levy_interval_mass_bound (μ : Measure ℝ) [MeasureTheory.IsProbabilityMeasure μ]
    (a w : ℝ) (hw : 0 < w) :
    μ.real (Set.Icc (a - w) (a + w)) ≤
      8 * w * ∫ t in (-(2 / w))..(2 / w), ‖charFun μ t‖ := by
  haveI : IsFiniteMeasure μ := ⟨by rw [IsProbabilityMeasure.measure_univ]; exact ENNReal.one_lt_top⟩
  let T : ℝ := 2 / w
  have hT : 0 < T := by dsimp [T]; positivity
  have hT0 : 0 ≤ T := le_of_lt hT
  let c : ℝ → ℝ := fun t => (2 * w) * (1 - (w / 2) * t)
  let g : ℝ → ℝ := fun t => ∫ x, Real.cos (t * (x - a)) ∂μ
  let φn : ℝ → ℝ := fun t => ‖charFun μ t‖
  have hφ0 : ∀ t, 0 ≤ φn t := by
    intro t
    dsimp [φn]
    exact norm_nonneg _
  have hgφ : ∀ t, g t ≤ φn t := by
    intro t
    dsimp [g, φn]
    exact cos_integral_le_charFun_norm μ t a
  have hc_bounds : ∀ t ∈ Set.Icc 0 T, 0 ≤ c t ∧ c t ≤ 2 * w := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have ht2 : t ≤ 2 / w := by dsimp [T] at ht; exact ht.2
    have hwt : (w / 2) * t ≤ 1 := by
      have hstep : (w / 2) * t ≤ (w / 2) * (2 / w) := mul_le_mul_of_nonneg_left ht2 (by positivity)
      have hfin : (w / 2) * (2 / w) = 1 := by field_simp [hw.ne']
      nlinarith
    dsimp [c]
    have h01 : 0 ≤ 1 - (w / 2) * t := by nlinarith
    have h02 : 1 - (w / 2) * t ≤ 1 := by nlinarith
    constructor
    · exact mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * w) h01
    · have hle : (2 * w) * (1 - (w / 2) * t) ≤ (2 * w) * 1 :=
        mul_le_mul_of_nonneg_left h02 (by positivity : (0 : ℝ) ≤ 2 * w)
      simpa using hle
  -- continuity facts
  have hc_cont : Continuous c := by dsimp [c]; fun_prop
  have hφ_cont : Continuous φn := by dsimp [φn]; fun_prop
  have hg_cont : Continuous g := by
    have hfun : g = fun t => (Complex.exp (↑(-(t * a)) * Complex.I) * charFun μ t).re := by
      funext t
      dsimp [g]
      exact integral_cos_eq_re_char μ t a
    rw [hfun]
    fun_prop
  have hInt_cg : IntervalIntegrable (fun t => c t * g t) volume 0 T :=
    (hc_cont.mul hg_cont).intervalIntegrable 0 T
  have hInt_cφ : IntervalIntegrable (fun t => c t * φn t) volume 0 T :=
    (hc_cont.mul hφ_cont).intervalIntegrable 0 T
  have hInt_cφ' : IntervalIntegrable (fun t => c t * φn t) volume 0 (2 / w) := by
    simpa [T] using hInt_cφ
  have hInt_2φ : IntervalIntegrable (fun t => (2 * w) * φn t) volume 0 T :=
    (continuous_const.mul hφ_cont).intervalIntegrable 0 T
  have hInt_φ0 : IntervalIntegrable φn volume 0 T := hφ_cont.intervalIntegrable 0 T
  have hInt_φneg : IntervalIntegrable φn volume (-T) 0 := hφ_cont.intervalIntegrable (-T) 0
  have hInt_φsym : IntervalIntegrable φn volume (-T) T := hφ_cont.intervalIntegrable (-T) T
  have hspec := integral_bump_eq_spectral μ a w hw
  calc
    μ.real (Set.Icc (a - w) (a + w)) ≤ ∫ x, levyBump a w x ∂μ :=
      measureReal_Icc_le_integral_bump μ a w hw
    _ = ∫ t in (0:ℝ)..T, c t * g t := by
          simpa [T, c, g] using hspec
    _ ≤ ∫ t in (0:ℝ)..T, c t * φn t := by
          refine intervalIntegral.integral_mono_on hT0 hInt_cg hInt_cφ ?_
          intro t ht
          exact mul_le_mul_of_nonneg_left (hgφ t) (hc_bounds t ht).1
    _ ≤ ∫ t in (0:ℝ)..T, (2 * w) * φn t := by
          refine intervalIntegral.integral_mono_on hT0 hInt_cφ hInt_2φ ?_
          intro t ht
          exact mul_le_mul_of_nonneg_right (hc_bounds t ht).2 (hφ0 t)
    _ = (2 * w) * ∫ t in (0:ℝ)..T, φn t := by
          rw [intervalIntegral.integral_const_mul]
    _ ≤ (2 * w) * ∫ t in -T..T, φn t := by
          have hwin : (∫ t in (0:ℝ)..T, φn t) ≤ ∫ t in -T..T, φn t :=
            interval_integral_zero_le_symm hT0 hInt_φ0 hInt_φneg hφ0
          exact mul_le_mul_of_nonneg_left hwin (by positivity : (0 : ℝ) ≤ 2 * w)
    _ ≤ (8 * w) * ∫ t in -T..T, φn t := by
          have hX : 0 ≤ ∫ t in -T..T, φn t := by
            refine intervalIntegral.integral_nonneg_of_ae ?_ ?_
            · dsimp [T]; linarith [hT]
            · apply ae_of_all
              intro t
              exact hφ0 t
          have hw4 : (2 * w : ℝ) ≤ 8 * w := by nlinarith
          exact mul_le_mul_of_nonneg_right hw4 hX
    _ ≤ 8 * w * ∫ t in (-(2 / w))..(2 / w), ‖charFun μ t‖ := by
          have heq : (8 * w) * ∫ t in -T..T, φn t = 8 * w * ∫ t in (-(2 / w))..(2 / w), ‖charFun μ t‖ := by
            simp [T, φn]
          rw [heq]

end Commons.Probability.Levy