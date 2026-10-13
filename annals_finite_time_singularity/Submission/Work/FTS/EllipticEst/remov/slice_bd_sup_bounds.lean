import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.cs_integral
import Submission.Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

noncomputable section

/-! ## Elementary one-dimensional tools for the slice estimate -/

/-- On the open slice `(0, π/2)` the weight `sEta = sin(2θ)^{-η}` is at least `1`. -/
private lemma one_le_sEta {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    1 ≤ Work.FTS.EllipticEst.sEta θ := by
  rw [Work.FTS.EllipticEst.sEta]
  refine Real.one_le_rpow_of_pos_of_le_one_of_nonpos ?_ ?_ ?_
  · exact Real.sin_pos_of_mem_Ioo ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  · exact Real.sin_le_one _
  · have hη : (0 : ℝ) < Work.Spaces.eta := by norm_num [Work.Spaces.eta]
    linarith

/-- On the slice `Iθ` the weight `sEta` is nonnegative. -/
private lemma sEta_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.sEta θ := by
  rw [Work.FTS.EllipticEst.sEta]
  exact Real.rpow_nonneg
    (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _

/-- The mean-value property of the integral: a continuous function on `[a,b]` takes its average
value at some point of `[a,b]`. -/
private lemma exists_eq_average {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) :
    ∃ x ∈ Set.Icc a b, f x = (∫ t in Set.Icc a b, f t) / (b - a) := by
  have h1 : ContinuousOn f (Set.uIcc a b) := by
    rwa [Set.uIcc_of_le hab.le]
  obtain ⟨c, hc, hcc⟩ := exists_eq_const_mul_intervalIntegral_of_nonneg
    (f := f) (g := fun _ : ℝ => (1 : ℝ)) (μ := volume) (a := a) (b := b) h1
    intervalIntegrable_const (fun x _ => zero_le_one)
  have hc' : c ∈ Set.Icc a b := by rwa [Set.uIcc_of_le hab.le] at hc
  refine ⟨c, hc', ?_⟩
  have hL : (∫ x in a..b, f x * 1) = ∫ x in a..b, f x := by simp
  have hR : (∫ x in a..b, (1 : ℝ)) = b - a := by
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_one]
  have hset : (∫ x in a..b, f x) = ∫ x in Set.Icc a b, f x := by
    rw [intervalIntegral.integral_of_le hab.le, MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [hL, hR, hset] at hcc
  rw [hcc, mul_div_cancel_right₀ _ (by linarith)]

/-- If `g²·sEta` is integrable on `Iθ` then so are `g²` and `|g|`, and `∫ g² ≤ ∫ g²·sEta`. -/
private lemma integrableOn_sq_of_sq_mul_sEta {g : ℝ → ℝ}
    (hmeas : AEStronglyMeasurable g (volume.restrict Work.Spaces.Iθ))
    (h : IntegrableOn (fun θ => (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ) :
    IntegrableOn (fun θ => (g θ) ^ 2) Work.Spaces.Iθ
      ∧ IntegrableOn (fun θ => |g θ|) Work.Spaces.Iθ
      ∧ (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2)
          ≤ ∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  have hae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      1 ≤ Work.FTS.EllipticEst.sEta θ := by
    have hIoo : (volume.restrict (Set.Ioo 0 (Real.pi / 2)))
        = volume.restrict Work.Spaces.Iθ :=
      Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc
    rw [← hIoo, MeasureTheory.ae_restrict_iff' isOpen_Ioo.measurableSet]
    exact Eventually.of_forall (fun x hx => one_le_sEta hx)
  have hsq_le : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (g θ) ^ 2 ≤ (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
    filter_upwards [hae] with θ hθ
    simpa using mul_le_mul_of_nonneg_left hθ (sq_nonneg (g θ))
  have hint_sq : IntegrableOn (fun θ => (g θ) ^ 2) Work.Spaces.Iθ := by
    refine Integrable.mono' h (hmeas.pow 2) ?_
    filter_upwards [hsq_le] with θ hθ
    rwa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (g θ))]
  haveI : IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) := ⟨by
    rw [Measure.restrict_apply_univ, Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top⟩
  have hint_abs : IntegrableOn (fun θ => |g θ|) Work.Spaces.Iθ := by
    refine (hint_sq.add (integrable_const (1 : ℝ))).mono' ?_ ?_
    · simpa only [Real.norm_eq_abs] using hmeas.norm
    · filter_upwards with θ
      have h1 : |g θ| ≤ (g θ) ^ 2 + 1 := by
        nlinarith [sq_nonneg (|g θ| - 1), sq_abs (g θ), abs_nonneg (g θ)]
      simpa only [Pi.add_apply, Real.norm_eq_abs, abs_abs] using h1
  refine ⟨hint_sq, hint_abs, ?_⟩
  refine integral_mono_ae hint_sq h hsq_le

/-- Cauchy–Schwarz on the slice: `∫|f| ≤ √(π/2) √(∫ f²)`. -/
private lemma integral_abs_le_sqrt_pi_div_two {f : ℝ → ℝ}
    (hmeas : AEStronglyMeasurable f (volume.restrict Work.Spaces.Iθ))
    (h : IntegrableOn (fun x => f x ^ 2) Work.Spaces.Iθ) :
    ∫ x in Work.Spaces.Iθ, |f x|
      ≤ Real.sqrt (Real.pi / 2) * Real.sqrt (∫ x in Work.Spaces.Iθ, f x ^ 2) := by
  haveI : IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) := ⟨by
    rw [Measure.restrict_apply_univ, Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top⟩
  have hmeas_abs : AEStronglyMeasurable (fun x => |f x|) (volume.restrict Work.Spaces.Iθ) := by
    simpa only [Real.norm_eq_abs] using hmeas.norm
  have hmemLp_abs : MemLp (fun x => |f x|) 2 (volume.restrict Work.Spaces.Iθ) := by
    refine (memLp_two_iff_integrable_sq hmeas_abs).mpr ?_
    refine h.congr (Eventually.of_forall (fun x => (sq_abs (f x)).symm))
  have hone : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume.restrict Work.Spaces.Iθ) := memLp_const 1
  have hcs : |∫ x in Work.Spaces.Iθ, |f x| * 1|
      ≤ Real.sqrt (∫ x in Work.Spaces.Iθ, |f x| ^ 2)
        * Real.sqrt (∫ x in Work.Spaces.Iθ, (1 : ℝ) ^ 2) := by
    simpa only [mul_one] using Ebs.abs_integral_mul_le_sqrt hmemLp_abs hone
  have hInt1 : (∫ x in Work.Spaces.Iθ, (1 : ℝ) ^ 2) = Real.pi / 2 := by
    rw [Work.Spaces.Iθ, one_pow, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2),
      intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero]
  have hsq : (∫ x in Work.Spaces.Iθ, |f x| ^ 2) = ∫ x in Work.Spaces.Iθ, f x ^ 2 :=
    integral_congr_ae (Eventually.of_forall (fun x => sq_abs (f x)))
  have hnonneg : 0 ≤ ∫ x in Work.Spaces.Iθ, |f x| :=
    integral_nonneg (fun x => abs_nonneg (f x))
  simp only [mul_one] at hcs
  rw [hsq, hInt1, abs_of_nonneg hnonneg, mul_comm] at hcs
  exact hcs

/-- A bound for `deriv u` on the *open* interval extends to the closed interval: at an endpoint
either `u` fails to be differentiable there (and Mathlib's `deriv` is `0`), or the two-sided
derivative agrees with the one-sided limit of the slopes, which the mean value theorem bounds by
the interior bound. -/
private lemma deriv_endpoint_bound {u : ℝ → ℝ} {K a b : ℝ} (hab : a < b) (hK : 0 ≤ K)
    (hcont : ContinuousOn u (Set.Icc a b))
    (hdiff : DifferentiableOn ℝ u (Set.Ioo a b))
    (hbd : ∀ t ∈ Set.Ioo a b, |deriv u t| ≤ K) :
    ∀ x ∈ Set.Icc a b, |deriv u x| ≤ K := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with hxa | hxa
  · rw [← hxa]
    by_cases hd : DifferentiableAt ℝ u a
    · have hev : ∀ᶠ θ in 𝓝[>] a, |slope u a θ| ≤ K := by
        filter_upwards [self_mem_nhdsWithin,
          nhdsWithin_le_nhds (Iio_mem_nhds hab)] with θ h1 h2
        obtain ⟨c, hc, hcs⟩ := exists_deriv_eq_slope u h1
          (hcont.mono (fun t ht => ⟨ht.1, le_trans ht.2 h2.le⟩))
          (hdiff.mono (fun t ht => ⟨ht.1, lt_trans ht.2 h2⟩))
        rw [slope_def_field, ← hcs]
        exact hbd c ⟨hc.1, lt_trans hc.2 h2⟩
      have hslope : Tendsto (slope u a) (𝓝[>] a) (𝓝 (deriv u a)) :=
        hd.hasDerivAt.tendsto_slope.mono_left
          (nhdsWithin_mono a (fun t ht => ne_of_gt ht))
      simpa using le_of_tendsto hslope.abs hev
    · rw [deriv_zero_of_not_differentiableAt hd, abs_zero]
      exact hK
  · rcases eq_or_lt_of_le hx.2 with hxb | hxb
    · rw [hxb]
      by_cases hd : DifferentiableAt ℝ u b
      · have hev : ∀ᶠ θ in 𝓝[<] b, |slope u b θ| ≤ K := by
          filter_upwards [self_mem_nhdsWithin,
            nhdsWithin_le_nhds (Ioi_mem_nhds hab)] with θ h1 h2
          obtain ⟨c, hc, hcs⟩ := exists_deriv_eq_slope u h1
            (hcont.mono (fun t ht => ⟨le_trans h2.le ht.1, ht.2⟩))
            (hdiff.mono (fun t ht => ⟨lt_trans h2 ht.1, ht.2⟩))
          have hθb : θ < b := h1
          have hne1 : θ - b ≠ 0 := sub_ne_zero.mpr (by linarith : θ ≠ b)
          have hne2 : b - θ ≠ 0 := sub_ne_zero.mpr (by linarith : b ≠ θ)
          have hsl : slope u b θ = (u b - u θ) / (b - θ) := by
            rw [slope_def_field, div_eq_div_iff hne1 hne2]
            ring
          rw [hsl, ← hcs]
          exact hbd c ⟨lt_trans h2 hc.1, hc.2⟩
        have hslope : Tendsto (slope u b) (𝓝[<] b) (𝓝 (deriv u b)) :=
          hd.hasDerivAt.tendsto_slope.mono_left
            (nhdsWithin_mono b (fun t ht => ne_of_lt ht))
        simpa using le_of_tendsto hslope.abs hev
      · rw [deriv_zero_of_not_differentiableAt hd, abs_zero]
        exact hK
    · exact hbd x ⟨hxa, hxb⟩

/-- A pointwise inequality on the open interval extends to the closed interval when both sides
are continuous there. -/
private lemma le_on_Icc_of_le_on_Ioo {f g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b))
    (h : ∀ x ∈ Set.Ioo a b, f x ≤ g x) : ∀ x ∈ Set.Icc a b, f x ≤ g x := by
  intro x hx
  have hxcl : x ∈ closure (Set.Ioo a b) := by
    rw [closure_Ioo hab.ne]; exact hx
  obtain ⟨u, hu, hut⟩ := mem_closure_iff_seq_limit.mp hxcl
  have hut' : Tendsto u atTop (𝓝[Set.Icc a b] x) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hut, Eventually.of_forall (fun n =>
      ⟨le_of_lt (hu n).1, le_of_lt (hu n).2⟩)⟩
  have hfu : Tendsto (fun n => f (u n)) atTop (𝓝 (f x)) :=
    Tendsto.comp (show Tendsto f (𝓝[Set.Icc a b] x) (𝓝 (f x)) from hf.continuousWithinAt hx)
      hut'
  have hgu : Tendsto (fun n => g (u n)) atTop (𝓝 (g x)) :=
    Tendsto.comp (show Tendsto g (𝓝[Set.Icc a b] x) (𝓝 (g x)) from hg.continuousWithinAt hx)
      hut'
  exact le_of_tendsto_of_tendsto hfu hgu (Eventually.of_forall (fun n => h (u n) (hu n)))

/-- Pointwise `L^∞` bounds on a slice from its weighted `L²` data.

For `u` of class `C³` on `(0, π/2)`, continuous on `[0, π/2]`, with `u (π/2) = 0` and
`(u'')²·sEta`, `(u')²` integrable on `Iθ = [0, π/2]` (here `sEta = sin(2θ)^{-η} ≥ 1`), one has
for every `θ ∈ Iθ`

`|u' θ| ≤ C (√(∫ (u'')² sEta) + √(∫ (u')²))`   and
`|u θ| ≤ (π/2 - θ) · C (√(∫ (u'')² sEta) + √(∫ (u')²))`.

Route: `(u'')² ≤ (u'')² sEta` is integrable, so `|u''|` is integrable; by the mean-value
property of the integral there is `x₀ ∈ [π/4, 3π/8]` with
`|u' x₀|² ≤ (∫_{[π/4,3π/8]} (u')²)/(π/8)`, and then for any `θ ∈ Iθ` the fundamental fact of
calculus gives `|u' θ| ≤ |u' x₀| + ∫_{Iθ} |u''|`, which Cauchy–Schwarz
(`Work.Spaces.cs_integral`) bounds by `C(√(∫(u')²) + √(∫(u'')² sEta))`.  The bound for `u`
follows from `u (π/2) = 0` and `|u θ| ≤ (π/2 - θ) · sup|u'|`. -/
theorem slice_bd_sup_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : ℝ → ℝ),
      ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)) →
      ContinuousOn u (Set.Icc 0 (Real.pi / 2)) →
      u (Real.pi / 2) = 0 →
      MeasureTheory.IntegrableOn
        (fun θ => (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ →
      (∀ θ ∈ Work.Spaces.Iθ,
          |deriv u θ| ≤ C * (Real.sqrt (∫ θ in Work.Spaces.Iθ,
              (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
            + Real.sqrt (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)))
        ∧ (∀ θ ∈ Work.Spaces.Iθ,
          |u θ| ≤ (Real.pi / 2 - θ) * C * (Real.sqrt (∫ θ in Work.Spaces.Iθ,
              (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
            + Real.sqrt (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2))) := by
  refine ⟨2, by norm_num, ?_⟩
  intro u h3 hcont hu_pi hInt2 hInt1
  set A : ℝ := ∫ θ in Work.Spaces.Iθ,
      (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ with hAdef
  set B : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 with hBdef
  have hpi2 : (0 : ℝ) < Real.pi / 2 := by positivity
  have hdiff : DifferentiableOn ℝ u (Set.Ioo 0 (Real.pi / 2)) :=
    h3.differentiableOn (by norm_num)
  have h2 : ContDiffOn ℝ 2 (deriv u) (Set.Ioo 0 (Real.pi / 2)) :=
    h3.deriv_of_isOpen isOpen_Ioo (m := 2) (by norm_num)
  have h2cont : ContinuousOn (deriv u) (Set.Ioo 0 (Real.pi / 2)) := h2.continuousOn
  -- integrability of the second derivative and the `L¹` bound
  have hmeas2 : AEStronglyMeasurable (deriv (deriv u)) (volume.restrict Work.Spaces.Iθ) :=
    (measurable_deriv (deriv u)).aestronglyMeasurable
  obtain ⟨hInt2', hInt2abs, hInt2le⟩ := integrableOn_sq_of_sq_mul_sEta hmeas2 hInt2
  have hL1le : (∫ θ in Work.Spaces.Iθ, |deriv (deriv u) θ|)
      ≤ Real.sqrt (Real.pi / 2) * Real.sqrt A := by
    have hcs := integral_abs_le_sqrt_pi_div_two hmeas2 hInt2'
    have hmono : Real.sqrt (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2)
        ≤ Real.sqrt A := by
      rw [hAdef]; exact Real.sqrt_le_sqrt hInt2le
    exact le_trans hcs (mul_le_mul_of_nonneg_left hmono (Real.sqrt_nonneg _))
  -- the mean-value point in the middle of the slice
  have hderiv_cont : ContinuousOn (deriv u) (Set.Icc (Real.pi / 4) (3 * Real.pi / 8)) :=
    h2cont.mono (fun t ht =>
      ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2, Real.pi_pos]⟩)
  obtain ⟨x0, hx0mem, hx0eq⟩ := exists_eq_average (f := fun θ => (deriv u θ) ^ 2)
    (by linarith [Real.pi_pos] : Real.pi / 4 < 3 * Real.pi / 8) (hderiv_cont.pow 2)
  have hx0Ioo : x0 ∈ Set.Ioo 0 (Real.pi / 2) :=
    ⟨by linarith [hx0mem.1, Real.pi_pos], by linarith [hx0mem.2, Real.pi_pos]⟩
  have hBsub : (∫ θ in Set.Icc (Real.pi / 4) (3 * Real.pi / 8), (deriv u θ) ^ 2) ≤ B := by
    rw [hBdef]
    refine MeasureTheory.setIntegral_mono_set hInt1
      (Eventually.of_forall (fun t => sq_nonneg _)) ?_
    exact Eventually.of_forall (fun t ht =>
      ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2, Real.pi_pos]⟩)
  have hx0bd : |deriv u x0| ≤ Real.sqrt (8 / Real.pi) * Real.sqrt B := by
    have hsq : (deriv u x0) ^ 2 ≤ (8 / Real.pi) * B := by
      have hden : (3 * Real.pi / 8 - Real.pi / 4) = Real.pi / 8 := by ring
      rw [hx0eq, hden, div_eq_mul_inv, inv_div]
      have hcomm : (∫ t in Set.Icc (Real.pi / 4) (3 * Real.pi / 8), (deriv u t) ^ 2)
          * (8 / Real.pi)
          = (8 / Real.pi)
            * (∫ t in Set.Icc (Real.pi / 4) (3 * Real.pi / 8), (deriv u t) ^ 2) := by
        ring
      rw [hcomm]
      exact mul_le_mul_of_nonneg_left hBsub (by positivity)
    have h2' : Real.sqrt ((deriv u x0) ^ 2) ≤ Real.sqrt ((8 / Real.pi) * B) :=
      Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 8 / Real.pi)] at h2'
    simpa only [Real.sqrt_sq_eq_abs] using h2'
  -- the estimate on the open interval
  have hmain : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |deriv u θ| ≤ 2 * (Real.sqrt A + Real.sqrt B) := by
    intro θ hθ
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
    have h1 : ContDiffOn ℝ 1 (deriv u) (Set.uIcc x0 θ) := by
      refine (h2.mono ?_).of_le (by norm_num)
      intro t ht
      rw [Set.mem_uIcc] at ht
      rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨lt_of_lt_of_le hx0Ioo.1 h1, lt_of_le_of_lt h2 hθ.2⟩
      · exact ⟨lt_of_lt_of_le hθ.1 h1, lt_of_le_of_lt h2 hx0Ioo.2⟩
    have hFTC : (∫ t in x0..θ, deriv (deriv u) t) = deriv u θ - deriv u x0 :=
      intervalIntegral.integral_deriv_of_contDiffOn_uIcc h1
    have hstep : |deriv u θ - deriv u x0| ≤ ∫ t in Work.Spaces.Iθ, |deriv (deriv u) t| := by
      rw [← hFTC]
      rcases le_total x0 θ with hle | hle
      · have hb : |∫ t in x0..θ, deriv (deriv u) t|
            ≤ ∫ t in x0..θ, |deriv (deriv u) t| :=
          intervalIntegral.abs_integral_le_integral_abs hle
        have he : (∫ t in x0..θ, |deriv (deriv u) t|)
            = ∫ t in Set.Icc x0 θ, |deriv (deriv u) t| := by
          rw [intervalIntegral.integral_of_le hle, MeasureTheory.integral_Icc_eq_integral_Ioc]
        rw [he] at hb
        exact le_trans hb (MeasureTheory.setIntegral_mono_set hInt2abs
          (Eventually.of_forall (fun t => abs_nonneg _))
          (Eventually.of_forall (fun t ht =>
            ⟨le_trans (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 4)
              (le_trans hx0mem.1 ht.1), le_trans ht.2 hθI.2⟩)))
      · have hsym : (∫ t in x0..θ, deriv (deriv u) t)
            = -(∫ t in θ..x0, deriv (deriv u) t) :=
          intervalIntegral.integral_symm θ x0
        rw [hsym, abs_neg]
        have hb : |∫ t in θ..x0, deriv (deriv u) t|
            ≤ ∫ t in θ..x0, |deriv (deriv u) t| :=
          intervalIntegral.abs_integral_le_integral_abs hle
        have he : (∫ t in θ..x0, |deriv (deriv u) t|)
            = ∫ t in Set.Icc θ x0, |deriv (deriv u) t| := by
          rw [intervalIntegral.integral_of_le hle, MeasureTheory.integral_Icc_eq_integral_Ioc]
        rw [he] at hb
        exact le_trans hb (MeasureTheory.setIntegral_mono_set hInt2abs
          (Eventually.of_forall (fun t => abs_nonneg _))
          (Eventually.of_forall (fun t ht =>
            ⟨le_trans hθI.1 ht.1,
              le_trans (le_trans ht.2 hx0mem.2) (by linarith [Real.pi_pos])⟩)))
    have htri : |deriv u θ| ≤ |deriv u x0| + |deriv u θ - deriv u x0| := by
      have h := abs_add_le (deriv u x0) (deriv u θ - deriv u x0)
      have he : deriv u x0 + (deriv u θ - deriv u x0) = deriv u θ := by ring
      rwa [he] at h
    have hnum1 : Real.sqrt (8 / Real.pi) ≤ 2 := by
      have h4 : (8 : ℝ) / Real.pi ≤ 4 := by
        rw [div_le_iff₀ Real.pi_pos]; linarith [Real.pi_gt_three]
      have h5 := Real.sqrt_le_sqrt h4
      have h6 : Real.sqrt (4 : ℝ) = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rwa [h6] at h5
    have hnum2 : Real.sqrt (Real.pi / 2) ≤ 2 := by
      have h4 : Real.pi / 2 ≤ 4 := by linarith [Real.pi_lt_four]
      have h5 := Real.sqrt_le_sqrt h4
      have h6 : Real.sqrt (4 : ℝ) = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rwa [h6] at h5
    calc |deriv u θ| ≤ |deriv u x0| + |deriv u θ - deriv u x0| := htri
      _ ≤ Real.sqrt (8 / Real.pi) * Real.sqrt B + Real.sqrt (Real.pi / 2) * Real.sqrt A :=
          add_le_add hx0bd (le_trans hstep hL1le)
      _ ≤ 2 * (Real.sqrt A + Real.sqrt B) := by
          have hA0 : (0 : ℝ) ≤ Real.sqrt A := Real.sqrt_nonneg _
          have hB0 : (0 : ℝ) ≤ Real.sqrt B := Real.sqrt_nonneg _
          have h1' := mul_le_mul_of_nonneg_right hnum1 hB0
          have h2' := mul_le_mul_of_nonneg_right hnum2 hA0
          linarith
  -- the estimate on the closed interval
  have hK0 : (0 : ℝ) ≤ 2 * (Real.sqrt A + Real.sqrt B) := by
    have hA0 : (0 : ℝ) ≤ Real.sqrt A := Real.sqrt_nonneg _
    have hB0 : (0 : ℝ) ≤ Real.sqrt B := Real.sqrt_nonneg _
    linarith
  have hderiv_bd : ∀ x ∈ Work.Spaces.Iθ, |deriv u x| ≤ 2 * (Real.sqrt A + Real.sqrt B) :=
    deriv_endpoint_bound hpi2 hK0 hcont hdiff hmain
  -- the estimate for `u` itself
  have hu_Ioo : ∀ x ∈ Set.Ioo 0 (Real.pi / 2),
      |u x| ≤ (Real.pi / 2 - x) * (2 * (Real.sqrt A + Real.sqrt B)) := by
    intro x hx
    obtain ⟨c, hc, hcs⟩ := exists_deriv_eq_slope u hx.2
      (hcont.mono (fun t ht => ⟨le_trans hx.1.le ht.1, ht.2⟩))
      (hdiff.mono (fun t ht => ⟨lt_trans hx.1 ht.1, ht.2⟩))
    have hpos : 0 < Real.pi / 2 - x := by linarith [hx.2]
    have hcbd : |deriv u c| ≤ 2 * (Real.sqrt A + Real.sqrt B) :=
      hderiv_bd c ⟨le_trans hx.1.le hc.1.le, hc.2.le⟩
    have hid : deriv u c = -(u x) / (Real.pi / 2 - x) := by
      rw [hcs, hu_pi]; ring
    rw [hid, abs_div, abs_neg, abs_of_pos hpos] at hcbd
    rw [div_le_iff₀ hpos] at hcbd
    calc |u x| ≤ 2 * (Real.sqrt A + Real.sqrt B) * (Real.pi / 2 - x) := hcbd
      _ = (Real.pi / 2 - x) * (2 * (Real.sqrt A + Real.sqrt B)) := by ring
  have hu_bd : ∀ x ∈ Work.Spaces.Iθ,
      |u x| ≤ (Real.pi / 2 - x) * (2 * (Real.sqrt A + Real.sqrt B)) :=
    le_on_Icc_of_le_on_Ioo hpi2 hcont.abs
      (((continuous_const.sub continuous_id).mul continuous_const).continuousOn) hu_Ioo
  constructor
  · simpa only [hAdef, hBdef] using hderiv_bd
  · simpa only [hAdef, hBdef, mul_assoc] using hu_bd

end

end Work.FTS.EllipticEst.remov
