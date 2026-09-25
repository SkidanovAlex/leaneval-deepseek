import Mathlib
import Submission.Work.Beltrami.Cauchy
import Submission.Work.Beltrami.integral_inv_mul_dW_eq_ball_sub_div_sq
import Submission.Work.Beltrami.dW_cauchyT_fderiv
import Submission.Work.Beltrami.hasFDerivAt_cauchyInt_smooth
import Submission.Work.Beltrami.dW_kernel
import Submission.Work.Beltrami.integral_radial_weight_inv_sq_eq_zero
import Submission.Work.Beltrami.cauchyInt_fderiv_apply

noncomputable section

namespace Work.Beltrami

open MeasureTheory Filter
open scoped ContDiff Topology

/-! ## `C¹` versions of the differentiation lemmas for the Cauchy integral

`Work.Beltrami.dW_cauchyT_fderiv` and the lemmas it rests on are stated for `ContDiff ℝ ⊤ f`,
where `⊤ : ℕ∞ω` denotes *analytic* (`ω`) regularity, not smoothness (`∞`).  Their proofs only
use `C¹` regularity, so we record the `C¹` versions here; this is what lets the final theorem be
applied to a merely smooth (and compactly supported) `f`. -/

/-- The continuous-linear-map valued integrand of the derivative of the Cauchy integral,
`u ↦ u⁻¹ • fderiv ℝ f (z + u)`, is Bochner integrable for `C¹` compactly supported `f`. -/
lemma integrable_smul_fderiv_cauchyInt_c1 (f : ℂ → ℂ) (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (z : ℂ) :
    Integrable (fun u : ℂ => (u⁻¹ : ℂ) • fderiv ℝ f (z + u)) volume := by
  have hfdc : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  -- a radius outside which `f` vanishes
  obtain ⟨R0, _hR0pos, hR0⟩ := hc.exists_pos_le_norm
  -- a global bound for `‖fderiv ℝ f‖`
  obtain ⟨M, hM⟩ := Continuous.bounded_above_of_compact_support hfdc (hc.fderiv (𝕜 := ℝ))
  let M' : ℝ := max M 0
  have hM'pos : 0 ≤ M' := le_max_right _ _
  have hM'bound : ∀ w, ‖fderiv ℝ f w‖ ≤ M' := fun w => le_trans (hM w) (le_max_left _ _)
  -- the cutoff radius for the dominating function
  let r : ℝ := R0 + ‖z‖ + 2
  have hr : r = R0 + ‖z‖ + 2 := rfl
  -- `f` vanishes away from the ball of radius `R0`
  have hsup : tsupport f ⊆ Metric.closedBall 0 R0 := by
    refine closure_minimal ?_ Metric.isClosed_closedBall
    intro v hv
    rw [Function.mem_support] at hv
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra h
    exact hv (hR0 v (le_of_lt (not_le.mp h)))
  have hfin : (1 : ℝ) < (Module.finrank ℝ ℂ : ℝ) := by
    rw [Complex.finrank_real_complex]; norm_num
  have hfin1 : (1 : ℕ) ≤ Module.finrank ℝ ℂ := by
    rw [Complex.finrank_real_complex]; norm_num
  -- the dominating function `‖a‖⁻¹`, cut off at the ball of radius `r`
  let bound : ℂ → ℝ := Set.indicator (Metric.ball 0 r) (fun a => M' * ‖a‖⁻¹)
  have hbound : bound = Set.indicator (Metric.ball 0 r) (fun a => M' * ‖a‖⁻¹) := rfl
  have hbound_int : Integrable bound volume := by
    rw [hbound, integrable_indicator_iff measurableSet_ball]
    refine MeasureTheory.integrableOn_ball_of_norm_le_rpow (E := ℂ) (F := ℝ) (μ := volume)
      (C := M') (α := 1) (r := r) hfin1 hfin ?_ ?_
    · filter_upwards with a
      have hnn : 0 ≤ M' * ‖a‖⁻¹ := mul_nonneg hM'pos (inv_nonneg.mpr (norm_nonneg a))
      have he : ‖(M' * ‖a‖⁻¹ : ℝ)‖ = M' * ‖a‖ ^ (-1 : ℝ) := by
        rw [Real.norm_eq_abs, abs_of_nonneg hnn, Real.rpow_neg_one]
      exact he.le
    · apply AEMeasurable.aestronglyMeasurable
      fun_prop
  refine Integrable.mono' hbound_int ?_ ?_
  · -- strong measurability
    have h1 : Measurable (fun u : ℂ => (u⁻¹ : ℂ)) := measurable_inv
    have h2 : Measurable (fun u : ℂ => fderiv ℝ f (z + u)) :=
      hfdc.measurable.comp (by fun_prop)
    exact (h1.smul h2).aestronglyMeasurable
  · -- pointwise domination
    refine Filter.Eventually.of_forall (fun a => ?_)
    by_cases ha : a ∈ Metric.ball 0 r
    · rw [hbound, Set.indicator_of_mem ha]
      calc ‖(a⁻¹ : ℂ) • fderiv ℝ f (z + a)‖
          ≤ ‖(a⁻¹ : ℂ)‖ * ‖fderiv ℝ f (z + a)‖ := norm_smul_le _ _
        _ = ‖a‖⁻¹ * ‖fderiv ℝ f (z + a)‖ := by rw [norm_inv]
        _ ≤ ‖a‖⁻¹ * M' :=
            mul_le_mul_of_nonneg_left (hM'bound (z + a)) (inv_nonneg.mpr (norm_nonneg a))
        _ = M' * ‖a‖⁻¹ := by ring
    · rw [hbound, Set.indicator_of_notMem ha]
      have h1 : r ≤ ‖a‖ := by
        rw [Metric.mem_ball, dist_zero_right] at ha
        exact not_lt.mp ha
      have htsup : z + a ∉ tsupport f := by
        intro hmem
        have hc' := hsup hmem
        rw [Metric.mem_closedBall, dist_zero_right] at hc'
        rw [hr] at h1
        have hza : ‖a‖ ≤ ‖z + a‖ + ‖z‖ := by
          have h := norm_sub_le (z + a) z
          rw [add_sub_cancel_left] at h
          exact h
        linarith
      rw [fderiv_of_notMem_tsupport ℝ htsup, smul_zero, norm_zero]

/-- Scalar form of the differentiation under the integral sign for the Cauchy integral,
`C¹` version. -/
theorem cauchyInt_fderiv_apply_c1 (f : ℂ → ℂ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (z v : ℂ) :
    fderiv ℝ (cauchyInt f) z v = ∫ u, u⁻¹ * (fderiv ℝ f (z + u) v) ∂volume := by
  rw [(hasFDerivAt_cauchyInt_smooth f hf hc z).fderiv]
  rw [ContinuousLinearMap.integral_apply (integrable_smul_fderiv_cauchyInt_c1 f hf hc z) v]
  apply integral_congr_ae
  filter_upwards with u
  rw [smul_apply, smul_eq_mul]

/-- The `∂`-derivative of the Cauchy transform, `C¹` version:
`dW (cauchyT f) z = -(1/π) • ∫ u, u⁻¹ * dW f (z + u)`. -/
theorem dW_cauchyT_fderiv_c1 (f : ℂ → ℂ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (z : ℂ) :
    dW (cauchyT f) z = (-(Real.pi)⁻¹) • ∫ u, u⁻¹ * dW f (z + u) ∂volume := by
  set c : ℂ := ((-(Real.pi : ℝ)⁻¹ : ℝ) : ℂ) with hc_def
  -- the integral form of the derivative of the Cauchy integral
  have hInt := integrable_smul_fderiv_cauchyInt_c1 f hf hc z
  set L : ℂ →L[ℝ] ℂ := ∫ u, (u⁻¹ : ℂ) • fderiv ℝ f (z + u) ∂volume with hL_def
  have hL : HasFDerivAt (cauchyInt f) L z := by
    rw [hL_def]; exact hasFDerivAt_cauchyInt_smooth f hf hc z
  have hfL : fderiv ℝ (cauchyInt f) z = L := hL.fderiv
  have hL1 : L 1 = ∫ u, u⁻¹ * (fderiv ℝ f (z + u) 1) ∂volume := by
    rw [hL_def, ContinuousLinearMap.integral_apply hInt 1]
    apply integral_congr_ae; filter_upwards with u; simp [smul_eq_mul]
  have hLI : L Complex.I = ∫ u, u⁻¹ * (fderiv ℝ f (z + u) Complex.I) ∂volume := by
    rw [hL_def, ContinuousLinearMap.integral_apply hInt Complex.I]
    apply integral_congr_ae; filter_upwards with u; simp [smul_eq_mul]
  -- integrability of the two scalar integrands
  have hg1 : Integrable (fun u => u⁻¹ * (fderiv ℝ f (z + u) 1)) volume := by
    have hcont : Continuous (fun u : ℂ => (fderiv ℝ f (z + u)) 1) :=
      ((hf.continuous_fderiv (by simp)).comp (continuous_const.add continuous_id)).clm_apply
        continuous_const
    have hcs : HasCompactSupport (fun u : ℂ => (fderiv ℝ f (z + u)) 1) :=
      ((hc.fderiv ℝ).comp_homeomorph (Homeomorph.addLeft z)).comp_left
        (g := fun L : ℂ →L[ℝ] ℂ => L 1) (by simp)
    exact (integrable_mul_inv (fun u : ℂ => (fderiv ℝ f (z + u)) 1) hcont hcs).congr
      (Filter.Eventually.of_forall (fun u => by ring))
  have hgI : Integrable (fun u => u⁻¹ * (fderiv ℝ f (z + u) Complex.I)) volume := by
    have hcont : Continuous (fun u : ℂ => (fderiv ℝ f (z + u)) Complex.I) :=
      ((hf.continuous_fderiv (by simp)).comp (continuous_const.add continuous_id)).clm_apply
        continuous_const
    have hcs : HasCompactSupport (fun u : ℂ => (fderiv ℝ f (z + u)) Complex.I) :=
      ((hc.fderiv ℝ).comp_homeomorph (Homeomorph.addLeft z)).comp_left
        (g := fun L : ℂ →L[ℝ] ℂ => L Complex.I) (by simp)
    exact (integrable_mul_inv (fun u : ℂ => (fderiv ℝ f (z + u)) Complex.I) hcont hcs).congr
      (Filter.Eventually.of_forall (fun u => by ring))
  -- rewrite the scalar integrand of `dW f` in coordinates
  have hdWf : (fun u : ℂ => u⁻¹ * dW f (z + u))
      = fun u => (2:ℂ)⁻¹ * (u⁻¹ * (fderiv ℝ f (z + u) 1)
          - Complex.I * (u⁻¹ * (fderiv ℝ f (z + u) Complex.I))) := by
    funext u; rw [dW, dzCoeff]; ring
  have h2 : (∫ u, u⁻¹ * dW f (z + u) ∂volume)
      = (2:ℂ)⁻¹ * ((∫ u, u⁻¹ * (fderiv ℝ f (z + u) 1))
          - Complex.I * (∫ u, u⁻¹ * (fderiv ℝ f (z + u) Complex.I))) := by
    rw [hdWf, integral_const_mul, integral_sub hg1 (hgI.const_mul Complex.I), integral_const_mul]
  -- the derivative of the Cauchy integral has the stated `∂`-coefficient
  have hdW_int : dW (cauchyInt f) z = ∫ u, u⁻¹ * dW f (z + u) ∂volume := by
    have h1 : dW (cauchyInt f) z = (L 1 - Complex.I * L Complex.I) / 2 := by
      unfold dW dzCoeff; rw [hfL]
    rw [h1, hL1, hLI, h2]
    ring
  -- `cauchyT` is a real multiple of `cauchyInt`, so its `∂`-derivative scales
  have hcT : cauchyT f = fun y => c * cauchyInt f y := by
    funext y; rw [hc_def]; exact cauchyT_eq_cauchyInt f y
  have hderiv : fderiv ℝ (cauchyT f) z = c • L := by
    rw [hcT]; exact (hL.const_mul c).fderiv
  have hdz : dW (cauchyT f) z = c * ∫ u, u⁻¹ * dW f (z + u) ∂volume := by
    rw [dW, hderiv, dzCoeff_smul]
    have : dzCoeff L = ∫ u, u⁻¹ * dW f (z + u) ∂volume := by
      rw [← hfL]; exact hdW_int
    rw [this]
  rw [hdz, hc_def, Complex.real_smul]

/-! ## Translation invariance of `∂` and of the Beurling transform -/

/-- The `∂`-derivative commutes with translation of the argument:
`∂(u ↦ f (z + u)) u = ∂f (z + u)`. -/
theorem dW_comp_add (f : ℂ → ℂ) (hf : Differentiable ℝ f) (z u : ℂ) :
    dW (fun y : ℂ => f (z + y)) u = dW f (z + u) := by
  unfold dW dzCoeff
  have hd : HasFDerivAt f (fderiv ℝ f (z + u)) (z + u) := (hf (z + u)).hasFDerivAt
  have h1 : HasFDerivAt (fun y : ℂ => z + y) (ContinuousLinearMap.id ℝ ℂ) u :=
    (hasFDerivAt_id u).const_add z
  have h2 : HasFDerivAt (fun y : ℂ => f (z + y)) (fderiv ℝ f (z + u)) u := by
    have h := hd.comp u h1
    rw [ContinuousLinearMap.comp_id] at h
    exact h
  rw [h2.fderiv]

/-- The Beurling transform, written as a convolution: the substitution `ζ = z + u`
(translation invariance of Lebesgue measure) turns `beurling f z` into an integral over `u`. -/
theorem beurling_eq_integral (f : ℂ → ℂ) (z : ℂ) :
    beurling f z
      = (-(Real.pi)⁻¹) • ∫ u, (f (z + u) - (bumpC u : ℂ) * f z) * (u^2)⁻¹ ∂volume := by
  have hgoal : (∫ ζ, (f ζ - (bumpC (ζ - z) : ℂ) * f z) * ((ζ - z) ^ 2)⁻¹)
      = ∫ w, (f (z + w) - (bumpC w : ℂ) * f z) * (w ^ 2)⁻¹ := by
    rw [← MeasureTheory.integral_sub_right_eq_self
      (fun w : ℂ => (f (z + w) - (bumpC w : ℂ) * f z) * (w ^ 2)⁻¹) (μ := volume) (g := z)]
    apply integral_congr_ae
    filter_upwards with ζ
    rw [show z + (ζ - z) = ζ by ring]
  rw [beurling_apply, hgoal]

/-! ## The radial weight `1 - bumpC` -/

/-- The radial weight whose value at `‖w‖` is `1 - bumpC w`. -/
def oneSubBump (t : ℝ) : ℝ := 1 - Real.smoothTransition (2 - 2 * t)

theorem bumpC_eq_oneSubBump (w : ℂ) : 1 - (bumpC w : ℂ) = ((oneSubBump ‖w‖ : ℝ) : ℂ) := by
  simp [oneSubBump, bumpC]

/-- `w ↦ (1 - bumpC w) * w⁻²` is integrable on any ball: near the origin it vanishes
(`bumpC = 1` on the disc of radius `1/2`), and on the rest of the ball it is bounded by a
constant times `‖w‖⁻¹`. -/
lemma integrableOn_one_sub_bumpC_mul_inv_sq (R : ℝ) :
    IntegrableOn (fun w : ℂ => (1 - (bumpC w : ℂ)) * (w ^ 2)⁻¹) (Metric.ball 0 R) volume := by
  refine MeasureTheory.integrableOn_ball_of_norm_le_rpow (E := ℂ) (F := ℂ) (μ := volume)
    (f := fun w : ℂ => (1 - (bumpC w : ℂ)) * (w ^ 2)⁻¹) (C := 2) (α := 1) (r := R)
    ?_ ?_ ?_ ?_
  · rw [Complex.finrank_real_complex]; norm_num
  · rw [Complex.finrank_real_complex]; norm_num
  · filter_upwards with x
    have hnorm : ‖(1 - (bumpC x : ℂ))‖ ≤ 1 := by
      rw [show (1 - (bumpC x : ℂ)) = ((1 - bumpC x : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_le_one]
      nlinarith [bumpC_le_one x, bumpC_nonneg x]
    rcases lt_or_ge ‖x‖ (1 / 2) with hx | hx
    · have h1 : (1 - (bumpC x : ℂ)) = 0 := by
        rw [bumpC_eq_one hx.le]; norm_num
      rw [h1, zero_mul, norm_zero, Real.rpow_neg_one]
      positivity
    · have hmem : ‖x‖⁻¹ ≤ 2 := by
        have h2 : ‖x‖⁻¹ ≤ (1 / 2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hx
        simpa using h2
      calc ‖(1 - (bumpC x : ℂ)) * (x ^ 2)⁻¹‖ ≤ 1 * ‖(x ^ 2)⁻¹‖ := by
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
        _ = (‖x‖ ^ 2)⁻¹ := by rw [one_mul, norm_inv, norm_pow]
        _ = ‖x‖⁻¹ * ‖x‖⁻¹ := by rw [← inv_pow, pow_two]
        _ ≤ 2 * ‖x‖⁻¹ := mul_le_mul_of_nonneg_right hmem (inv_nonneg.mpr (norm_nonneg x))
        _ = 2 * ‖x‖ ^ (-1 : ℝ) := by rw [Real.rpow_neg_one]
  · apply AEMeasurable.aestronglyMeasurable
    have h1 : Measurable (fun w : ℂ => 1 - (bumpC w : ℂ)) :=
      Measurable.const_sub (Complex.continuous_ofReal.measurable.comp
        bumpC_contDiff.continuous.measurable) 1
    have h2 : Measurable (fun w : ℂ => (w ^ 2)⁻¹) := by measurability
    exact (h1.mul h2).aemeasurable

/-- **The regularising term vanishes.**  `∫ w in ball 0 R, (1 - bumpC w) * w⁻² = 0`:
the integrand is radial and the quarter turn `w ↦ i w` preserves both the ball and Lebesgue
measure while reversing the sign of `w⁻²`. -/
theorem integral_one_sub_bumpC_mul_inv_sq_eq_zero (R : ℝ) :
    ∫ w in Metric.ball 0 R, (1 - (bumpC w : ℂ)) * (w ^ 2)⁻¹ = 0 := by
  have hint : IntegrableOn (fun w : ℂ => ((oneSubBump ‖w‖ : ℝ) : ℂ) * (w ^ 2)⁻¹)
      (Metric.ball 0 R) volume := by
    simpa only [bumpC_eq_oneSubBump] using integrableOn_one_sub_bumpC_mul_inv_sq R
  have hmain := integral_radial_weight_inv_sq_eq_zero oneSubBump (S := Metric.ball 0 R)
    (fun c w => by
      rw [Metric.mem_ball, Metric.mem_ball, dist_zero_right, dist_zero_right, norm_mul,
        Circle.norm_coe, one_mul])
    hint
  simpa only [bumpC_eq_oneSubBump] using hmain

/-- For a `C¹` function with compact support, `u ↦ (H u - H 0) * u⁻²` is integrable on any
ball: `H u - H 0 = O(‖u‖)`, so the integrand is `O(‖u‖⁻¹)`, which is integrable in dimension
two. -/
lemma integrableOn_sub_const_mul_inv_sq {H : ℂ → ℂ} (hH : ContDiff ℝ 1 H)
    (hc : HasCompactSupport H) (R : ℝ) :
    IntegrableOn (fun u : ℂ => (H u - H 0) * (u ^ 2)⁻¹) (Metric.ball 0 R) volume := by
  obtain ⟨C, hC⟩ := Continuous.bounded_above_of_compact_support
    (hH.continuous_fderiv (by simp)) (hc.fderiv ℝ)
  have hlip : ∀ u : ℂ, ‖H u - H 0‖ ≤ C * ‖u‖ := by
    intro u
    have h := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := H) (s := Set.univ)
      (C := C) (fun x _ => (hH.differentiable (by simp)) x) (fun x _ => hC x) convex_univ
      (Set.mem_univ (0 : ℂ)) (Set.mem_univ u)
    simpa using h
  refine MeasureTheory.integrableOn_ball_of_norm_le_rpow (E := ℂ) (F := ℂ) (μ := volume)
    (f := fun u : ℂ => (H u - H 0) * (u ^ 2)⁻¹) (C := C) (α := 1) (r := R) ?_ ?_ ?_ ?_
  · rw [Complex.finrank_real_complex]; norm_num
  · rw [Complex.finrank_real_complex]; norm_num
  · filter_upwards with x
    rcases eq_or_ne x 0 with hx | hx
    · subst hx
      rw [sub_self, zero_mul, norm_zero, Real.rpow_neg_one]
      simp
    · rw [norm_mul, norm_inv, norm_pow, Real.rpow_neg_one]
      calc ‖H x - H 0‖ * (‖x‖ ^ 2)⁻¹ ≤ (C * ‖x‖) * (‖x‖ ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_right (hlip x) (inv_nonneg.mpr (sq_nonneg _))
        _ = C * ‖x‖⁻¹ := by
            have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
            rw [mul_assoc, ← inv_pow, pow_two, ← mul_assoc (a := ‖x‖), mul_inv_cancel₀ hr, one_mul]
  · apply AEMeasurable.aestronglyMeasurable
    have h1 : Measurable (fun u : ℂ => H u - H 0) :=
      hH.continuous.measurable.sub_const (H 0)
    have h2 : Measurable (fun u : ℂ => (u ^ 2)⁻¹) := by measurability
    exact (h1.mul h2).aemeasurable

/-! ## The main identity -/

/-- `dW (cauchyT f) z = beurling f z` for smooth compactly supported `f` (the field
`beurlingDeriv` of `Work.Beltrami.CauchyEstimates`).

Now TRUE: `bumpC` in `Submission/Work/Beltrami/Cauchy.lean` is defined explicitly and radially as
`bumpC w = Real.smoothTransition (2 - 2 * ‖w‖)`, with `bumpC_rotI : bumpC (I * w) = bumpC w`,
`bumpC_contDiffC`, `bumpC_hasCompactSupport`, `bumpC_eq_one`, `bumpC_eq_zero`.

Ingredients available (all sorry-free): `Work.Beltrami.dW_cauchyT_fderiv` gives
`dW (cauchyT f) z = -(1/π) • ∫ u, u⁻¹ * dW f (z+u)` but stated for `ContDiff ℝ ⊤ f` where
`⊤ : ℕ∞ω` is `ω` (analytic), not `∞`; a copy of its proof with the hypothesis weakened to
`ContDiff ℝ 1 f` is needed (all its steps - `hasFDerivAt_cauchyInt_c1`/`_smooth`,
`integrable_smul_fderiv_cauchyInt` with the same weakening, `cauchyT_eq_cauchyInt`,
`ContinuousLinearMap.integral_apply` - are available in `C¹` form).
`Work.Beltrami.integral_inv_mul_dW_eq_ball_sub_div_sq` (already `C¹`): for `H` of class `C¹`
vanishing off `ball 0 R`, `∫ u, u⁻¹ * dW H u = ∫ u in ball 0 R, (H u - H 0) * (u^2)⁻¹`.
`beurling_apply` plus `integral_add_right_eq_self` writes
`beurling f z = -(1/π) • ∫ u, (f (z+u) - (bumpC u : ℂ) * f z) * (u^2)⁻¹`.
The regularising term vanishes:
`∫ u in ball 0 R, (1 - (bumpC u : ℂ)) * (u^2)⁻¹ = 0`, by the quarter-turn substitution
`u ↦ I * u` (measure preserving, `bumpC_rotI`, `(I*u)^2 = -(u^2)`).
Also `dW (fun u => f (z + u)) u = dW f (z + u)` (chain rule, cf. `fderiv_comp_add_left`).

Suggested shape: for fixed `z` set `H u := f (z + u)`; take `R' ≥ max R 1` with
`∀ u, R' ≤ ‖u‖ → H u = 0` (`‖u‖ ≥ R + ‖z‖ + 1` suffices); apply
`integral_inv_mul_dW_eq_ball_sub_div_sq` to `H`, `R'`; replace `H u - H 0` by
`H u - (bumpC u : ℂ) * H 0` via the vanishing regularising integral; identify with
`beurling f z`. -/
theorem dW_cauchyT_eq_beurling_radial (f : ℂ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) : ∀ z : ℂ, dW (cauchyT f) z = beurling f z := by
  intro z
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by simp)
  obtain ⟨R0, hR0pos, hR0⟩ := hc.exists_pos_le_norm
  set R' : ℝ := R0 + ‖z‖ + 1 with hR'def
  have hR'pos : 0 < R' := by rw [hR'def]; positivity
  have hR'one : 1 ≤ R' := by rw [hR'def]; nlinarith [norm_nonneg z]
  set H : ℂ → ℂ := fun u => f (z + u) with hHdef
  have hHc1 : ContDiff ℝ 1 H := hf1.comp (contDiff_const.add contDiff_id)
  have hHc : HasCompactSupport H := hc.comp_homeomorph (Homeomorph.addLeft z)
  have hHsupp : ∀ u : ℂ, R' ≤ ‖u‖ → H u = 0 := by
    intro u hu
    have h1 : R0 ≤ ‖z + u‖ := by
      have h := norm_sub_le (z + u) z
      rw [add_sub_cancel_left] at h
      rw [hR'def] at hu
      linarith
    show f (z + u) = 0
    exact hR0 (z + u) h1
  have hH0 : H 0 = f z := by show f (z + 0) = f z; rw [add_zero]
  -- step 1: differentiate the Cauchy transform (`C¹` version)
  have h1 : dW (cauchyT f) z = (-(Real.pi)⁻¹) • ∫ u, u⁻¹ * dW f (z + u) ∂volume :=
    dW_cauchyT_fderiv_c1 f hf1 hc z
  -- step 2: recognise `dW f (z + u)` as `dW H u`
  have h2 : (∫ u, u⁻¹ * dW f (z + u) ∂volume) = ∫ u, u⁻¹ * dW H u ∂volume := by
    apply integral_congr_ae
    filter_upwards with u
    show u⁻¹ * dW f (z + u) = u⁻¹ * dW H u
    rw [hHdef]
    rw [dW_comp_add f (hf1.differentiable (by simp)) z u]
  -- step 3: the principal-value formula for the `∂`-derivative of `H`
  have h3 : (∫ u, u⁻¹ * dW H u ∂volume)
      = ∫ u in Metric.ball 0 R', (H u - H 0) * (u ^ 2)⁻¹ ∂volume :=
    integral_inv_mul_dW_eq_ball_sub_div_sq hR'pos hHc1 hHsupp
  -- step 4: replace `H 0` by `bumpC u * H 0`
  have h4 : (∫ u in Metric.ball 0 R', (H u - H 0) * (u ^ 2)⁻¹ ∂volume)
      = ∫ u in Metric.ball 0 R', (H u - (bumpC u : ℂ) * H 0) * (u ^ 2)⁻¹ ∂volume := by
    have hI1 : IntegrableOn (fun u : ℂ => (H u - H 0) * (u ^ 2)⁻¹) (Metric.ball 0 R') volume :=
      integrableOn_sub_const_mul_inv_sq hHc1 hHc R'
    have hI2 : IntegrableOn (fun u : ℂ => (1 - (bumpC u : ℂ)) * H 0 * (u ^ 2)⁻¹)
        (Metric.ball 0 R') volume :=
      ((integrableOn_one_sub_bumpC_mul_inv_sq R').const_mul (H 0)).congr
        (Filter.Eventually.of_forall (fun u => by ring))
    have hI2' : IntegrableOn (fun u : ℂ => ((bumpC u : ℂ) - 1) * H 0 * (u ^ 2)⁻¹)
        (Metric.ball 0 R') volume := by
      refine (hI2.neg).congr ?_
      filter_upwards with u
      rw [Pi.neg_apply]
      ring
    have hI3 : IntegrableOn (fun u : ℂ => (H u - (bumpC u : ℂ) * H 0) * (u ^ 2)⁻¹)
        (Metric.ball 0 R') volume := by
      refine (hI1.add hI2).congr ?_
      filter_upwards with u
      rw [Pi.add_apply]
      ring
    have hdec : ∀ u : ℂ, (H u - H 0) * (u ^ 2)⁻¹
        = (H u - (bumpC u : ℂ) * H 0) * (u ^ 2)⁻¹
          + ((bumpC u : ℂ) - 1) * H 0 * (u ^ 2)⁻¹ := fun u => by ring
    have hzero : ∫ u in Metric.ball 0 R', ((bumpC u : ℂ) - 1) * H 0 * (u ^ 2)⁻¹ = 0 := by
      have hv := integral_one_sub_bumpC_mul_inv_sq_eq_zero R'
      have hc1 : (∫ u in Metric.ball 0 R', ((bumpC u : ℂ) - 1) * H 0 * (u ^ 2)⁻¹)
          = ∫ u in Metric.ball 0 R', (-H 0) * ((1 - (bumpC u : ℂ)) * (u ^ 2)⁻¹) :=
        MeasureTheory.setIntegral_congr_fun measurableSet_ball (fun u _ => by ring)
      rw [hc1, MeasureTheory.integral_const_mul, hv, mul_zero]
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_ball (fun u _ => hdec u),
      MeasureTheory.integral_add hI3 hI2', hzero, add_zero]
  -- step 5: the integrand is compactly supported, so the ball integral is the integral over `ℂ`
  have h5 : (∫ u in Metric.ball 0 R', (H u - (bumpC u : ℂ) * H 0) * (u ^ 2)⁻¹ ∂volume)
      = ∫ u, (H u - (bumpC u : ℂ) * H 0) * (u ^ 2)⁻¹ ∂volume := by
    rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro u hu
    rw [Metric.mem_ball, not_lt, dist_zero_right] at hu
    rw [hHsupp u hu, bumpC_eq_zero (le_trans hR'one hu)]
    simp
  -- step 6: identify the result with the Beurling transform
  have h6 : (-(Real.pi)⁻¹) • (∫ u, (H u - (bumpC u : ℂ) * H 0) * (u ^ 2)⁻¹ ∂volume)
      = beurling f z := by
    rw [beurling_eq_integral]
    congr 1
    apply integral_congr_ae
    filter_upwards with u
    show (H u - (bumpC u : ℂ) * H 0) * (u ^ 2)⁻¹
      = (f (z + u) - (bumpC u : ℂ) * f z) * (u ^ 2)⁻¹
    rw [hH0, hHdef]
  calc dW (cauchyT f) z = (-(Real.pi)⁻¹) • ∫ u, u⁻¹ * dW f (z + u) ∂volume := h1
    _ = (-(Real.pi)⁻¹) • ∫ u, u⁻¹ * dW H u ∂volume := by rw [h2]
    _ = (-(Real.pi)⁻¹) • ∫ u in Metric.ball 0 R', (H u - H 0) * (u ^ 2)⁻¹ ∂volume := by rw [h3]
    _ = (-(Real.pi)⁻¹) • ∫ u in Metric.ball 0 R', (H u - (bumpC u : ℂ) * H 0) * (u ^ 2)⁻¹
          ∂volume := by rw [h4]
    _ = (-(Real.pi)⁻¹) • ∫ u, (H u - (bumpC u : ℂ) * H 0) * (u ^ 2)⁻¹ ∂volume := by rw [h5]
    _ = beurling f z := h6

end Work.Beltrami
