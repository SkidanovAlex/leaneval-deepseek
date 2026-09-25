import Mathlib
import Submission.Work.Beltrami.dW_kernel
import Submission.Work.Beltrami.tendsto_cutK_mul
import Submission.Work.Beltrami.tendsto_cutProfile_deriv
import Submission.Work.Beltrami.integrable_mul_cutK
import Submission.Work.Beltrami.contDiff_cutK_smooth

noncomputable section

open MeasureTheory Filter Bornology
open scoped Topology ContDiff

namespace Work.Beltrami

/-! ## The `∂`-derivative of the cutoff kernel against a compactly supported `C¹` function -/

/-- `dW H` is continuous when `H` is `C¹`. -/
lemma continuous_dW {H : ℂ → ℂ} (hH : ContDiff ℝ 1 H) : Continuous (dW H) := by
  have hd : Continuous (fderiv ℝ H) := hH.continuous_fderiv (by simp)
  have h1 : Continuous (fun u : ℂ => (fderiv ℝ H u) 1) := hd.clm_apply continuous_const
  have hI : Continuous (fun u : ℂ => (fderiv ℝ H u) Complex.I) := hd.clm_apply continuous_const
  unfold dW dzCoeff
  exact (h1.sub (continuous_const.mul hI)).div_const 2

/-- `dW H` has compact support when `H` does. -/
lemma hasCompactSupport_dW {H : ℂ → ℂ} (hc : HasCompactSupport H) : HasCompactSupport (dW H) := by
  have h := (hc.fderiv ℝ).comp_left
    (g := fun L : ℂ →L[ℝ] ℂ => (L 1 - Complex.I * L Complex.I)/2) (by simp)
  unfold dW dzCoeff
  exact h

/-- **The Cauchy kernel against `∂H`.**  For a `C¹` function `H` with compact support,
`∫ u, ∂H(u) * cutK ε u → ∫ u, ∂H(u) * u⁻¹` as `ε → 0⁺`: the cutoff kernel converges to the
Cauchy kernel `u ↦ u⁻¹` pointwise (a.e.), with the integrable dominator `‖∂H u‖ * ‖u⁻¹‖`. -/
theorem tendsto_integral_dW_mul_cutK (H : ℂ → ℂ) (hH : ContDiff ℝ 1 H)
    (hc : HasCompactSupport H) :
    Filter.Tendsto (fun ε : ℝ => ∫ u, dW H u * cutK ε u ∂volume)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ u, dW H u * u⁻¹ ∂volume)) :=
  tendsto_cutK_mul (dW H) (continuous_dW hH) (hasCompactSupport_dW hc)

/-! ## Elementary facts about the kernels -/

/-- The angular factor of the Cauchy kernel is bounded by one. -/
lemma norm_star_mul_inv_le_one (u : ℂ) : ‖star u * u⁻¹‖ ≤ 1 := by
  rcases eq_or_ne u 0 with h | h
  · subst h; simp
  · rw [norm_mul, norm_star, norm_inv]
    exact le_of_eq (mul_inv_cancel₀ (norm_ne_zero_iff.mpr h))

/-- The derivative of the smooth transition vanishes to the left of zero. -/
lemma deriv_smoothTransition_eq_zero_of_lt_zero {t : ℝ} (ht : t < 0) :
    deriv Real.smoothTransition t = 0 := by
  have h : Real.smoothTransition =ᶠ[𝓝 t] (fun _ => (0:ℝ)) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    exact ⟨Set.Iio 0, IsOpen.mem_nhds isOpen_Iio ht,
      fun x hx => Real.smoothTransition.zero_of_nonpos hx.le⟩
  rw [h.deriv_eq]; simp

/-- The derivative of the cutoff profile vanishes below `ε²` (where the profile is locally zero). -/
lemma deriv_cutProfile_eq_zero_of_lt {ε s : ℝ} (hε : 0 < ε) (hs : s < ε^2) :
    deriv (cutProfile ε) s = 0 := by
  rw [deriv_cutProfile ε (ne_of_gt hε) s]
  have h2 : s / ε^2 - 1 < 0 := by
    have : s / ε^2 < 1 := (div_lt_one (pow_pos hε 2)).mpr hs
    linarith
  rw [deriv_smoothTransition_eq_zero_of_lt_zero h2, zero_div]

/-- The derivative of the cutoff profile vanishes above `2ε²` (where the profile is locally one). -/
lemma deriv_cutProfile_eq_zero_of_gt {ε s : ℝ} (hε : 0 < ε) (hs : 2*ε^2 < s) :
    deriv (cutProfile ε) s = 0 := by
  rw [deriv_cutProfile ε (ne_of_gt hε) s]
  have h2 : 1 < s / ε^2 - 1 := by
    have : 2 < s / ε^2 := (lt_div_iff₀ (pow_pos hε 2)).mpr hs
    linarith
  rw [deriv_smoothTransition_of_one_lt h2, zero_div]

/-- The radial bump `χ(u) = ψ(2 - ‖u‖²)`: smooth, `1` on the unit disc, supported in the disc
of radius `√2`. -/
def chiB (u : ℂ) : ℂ := (Real.smoothTransition (2 - ‖u‖^2) : ℂ)

lemma chiB_contDiff {n : ℕ∞} : ContDiff ℝ n chiB := by
  unfold chiB
  have h1 : ContDiff ℝ (n : WithTop ℕ∞) (fun u : ℂ => 2 - ‖u‖^2) :=
    contDiff_const.sub (contDiff_norm_sq ℝ (n := n))
  exact (Complex.ofRealCLM.contDiff).comp ((Real.smoothTransition.contDiff).comp h1)

lemma continuous_chiB : Continuous chiB := (chiB_contDiff (n := ⊤)).continuous

lemma chiB_eq_one {u : ℂ} (h : ‖u‖ ≤ 1) : chiB u = 1 := by
  have h2 : ‖u‖^2 ≤ 1 := by nlinarith [norm_nonneg u, h]
  have h1 : (1:ℝ) ≤ 2 - ‖u‖^2 := by linarith
  simp only [chiB, Real.smoothTransition.one_of_one_le h1, Complex.ofReal_one]

lemma chiB_eq_zero {u : ℂ} (h : Real.sqrt 2 ≤ ‖u‖) : chiB u = 0 := by
  have h2 : 2 ≤ ‖u‖^2 := by
    have h3 : (Real.sqrt 2)^2 ≤ ‖u‖^2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg 2) h 2
    rwa [Real.sq_sqrt (by norm_num)] at h3
  have h1 : 2 - ‖u‖^2 ≤ 0 := by linarith
  simp only [chiB, Real.smoothTransition.zero_of_nonpos h1, Complex.ofReal_zero]

lemma chiB_hasCompactSupport : HasCompactSupport chiB := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 (Real.sqrt 2)) ?_
  intro u hu
  rw [Function.mem_support] at hu
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra h
  push_neg at h
  exact hu (chiB_eq_zero h.le)

lemma chiB_zero : chiB 0 = 1 := chiB_eq_one (by simp)

/-- The weight identity used to apply the rotation-invariance lemma to the term where the
constant part of `H` meets the radial derivative of the cutoff. -/
lemma chiB_mul_deriv_cutProfile_eq (ε : ℝ) (w : ℂ) :
    (((Real.smoothTransition (2 - ‖w‖^2) * deriv (cutProfile ε) (‖w‖^2) * ‖w‖^2 : ℝ)) : ℂ)
        * (w^2)⁻¹
      = chiB w * ((deriv (cutProfile ε) (‖w‖^2) : ℝ) : ℂ) * (star w * w⁻¹) := by
  simp only [chiB]
  rw [star_mul_inv_eq_normSq_mul_inv_sq]
  push_cast
  ring

/-- The radial factor of `∂(cutK ε)` is continuous: it is a product of a continuous function
with the (discontinuous only at the origin) angular factor, which it kills near the origin. -/
lemma continuous_deriv_cutProfile_mul_star_inv (ε : ℝ) (hε : 0 < ε) :
    Continuous (fun w : ℂ => ((deriv (cutProfile ε) (‖w‖^2) : ℝ) : ℂ) * (star w * w⁻¹)) := by
  have hc0 : Continuous (fun s : ℝ => deriv (cutProfile ε) s) :=
    (cutProfile_contDiff ε 1).continuous_deriv (by simp)
  have hcont : Continuous (fun w : ℂ => ((deriv (cutProfile ε) (‖w‖^2) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (hc0.comp (continuous_norm.pow 2))
  rw [continuous_iff_continuousAt]
  intro w
  rcases eq_or_ne w 0 with hw | hw
  · subst hw
    rw [ContinuousAt]
    have hnear : (fun u : ℂ => ((deriv (cutProfile ε) (‖u‖^2) : ℝ) : ℂ) * (star u * u⁻¹))
        =ᶠ[𝓝 (0:ℂ)] (fun _ => (0:ℂ)) := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨Metric.ball (0:ℂ) ε, Metric.ball_mem_nhds 0 hε, ?_⟩
      intro u hu
      rw [Metric.mem_ball, dist_zero_right] at hu
      have h2 : ‖u‖^2 < ε^2 := by nlinarith [norm_nonneg u]
      simp [deriv_cutProfile_eq_zero_of_lt hε h2]
    rw [show ((deriv (cutProfile ε) (‖(0:ℂ)‖^2) : ℝ) : ℂ) * (star (0:ℂ) * (0:ℂ)⁻¹) = 0 by simp]
    exact (tendsto_const_nhds).congr' hnear.symm
  · have h2 : ContinuousAt (fun z : ℂ => star z * z⁻¹) w :=
      (continuous_star.continuousAt).mul (continuousAt_id.inv₀ hw)
    exact hcont.continuousAt.mul h2

/-- The radial factor of `∂(cutK ε)` has compact support (it is supported in the annulus
`ε ≤ ‖w‖ ≤ √2 ε`). -/
lemma hasCompactSupport_deriv_cutProfile (ε : ℝ) (hε : 0 < ε) :
    HasCompactSupport (fun w : ℂ => ((deriv (cutProfile ε) (‖w‖^2) : ℝ) : ℂ)) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall 0 (Real.sqrt 2 * ε)) ?_
  intro w hw
  rw [Function.mem_support] at hw
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra h
  push_neg at h
  have h2 : 2 * ε^2 < ‖w‖^2 := by
    have h3 : (Real.sqrt 2 * ε)^2 = 2 * ε^2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num)]
    have h5 : 0 ≤ Real.sqrt 2 * ε := mul_nonneg (Real.sqrt_nonneg 2) hε.le
    have h6 : (Real.sqrt 2 * ε) * (Real.sqrt 2 * ε) < ‖w‖ * ‖w‖ :=
      mul_self_lt_mul_self h5 h
    nlinarith [h3, h6]
  exact hw (by simp [deriv_cutProfile_eq_zero_of_gt hε h2])

/-- The radial derivative of the cutoff, as a continuous function on `ℂ`. -/
lemma continuous_deriv_cutProfile (ε : ℝ) :
    Continuous (fun w : ℂ => ((deriv (cutProfile ε) (‖w‖^2) : ℝ) : ℂ)) := by
  have hc0 : Continuous (fun s : ℝ => deriv (cutProfile ε) s) :=
    (cutProfile_contDiff ε 1).continuous_deriv (by simp)
  exact Complex.continuous_ofReal.comp (hc0.comp (continuous_norm.pow 2))

/-- **The radial part of `∂(cutK ε)` against `H`.**  For `H` of class `C¹` with compact support,
`∫ u, H u * (deriv (cutProfile ε) (‖u‖²) * (star u * u⁻¹)) → 0` as `ε → 0⁺`.  Writing
`H = H 0 * χ + (H - H 0 * χ)` with `χ = chiB` the radial bump:
* the first term vanishes identically for every `ε > 0` by rotational symmetry (a radial weight
  times `w⁻²` integrates to zero);
* the second term is `∫ u, F u * deriv (cutProfile ε) (‖u‖²)` with
  `F u = (H u - H 0 * χ u) * (star u * u⁻¹)`, which is continuous (it vanishes at the origin),
  compactly supported and satisfies `F 0 = 0`, so the approximate identity
  `deriv (cutProfile ε) ∘ ‖·‖²` gives the limit `π * F 0 = 0`. -/
theorem tendsto_integral_deriv_cutProfile_mul_star_inv (H : ℂ → ℂ) (hH : ContDiff ℝ 1 H)
    (hc : HasCompactSupport H) :
    Filter.Tendsto
      (fun ε : ℝ => ∫ u, H u * (((deriv (cutProfile ε) (‖u‖^2) : ℝ) : ℂ)
        * (star u * u⁻¹)) ∂volume)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  set F : ℂ → ℂ := fun u => (H u - H 0 * chiB u) * (star u * u⁻¹) with hFdef
  have hGcont : Continuous (fun u : ℂ => H u - H 0 * chiB u) :=
    hH.continuous.sub (continuous_const.mul continuous_chiB)
  have hFcont : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro x
    rcases eq_or_ne x 0 with hx | hx
    · subst hx
      have hzero : F 0 = 0 := by simp [hFdef, chiB_zero]
      rw [ContinuousAt, hzero, tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero' (f := fun u : ℂ => ‖F u‖) (g := fun u : ℂ => ‖H u - H 0‖)
        (Filter.Eventually.of_forall (fun u => norm_nonneg _)) ?_ ?_
      · filter_upwards [Metric.ball_mem_nhds (0:ℂ) one_pos] with u hu
        have hu1 : ‖u‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hu
        have h1 : chiB u = 1 := chiB_eq_one hu1.le
        have hFeq : F u = (H u - H 0) * (star u * u⁻¹) := by
          simp only [hFdef, h1, mul_one]
        rw [hFeq, norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _) (norm_star_mul_inv_le_one u)
      · have hcont : Filter.Tendsto (fun u : ℂ => H u - H 0) (𝓝 (0:ℂ)) (𝓝 (H 0 - H 0)) :=
          hH.continuous.continuousAt.sub tendsto_const_nhds
        simpa using hcont.norm
    · exact hGcont.continuousAt.mul
        ((continuous_star.continuousAt).mul (continuousAt_id.inv₀ hx))
  have hFc : HasCompactSupport F := by
    refine HasCompactSupport.of_support_subset_isCompact
      (K := tsupport H ∪ tsupport chiB) (hc.union chiB_hasCompactSupport) ?_
    intro u hu
    rw [Function.mem_support] at hu
    by_contra hcon
    rw [Set.mem_union, not_or] at hcon
    obtain ⟨h1, h2⟩ := hcon
    refine hu ?_
    have h3 : H u = 0 := by
      by_contra hh; exact h1 (subset_closure hh)
    have h4 : chiB u = 0 := by
      by_contra hh; exact h2 (subset_closure hh)
    simp [hFdef, h3, h4]
  have hF0 : F 0 = 0 := by simp [hFdef, chiB_zero]
  have hlimF : Filter.Tendsto
      (fun ε : ℝ => ∫ u, F u * ((deriv (cutProfile ε) (‖u‖^2) : ℝ) : ℂ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((Real.pi : ℂ) * F 0)) :=
    tendsto_cutProfile_deriv F hFcont hFc
  have hlimF0 : Filter.Tendsto
      (fun ε : ℝ => ∫ u, F u * ((deriv (cutProfile ε) (‖u‖^2) : ℝ) : ℂ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (0:ℂ)) := by
    rw [hF0, mul_zero] at hlimF
    exact hlimF
  have hconst : ∀ ε : ℝ, 0 < ε →
      ∫ u, (H 0 * chiB u) * (((deriv (cutProfile ε) (‖u‖^2) : ℝ) : ℂ)
        * (star u * u⁻¹)) ∂volume = 0 := by
    intro ε hε
    have hpt : ∀ u : ℂ, (H 0 * chiB u) * (((deriv (cutProfile ε) (‖u‖^2) : ℝ) : ℂ)
          * (star u * u⁻¹))
        = H 0 * (((((Real.smoothTransition (2 - ‖u‖^2) * deriv (cutProfile ε) (‖u‖^2)
            * ‖u‖^2 : ℝ)) : ℂ) * (u^2)⁻¹)) := by
      intro u
      rw [chiB_mul_deriv_cutProfile_eq]
      ring
    have hIntA : Integrable (fun w : ℂ => chiB w * (((deriv (cutProfile ε) (‖w‖^2) : ℝ) : ℂ)
        * (star w * w⁻¹))) :=
      (continuous_chiB.mul (continuous_deriv_cutProfile_mul_star_inv ε hε))
        |>.integrable_of_hasCompactSupport chiB_hasCompactSupport.mul_right
    have hInt : Integrable (fun w : ℂ =>
        ((((Real.smoothTransition (2 - ‖w‖^2) * deriv (cutProfile ε) (‖w‖^2) * ‖w‖^2 : ℝ)) : ℂ)
          * (w^2)⁻¹)) :=
      hIntA.congr (Filter.Eventually.of_forall (fun w => by
        show chiB w * (((deriv (cutProfile ε) (‖w‖^2) : ℝ) : ℂ) * (star w * w⁻¹))
          = ((((Real.smoothTransition (2 - ‖w‖^2) * deriv (cutProfile ε) (‖w‖^2)
              * ‖w‖^2 : ℝ)) : ℂ) * (w^2)⁻¹)
        rw [← mul_assoc, ← chiB_mul_deriv_cutProfile_eq ε w]))
    have hzero := integral_radial_weight_inv_sq_eq_zero
      (S := Set.univ)
      (fun r : ℝ => Real.smoothTransition (2 - r^2) * deriv (cutProfile ε) (r^2) * r^2)
      (fun c w => by simp) (by simpa using hInt)
    have hzero' : ∫ a : ℂ, ((((Real.smoothTransition (2 - ‖a‖^2) * deriv (cutProfile ε) (‖a‖^2)
        * ‖a‖^2 : ℝ)) : ℂ) * (a^2)⁻¹) ∂volume = 0 := by
      simpa using hzero
    simp only [hpt]
    rw [MeasureTheory.integral_const_mul, hzero', mul_zero]
  have hdecomp : (fun ε : ℝ => ∫ u, F u * ((deriv (cutProfile ε) (‖u‖^2) : ℝ) : ℂ))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun ε : ℝ => ∫ u, H u * (((deriv (cutProfile ε) (‖u‖^2) : ℝ) : ℂ)
        * (star u * u⁻¹))) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hDcont : Continuous (fun u : ℂ => ((deriv (cutProfile ε) (‖u‖^2) : ℝ) : ℂ)) :=
      continuous_deriv_cutProfile ε
    have hAcont : Continuous (fun u : ℂ => ((deriv (cutProfile ε) (‖u‖^2) : ℝ) : ℂ)
        * (star u * u⁻¹)) := continuous_deriv_cutProfile_mul_star_inv ε hε
    have hFint : Integrable (fun u : ℂ => F u * ((deriv (cutProfile ε) (‖u‖^2) : ℝ) : ℂ)) :=
      (hFcont.mul hDcont).integrable_of_hasCompactSupport hFc.mul_right
    have hCint : Integrable (fun u : ℂ => (H 0 * chiB u) * (((deriv (cutProfile ε) (‖u‖^2) : ℝ) : ℂ)
        * (star u * u⁻¹))) :=
      ((continuous_const.mul continuous_chiB).mul hAcont)
        |>.integrable_of_hasCompactSupport
          ((chiB_hasCompactSupport.mul_left (f := fun _ : ℂ => H 0)).mul_right)
    have hsum : (fun u : ℂ => F u * ((deriv (cutProfile ε) (‖u‖^2) : ℝ) : ℂ)
          + (H 0 * chiB u) * (((deriv (cutProfile ε) (‖u‖^2) : ℝ) : ℂ) * (star u * u⁻¹)))
        = fun u : ℂ => H u * (((deriv (cutProfile ε) (‖u‖^2) : ℝ) : ℂ) * (star u * u⁻¹)) := by
      funext u; simp only [hFdef]; ring
    rw [← hsum, integral_add hFint hCint, hconst ε hε, add_zero]
  exact hlimF0.congr' hdecomp


/-- The cutoff profile vanishes where its argument is at most `ε²`. -/
lemma cutProfile_eq_zero_of_le {ε s : ℝ} (hε : 0 < ε) (h : s ≤ ε^2) :
    cutProfile ε s = 0 := by
  rw [cutProfile]
  refine Real.smoothTransition.zero_of_nonpos ?_
  rw [sub_nonpos, div_le_one (pow_pos hε 2)]
  exact h

/-- **The shrinking term.**  For `H` of class `C¹` vanishing outside the disc of radius `R > 0`,
`∫ u, H u * (cutProfile ε (‖u‖²) : ℂ) * (u²)⁻¹ → ∫ u in Metric.ball 0 R, (H u - H 0) * (u²)⁻¹`
as `ε → 0⁺`.  The `H 0`-part vanishes inside the disc for every `ε > 0` by rotational symmetry,
and the remainder converges by dominated convergence, dominated by `C * ‖u⁻¹‖` on the disc
(`C` a bound for `fderiv ℝ H`). -/
theorem tendsto_integral_mul_cutProfile_inv_sq (H : ℂ → ℂ) {R : ℝ} (hR : 0 < R)
    (hH : ContDiff ℝ 1 H) (hsupp : ∀ u : ℂ, R ≤ ‖u‖ → H u = 0) :
    Filter.Tendsto
      (fun ε : ℝ => ∫ u, H u * (cutProfile ε (‖u‖^2) : ℂ) * (u^2)⁻¹ ∂volume)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ u in Metric.ball 0 R, (H u - H 0) * (u^2)⁻¹ ∂volume)) := by
  have hcomp : HasCompactSupport H := HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall 0 R) (fun u hu => by
      rw [Function.mem_support] at hu
      rw [Metric.mem_closedBall, dist_zero_right]
      by_contra h
      push_neg at h
      exact hu (hsupp u (le_of_lt h)))
  obtain ⟨C, hC⟩ := Continuous.bounded_above_of_compact_support
    (hH.continuous_fderiv (by simp)) (hcomp.fderiv ℝ)
  have hlip : ∀ u : ℂ, ‖H u - H 0‖ ≤ C * ‖u‖ := by
    intro u
    have h := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := H) (s := Set.univ) (C := C)
      (fun x _ => (hH.differentiable (by simp)) x) (fun x _ => hC x) convex_univ
      (Set.mem_univ (0:ℂ)) (Set.mem_univ u)
    simpa using h
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (fderiv ℝ H 0)) (hC 0)
  -- integrability of the dominator on the disc
  have hloc : LocallyIntegrable (fun u : ℂ => u⁻¹) (volume : Measure ℂ) := by
    refine MeasureTheory.locallyIntegrable_of_norm_le_rpow (E := ℂ) (F := ℂ) (C := 1) (α := 1)
      ?_ ?_ ?_ ?_
    · rw [Complex.finrank_real_complex]; norm_num
    · rw [Complex.finrank_real_complex]; norm_num
    · filter_upwards with x; rw [one_mul, norm_inv, Real.rpow_neg_one]
    · exact measurable_inv.aestronglyMeasurable
  have hdom_int : Integrable (fun u : ℂ => C * ‖u⁻¹‖) (volume.restrict (Metric.ball 0 R)) := by
    have h1 : IntegrableOn (fun u : ℂ => u⁻¹) (Metric.ball 0 R) volume :=
      (hloc.integrableOn_isCompact (isCompact_closedBall 0 R)).mono_set
        Metric.ball_subset_closedBall
    exact (h1.norm.const_mul C)
  -- the pointwise domination
  have hbound : ∀ (ε : ℝ) (u : ℂ),
      ‖(H u - H 0) * (cutProfile ε (‖u‖^2) : ℂ) * (u^2)⁻¹‖ ≤ C * ‖u⁻¹‖ := by
    intro ε u
    rcases eq_or_ne u 0 with hu | hu
    · subst hu; simp
    · have h1 := hlip u
      have h2 : ‖cutProfile ε (‖u‖^2)‖ ≤ 1 := by
        have h := norm_ofReal_cutProfile_le_one ε u
        rwa [Complex.norm_real] at h
      have h3 : (‖u‖^2)⁻¹ = ‖u⁻¹‖^2 := by rw [norm_inv, inv_pow]
      have h4 : ‖u‖ * ‖u⁻¹‖ = 1 := by
        rw [norm_inv, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hu)]
      have h5 : ‖u‖ * ‖u⁻¹‖^2 = ‖u⁻¹‖ := by
        calc ‖u‖ * ‖u⁻¹‖^2 = (‖u‖ * ‖u⁻¹‖) * ‖u⁻¹‖ := by ring
          _ = 1 * ‖u⁻¹‖ := by rw [h4]
          _ = ‖u⁻¹‖ := one_mul _
      rw [norm_mul, norm_mul, norm_inv, norm_pow, Complex.norm_real]
      calc ‖H u - H 0‖ * ‖cutProfile ε (‖u‖^2)‖ * (‖u‖^2)⁻¹
          ≤ (C * ‖u‖) * 1 * (‖u⁻¹‖^2) := by
            rw [h3]
            refine mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _)
              (mul_nonneg hC0 (norm_nonneg u))) le_rfl (by positivity)
              (mul_nonneg (mul_nonneg hC0 (norm_nonneg u)) zero_le_one)
        _ = C * ‖u⁻¹‖ := by rw [mul_one, mul_assoc, h5]
  -- measurability, for the dominated convergence theorem
  have hmeasF : ∀ ε : ℝ, AEStronglyMeasurable
      (fun u : ℂ => (H u - H 0) * (cutProfile ε (‖u‖^2) : ℂ) * (u^2)⁻¹)
      (volume.restrict (Metric.ball 0 R)) := by
    intro ε
    have h1 : Measurable (fun u : ℂ => H u - H 0) :=
      hH.continuous.measurable.sub measurable_const
    have h2 : Measurable (fun u : ℂ => (cutProfile ε (‖u‖^2) : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp
        (((differentiable_cutProfile ε).continuous.comp (continuous_norm.pow 2)).measurable)
    have h3 : Measurable (fun u : ℂ => (u^2)⁻¹) := (measurable_id.pow_const 2).inv
    exact ((h1.mul h2).mul h3).aestronglyMeasurable.mono_measure Measure.restrict_le_self
  -- integrability of the cutoff multiple of `w⁻²` over the disc
  have hIntφ : ∀ ε : ℝ, 0 < ε →
      Integrable (fun w : ℂ => (cutProfile ε (‖w‖^2) : ℂ) * (w^2)⁻¹)
        (volume.restrict (Metric.ball 0 R)) := by
    intro ε hε
    refine IntegrableOn.of_bound (measure_ball_lt_top) ?_ (1/ε^2) ?_
    · have h2 : Measurable (fun u : ℂ => (cutProfile ε (‖u‖^2) : ℂ)) :=
        Complex.continuous_ofReal.measurable.comp
          (((differentiable_cutProfile ε).continuous.comp (continuous_norm.pow 2)).measurable)
      have h3 : Measurable (fun u : ℂ => (u^2)⁻¹) := (measurable_id.pow_const 2).inv
      exact (h2.mul h3).aestronglyMeasurable.mono_measure Measure.restrict_le_self
    · filter_upwards with w
      rw [norm_mul]
      by_cases hw : ‖w‖ ≤ ε
      · have h0 : cutProfile ε (‖w‖^2) = 0 :=
          cutProfile_eq_zero_of_le hε (by nlinarith [norm_nonneg w])
        rw [h0]
        simp only [Complex.ofReal_zero, norm_zero, zero_mul]
        positivity
      · have hw' : ε < ‖w‖ := lt_of_not_ge hw
        have h1 : ‖cutProfile ε (‖w‖^2)‖ ≤ 1 := by
          have h := norm_ofReal_cutProfile_le_one ε w
          rwa [Complex.norm_real] at h
        have h2 : ‖(w^2)⁻¹‖ ≤ 1/ε^2 := by
          rw [norm_inv, norm_pow, one_div, inv_le_inv₀ (pow_pos (lt_trans hε hw') 2) (pow_pos hε 2)]
          nlinarith [norm_nonneg w, hw']
        rw [Complex.norm_real]
        calc ‖cutProfile ε (‖w‖^2)‖ * ‖(w^2)⁻¹‖ ≤ ‖cutProfile ε (‖w‖^2)‖ * (1/ε^2) :=
              mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
          _ ≤ 1 * (1/ε^2) := mul_le_mul_of_nonneg_right h1 (by positivity)
          _ = 1/ε^2 := one_mul _
  -- the constant part vanishes inside the disc, by rotational symmetry
  have hconst : ∀ ε : ℝ, 0 < ε →
      ∫ u in Metric.ball 0 R, (H 0 * (cutProfile ε (‖u‖^2) : ℂ)) * (u^2)⁻¹ ∂volume = 0 := by
    intro ε hε
    have h0 := integral_radial_weight_inv_sq_eq_zero (S := Metric.ball 0 R)
      (fun r : ℝ => cutProfile ε (r^2))
      (fun c w => by
        simp only [Metric.mem_ball, dist_zero_right, norm_mul, Circle.norm_coe, one_mul])
      (hIntφ ε hε)
    rw [show (fun u : ℂ => (H 0 * (cutProfile ε (‖u‖^2) : ℂ)) * (u^2)⁻¹)
        = fun u : ℂ => H 0 * ((cutProfile ε (‖u‖^2) : ℂ) * (u^2)⁻¹) by funext u; ring]
    rw [MeasureTheory.integral_const_mul, h0, mul_zero]
  -- step 1: the full-space integral is an integral over the disc
  have hball_eq : ∀ ε : ℝ, ∫ u, H u * (cutProfile ε (‖u‖^2) : ℂ) * (u^2)⁻¹ ∂volume
      = ∫ u in Metric.ball 0 R, H u * (cutProfile ε (‖u‖^2) : ℂ) * (u^2)⁻¹ ∂volume := by
    intro ε
    rw [← MeasureTheory.integral_indicator measurableSet_ball]
    apply integral_congr_ae
    filter_upwards with u
    by_cases hu : u ∈ Metric.ball 0 R
    · rw [Set.indicator_of_mem hu]
    · rw [Set.indicator_of_notMem hu]
      have hnorm : R ≤ ‖u‖ := by
        rw [Metric.mem_ball, dist_zero_right, not_lt] at hu
        exact hu
      rw [hsupp u hnorm]; ring
  -- step 2: dominated convergence inside the disc
  have hDCT : Filter.Tendsto
      (fun ε : ℝ => ∫ u, (H u - H 0) * (cutProfile ε (‖u‖^2) : ℂ) * (u^2)⁻¹
        ∂(volume.restrict (Metric.ball 0 R)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ u, (H u - H 0) * (u^2)⁻¹ ∂(volume.restrict (Metric.ball 0 R)))) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun u : ℂ => C * ‖u⁻¹‖) ?_ ?_ hdom_int ?_
    · filter_upwards with ε
      exact hmeasF ε
    · filter_upwards with ε
      exact Filter.Eventually.of_forall (hbound ε)
    · have hne : ∀ᵐ u : ℂ ∂(volume : Measure ℂ), u ≠ 0 := by
        rw [MeasureTheory.ae_iff]
        simp
      filter_upwards [MeasureTheory.ae_restrict_of_ae hne] with u hu
      have hev : (fun ε : ℝ => (H u - H 0) * (cutProfile ε (‖u‖^2) : ℂ) * (u^2)⁻¹)
          =ᶠ[nhdsWithin 0 (Set.Ioi 0)] (fun _ => (H u - H 0) * (u^2)⁻¹) := by
        filter_upwards [cutProfile_eventually_one u hu] with ε hε
        simp [hε]
      exact Filter.Tendsto.congr' hev.symm tendsto_const_nhds
  -- step 3: putting everything together
  refine hDCT.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [hball_eq ε]
  have hInt1 : Integrable (fun u : ℂ => (H 0 * (cutProfile ε (‖u‖^2) : ℂ)) * (u^2)⁻¹)
      (volume.restrict (Metric.ball 0 R)) := by
    refine ((hIntφ ε hε).const_mul (H 0)).congr (Filter.Eventually.of_forall (fun u => ?_))
    ring
  have hInt2 : Integrable (fun u : ℂ => (H u - H 0) * (cutProfile ε (‖u‖^2) : ℂ) * (u^2)⁻¹)
      (volume.restrict (Metric.ball 0 R)) :=
    hdom_int.mono' (hmeasF ε) (Filter.Eventually.of_forall (hbound ε))
  have hsum : (fun u : ℂ => (H 0 * (cutProfile ε (‖u‖^2) : ℂ)) * (u^2)⁻¹
        + (H u - H 0) * (cutProfile ε (‖u‖^2) : ℂ) * (u^2)⁻¹)
      = fun u : ℂ => H u * (cutProfile ε (‖u‖^2) : ℂ) * (u^2)⁻¹ := by
    funext u; ring
  rw [← hsum, MeasureTheory.integral_add hInt1 hInt2, hconst ε hε, zero_add]

end Work.Beltrami
