import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Interfaces.FatouNarrow
import Submission.Work.FatouCoord.Petal.reflected_inverse_germ
import Submission.Work.Pert.lintegral_cauchy_density

/-!
# `F₀ = τ₀ ∘ f₀ ∘ τ₀` is a near translation on the two limit regions

For a parabolic germ `f₀` (`f₀ z = z + z² + O(z³)`) the model map
`F₀ w = τ₀ (f₀ (τ₀ w))`, `τ₀ w = -1/w`, is the `α → 0` limit of the perturbed lifts
`F_f = liftF u σ α` of Shishikura §4.2.  This file proves that `F₀` is a near translation
(`NearTranslationL1`) on the two limit gate regions

* `Qreg (some ξ) none`, the limit of `Qreg (some ξ) (some (-ξ+1/α))`,
* `Qreg none (some (-ξ))`, the limit of `Qreg (some (ξ-1/α)) (some (-ξ))`,

for some `ξ > 0` depending on the germ data.  This is the hypothesis that
`MandelDim.FatouContinuity` / `MandelDim.FatouEnds` need at the limit; it generalises
`Work.Pert.nearTranslationL1_limit_f0` (the special case `f₀ z = z + z²`).

The two estimates are:

* the germ expansion `f₀ u = u + u² q u` with `q = 1 + O(u)` gives, for `u = τ₀ w`,
  `F₀ w - (w + 1) = (q u (1-u) - 1)/(1 + u q u) = O(1/w)` and
  `F₀' w - 1 = u² (q' u - q u²)/(1 + u q u)² = O(1/w²)` (the cancellation of the linear
  term, i.e. `q 0 = 1`, is what makes the L¹ integral converge),
* both regions contain `{|z| > ξ/2}`, so `|τ₀ w| ≤ 2/ξ` and the numerical bounds follow.
-/

namespace Work.Pert
namespace NTF0

open Set Filter Metric Complex MeasureTheory
open scoped Topology

noncomputable section

/-! ## Elementary facts about `τ₀ w = -1/w` -/

lemma tau0_invol {w : ℂ} (hw : w ≠ 0) : MandelDim.tau0 (MandelDim.tau0 w) = w := by
  simp only [MandelDim.tau0]
  field_simp

lemma norm_tau0 (w : ℂ) : ‖MandelDim.tau0 w‖ = 1 / ‖w‖ := by
  simp [MandelDim.tau0, norm_neg, norm_one]

lemma tau0_ne_zero {w : ℂ} (hw : w ≠ 0) : MandelDim.tau0 w ≠ 0 := by
  simp [MandelDim.tau0, hw]

lemma differentiableAt_tau0 {v : ℂ} (hv : v ≠ 0) : DifferentiableAt ℂ MandelDim.tau0 v := by
  rw [show MandelDim.tau0 = fun y : ℂ => (-1 : ℂ) * y⁻¹ from rfl]
  exact (differentiableAt_inv_iff.mpr hv).const_mul (-1)

lemma deriv_tau0 {v : ℂ} (hv : v ≠ 0) : deriv MandelDim.tau0 v = (v ^ 2)⁻¹ := by
  rw [show MandelDim.tau0 = fun y : ℂ => (-1 : ℂ) * y⁻¹ from rfl]
  rw [deriv_const_mul (-1) ((hasDerivAt_inv hv).differentiableAt), deriv_inv]
  ring

/-! ## The Cauchy density with a constant -/

/-- `∫⁻ y, ‖K / (a² + y²)‖ ≤ K π / |a|`: the exact mass of the Cauchy density, with a constant. -/
theorem lintegral_cauchy_density_const {K a : ℝ} (hK : 0 ≤ K) (ha : a ≠ 0) :
    ∫⁻ y : ℝ, ENNReal.ofReal (K * (a ^ 2 + y ^ 2)⁻¹) ≤ ENNReal.ofReal (K * Real.pi / |a|) := by
  have hb : (1 / a : ℝ) ≠ 0 := by simp [ha]
  have hfun : (fun y : ℝ => (a ^ 2 + y ^ 2)⁻¹)
      = fun y => (a ^ 2)⁻¹ * (1 + ((1 / a) * y) ^ 2)⁻¹ := by
    funext y; field_simp
  have hbase : Integrable (fun y : ℝ => (a ^ 2 + y ^ 2)⁻¹) := by
    rw [hfun]; exact (integrable_inv_one_add_mul_sq hb).const_mul _
  have hint : Integrable (fun y : ℝ => K * (a ^ 2 + y ^ 2)⁻¹) := hbase.const_mul K
  have hnn : 0 ≤ᵐ[volume] (fun y : ℝ => K * (a ^ 2 + y ^ 2)⁻¹) :=
    Filter.Eventually.of_forall fun y => by
      have h1 : (0 : ℝ) < (a ^ 2 + y ^ 2)⁻¹ := by
        apply inv_pos.mpr; positivity
      positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  rw [MeasureTheory.integral_const_mul, integral_inv_sq_add_sq ha]
  apply ENNReal.ofReal_le_ofReal
  rw [mul_div_assoc]

/-! ## Geometry of the two limit regions -/

/-- On `Qreg (some ξ) none = {Re z + |Im z| > ξ}` one has `Re z + |Im z| > ξ`. -/
lemma re_add_abs_im_gt {ξ : ℝ} {z : ℂ} (hz : z ∈ MandelDim.Qreg (some (ξ : ℂ)) none) :
    ξ < z.re + |z.im| := by
  have h := hz
  simp only [MandelDim.Qreg, Set.mem_ofPred_eq] at h
  have h1 := h.1 (ξ : ℂ) rfl
  have hre : (z - (ξ : ℂ)).re = z.re - ξ := by simp
  have him : (z - (ξ : ℂ)).im = z.im := by simp
  rw [hre, him] at h1
  linarith

/-- On `Qreg none (some (-ξ)) = {Re z + ξ < |Im z|}` one has `Re z + ξ < |Im z|`. -/
lemma abs_im_gt_re_add {ξ : ℝ} {z : ℂ} (hz : z ∈ MandelDim.Qreg none (some (-(ξ : ℂ)))) :
    z.re + ξ < |z.im| := by
  have h := hz
  simp only [MandelDim.Qreg, Set.mem_ofPred_eq] at h
  have h2 := h.2 (-(ξ : ℂ)) rfl
  have hre : (z - (-(ξ : ℂ))).re = z.re + ξ := by simp
  have him : (z - (-(ξ : ℂ))).im = z.im := by simp
  rw [hre, him] at h2
  exact h2

/-- Both limit regions are contained in the exterior of the disc of radius `ξ/2`. -/
lemma norm_gt_of_mem_right {ξ : ℝ} {z : ℂ} (hz : z ∈ MandelDim.Qreg (some (ξ : ℂ)) none) :
    ξ / 2 < ‖z‖ := by
  have h := re_add_abs_im_gt hz
  have h1 : z.re ≤ ‖z‖ := le_trans (le_abs_self _) (Complex.abs_re_le_norm z)
  have h2 : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
  linarith

lemma norm_gt_of_mem_left {ξ : ℝ} {z : ℂ} (hz : z ∈ MandelDim.Qreg none (some (-(ξ : ℂ)))) :
    ξ / 2 < ‖z‖ := by
  have h := abs_im_gt_re_add hz
  have h1 : -‖z‖ ≤ z.re := by
    have := Complex.abs_re_le_norm z
    have : -|z.re| ≤ z.re := neg_abs_le z.re
    linarith
  have h2 : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
  linarith

/-- A whole vertical line inside the right region has real part `≥ ξ`. -/
lemma line_re_ge {ξ : ℝ} {x : ℝ}
    (hx : ∀ y : ℝ, (x : ℂ) + y * I ∈ MandelDim.Qreg (some (ξ : ℂ)) none) : ξ ≤ x := by
  have h := re_add_abs_im_gt (hx 0)
  simpa using h.le

/-- A whole vertical line inside the left region has real part `≤ -ξ`. -/
lemma line_re_le {ξ : ℝ} {x : ℝ}
    (hx : ∀ y : ℝ, (x : ℂ) + y * I ∈ MandelDim.Qreg none (some (-(ξ : ℂ)))) : x ≤ -ξ := by
  have h := abs_im_gt_re_add (hx 0)
  have h' : x + ξ < 0 := by simpa using h
  linarith


/-! ## The pointwise estimates at the limit -/

/-- Pointwise bounds for `F₀ w = τ₀ (f₀ (τ₀ w))` from the germ expansion `f₀ u = u + u² q u`.

If `q = 1 + O(u)` on `ball 0 r` (`r ≤ 1/4`), then for `u = τ₀ w ∈ ball 0 r`
one has `f₀ u ≠ 0`, `F₀ w = w/(1 + u q u)`, hence
`F₀ w - (w+1) = O(‖u‖)` and `F₀' w - 1 = O(‖u‖²)`. -/
theorem limit_germ_pointwise_local {f₀ q : ℂ → ℂ} {D : Set ℂ} {b : ℂ} {r A2 A3 : ℝ}
    (hD : IsOpen D) (hr : 0 < r) (hrD : Metric.ball (0 : ℂ) r ⊆ D)
    (hr4 : r ≤ 1 / 4) (hfdiff : DifferentiableOn ℂ f₀ D)
    (hA2 : 0 ≤ A2) (hA3 : 0 ≤ A3)
    (hqdiff : DifferentiableOn ℂ q (Metric.ball (0 : ℂ) r))
    (hq : ∀ u ∈ Metric.ball (0 : ℂ) r, f₀ u = u + u ^ 2 * q u)
    (hq1 : ∀ u ∈ Metric.ball (0 : ℂ) r, ‖q u - 1 - b * u‖ ≤ A2 * ‖u‖ ^ 2)
    (hq2 : ∀ u ∈ Metric.ball (0 : ℂ) r, ‖q u‖ ≤ 2)
    (hq3 : ∀ u ∈ Metric.ball (0 : ℂ) r, ‖deriv q u‖ ≤ A3) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ w : ℂ, w ≠ 0 → MandelDim.tau0 w ∈ Metric.ball (0 : ℂ) r →
      f₀ (MandelDim.tau0 w) ≠ 0 ∧
      ‖MandelDim.tau0 (f₀ (MandelDim.tau0 w)) - (w + 1)‖ ≤ C * ‖MandelDim.tau0 w‖ ∧
      ‖deriv (fun z : ℂ => MandelDim.tau0 (f₀ (MandelDim.tau0 z))) w - 1‖
        ≤ K * ‖MandelDim.tau0 w‖ ^ 2 ∧
      DifferentiableAt ℂ (fun z : ℂ => MandelDim.tau0 (f₀ (MandelDim.tau0 z))) w := by
  refine ⟨2 * (A2 * (5 / 16) + (‖b‖ + 1) + ‖b‖ / 4) + 1, 4 * (A3 + 4) + 1,
    by positivity, by positivity, ?_⟩
  intro w hw hwu
  set u := MandelDim.tau0 w with hu_def
  have hun : 0 ≤ ‖u‖ := norm_nonneg u
  have hu_mem : u ∈ Metric.ball (0 : ℂ) r := hwu
  have hu_norm_lt : ‖u‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hu_mem
  have hu_norm_lt4 : ‖u‖ < 1 / 4 := lt_of_lt_of_le hu_norm_lt hr4
  have hu_ne : u ≠ 0 := by rw [hu_def]; simp [MandelDim.tau0, hw]
  have hw_tau : w = MandelDim.tau0 u := by rw [hu_def]; simp only [MandelDim.tau0]; field_simp
  have hqd : DifferentiableAt ℂ q u := hqdiff.differentiableAt (Metric.isOpen_ball.mem_nhds hu_mem)
  have hfd : DifferentiableAt ℂ f₀ u := hfdiff.differentiableAt (hD.mem_nhds (hrD hu_mem))
  have hq_u : f₀ u = u + u ^ 2 * q u := hq u hu_mem
  have hq_norm : ‖q u‖ ≤ 2 := hq2 u hu_mem
  have hq_norm_sq : ‖q u‖ ^ 2 ≤ 4 := by nlinarith [hq_norm, norm_nonneg (q u)]
  have huq_lt : ‖u * q u‖ < 1 := by rw [norm_mul]; nlinarith
  have hden : (1 : ℂ) + u * q u ≠ 0 := by
    intro h
    have h1 : u * q u = -1 := by linear_combination h
    rw [h1, norm_neg, norm_one] at huq_lt
    exact lt_irrefl 1 huq_lt
  have hden_lb : (1 : ℝ) / 2 ≤ ‖1 + u * q u‖ := by
    have h := norm_sub_le ((1 : ℂ) + u * q u) (u * q u)
    have h' : (1 : ℝ) ≤ ‖1 + u * q u‖ + ‖u * q u‖ := by simpa using h
    have h2 : ‖u * q u‖ ≤ 1 / 2 := by rw [norm_mul]; nlinarith
    linarith
  have hf0_eq : f₀ u = u * (1 + u * q u) := by rw [hq_u]; ring
  have hf0_ne : f₀ u ≠ 0 := by rw [hf0_eq]; exact mul_ne_zero hu_ne hden
  refine ⟨hf0_ne, ?_, ?_, ?_⟩
  · -- the value bound
    have hT1 : MandelDim.tau0 (f₀ u) = w / (1 + u * q u) := by
      rw [hq_u, hw_tau]
      simp only [MandelDim.tau0]
      field_simp
    have hval : MandelDim.tau0 (f₀ u) - (w + 1) = (q u * (1 - u) - 1) / (1 + u * q u) := by
      rw [hT1, hw_tau]
      simp only [MandelDim.tau0]
      field_simp
      ring
    have hnum : ‖q u * (1 - u) - 1‖ ≤ (A2 * (5 / 16) + (‖b‖ + 1) + ‖b‖ / 4) * ‖u‖ := by
      have h2 : ‖u‖ ^ 2 ≤ (1 / 4) * ‖u‖ := by nlinarith
      have h3 : ‖u‖ ^ 3 ≤ (1 / 16) * ‖u‖ := by nlinarith
      have h2' : A2 * ‖u‖ ^ 2 ≤ A2 * ((1 / 4) * ‖u‖) := mul_le_mul_of_nonneg_left h2 hA2
      have h3' : A2 * ‖u‖ ^ 3 ≤ A2 * ((1 / 16) * ‖u‖) := mul_le_mul_of_nonneg_left h3 hA2
      have h4 : ‖b‖ * ‖u‖ ^ 2 ≤ ‖b‖ * ((1 / 4) * ‖u‖) :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg b)
      have hsplit : q u * (1 - u) - 1
          = (q u - 1 - b * u) * (1 - u) + ((1 + b * u) * (1 - u) - 1) := by ring
      have hA : ‖(q u - 1 - b * u) * (1 - u)‖ ≤ A2 * ‖u‖ ^ 2 * (1 + ‖u‖) := by
        rw [norm_mul]
        have h1 : ‖1 - u‖ ≤ 1 + ‖u‖ := by
          calc ‖1 - u‖ ≤ ‖(1 : ℂ)‖ + ‖u‖ := norm_sub_le 1 u
            _ = 1 + ‖u‖ := by simp
        calc ‖q u - 1 - b * u‖ * ‖1 - u‖ ≤ (A2 * ‖u‖ ^ 2) * (1 + ‖u‖) :=
              mul_le_mul (hq1 u hu_mem) h1 (norm_nonneg _) (by positivity)
          _ = A2 * ‖u‖ ^ 2 * (1 + ‖u‖) := by ring
      have hB : ‖(1 + b * u) * (1 - u) - 1‖ ≤ (‖b‖ + 1) * ‖u‖ + ‖b‖ * ‖u‖ ^ 2 := by
        have heq : (1 + b * u) * (1 - u) - 1 = (b - 1) * u - b * u ^ 2 := by ring
        rw [heq]
        calc ‖(b - 1) * u - b * u ^ 2‖ ≤ ‖(b - 1) * u‖ + ‖b * u ^ 2‖ := norm_sub_le _ _
          _ = ‖b - 1‖ * ‖u‖ + ‖b‖ * ‖u‖ ^ 2 := by rw [norm_mul, norm_mul, norm_pow]
          _ ≤ (‖b‖ + 1) * ‖u‖ + ‖b‖ * ‖u‖ ^ 2 := by
              have h : ‖b - 1‖ ≤ ‖b‖ + 1 := by
                calc ‖b - 1‖ ≤ ‖b‖ + ‖(1 : ℂ)‖ := norm_sub_le b 1
                  _ = ‖b‖ + 1 := by simp
              nlinarith [norm_nonneg u]
      calc ‖q u * (1 - u) - 1‖
          = ‖(q u - 1 - b * u) * (1 - u) + ((1 + b * u) * (1 - u) - 1)‖ := by rw [hsplit]
        _ ≤ ‖(q u - 1 - b * u) * (1 - u)‖ + ‖(1 + b * u) * (1 - u) - 1‖ := norm_add_le _ _
        _ ≤ A2 * ‖u‖ ^ 2 * (1 + ‖u‖) + ((‖b‖ + 1) * ‖u‖ + ‖b‖ * ‖u‖ ^ 2) := add_le_add hA hB
        _ ≤ (A2 * (5 / 16) + (‖b‖ + 1) + ‖b‖ / 4) * ‖u‖ := by nlinarith [h2', h3', h4]
    rw [hval, norm_div]
    have hstep : ‖q u * (1 - u) - 1‖ / ‖1 + u * q u‖ ≤ ‖q u * (1 - u) - 1‖ / (1 / 2) :=
      div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) hden_lb
    calc ‖q u * (1 - u) - 1‖ / ‖1 + u * q u‖
        ≤ ‖q u * (1 - u) - 1‖ / (1 / 2) := hstep
      _ = 2 * ‖q u * (1 - u) - 1‖ := by ring
      _ ≤ 2 * ((A2 * (5 / 16) + (‖b‖ + 1) + ‖b‖ / 4) * ‖u‖) := by linarith [hnum]
      _ ≤ (2 * (A2 * (5 / 16) + (‖b‖ + 1) + ‖b‖ / 4) + 1) * ‖u‖ := by nlinarith [hun]
  · -- the derivative bound
    have hderiv_f : deriv f₀ u = 1 + 2 * u * q u + u ^ 2 * deriv q u := by
      have hev : f₀ =ᶠ[𝓝 u] fun v : ℂ => v + v ^ 2 * q v := by
        filter_upwards [Metric.isOpen_ball.mem_nhds hu_mem] with v hv
        exact hq v hv
      rw [hev.deriv_eq]
      have h6 := (hasDerivAt_id u).add (((hasDerivAt_id u).pow 2).mul hqd.hasDerivAt)
      have h := h6.deriv
      change deriv (id + id ^ 2 * q) u = 1 + 2 * u * q u + u ^ 2 * deriv q u
      rw [h]
      simp
      ring
    have hF_deriv : deriv (fun z : ℂ => MandelDim.tau0 (f₀ (MandelDim.tau0 z))) w
        = deriv f₀ u * u ^ 2 / (f₀ u) ^ 2 := by
      have hd_tau_w : DifferentiableAt ℂ MandelDim.tau0 w := differentiableAt_tau0 hw
      have hd_tau_fu : DifferentiableAt ℂ MandelDim.tau0 (f₀ u) := differentiableAt_tau0 hf0_ne
      have hd_f_tau : DifferentiableAt ℂ (fun z : ℂ => f₀ (MandelDim.tau0 z)) w :=
        hfd.comp w hd_tau_w
      have h1 : deriv (fun z : ℂ => f₀ (MandelDim.tau0 z)) w
          = deriv f₀ u * deriv MandelDim.tau0 w := by
        have h := deriv_comp w hfd hd_tau_w
        change deriv (f₀ ∘ MandelDim.tau0) w = deriv f₀ u * deriv MandelDim.tau0 w
        rw [h]
      have h2 : deriv (fun z : ℂ => MandelDim.tau0 (f₀ (MandelDim.tau0 z))) w
          = deriv MandelDim.tau0 (f₀ u) * deriv (fun z : ℂ => f₀ (MandelDim.tau0 z)) w := by
        have h := deriv_comp w hd_tau_fu hd_f_tau
        change deriv (MandelDim.tau0 ∘ fun z : ℂ => f₀ (MandelDim.tau0 z)) w
          = deriv MandelDim.tau0 (f₀ u) * deriv (fun z : ℂ => f₀ (MandelDim.tau0 z)) w
        rw [h]
      have hwinv : (w ^ 2)⁻¹ = u ^ 2 := by
        rw [hw_tau]
        simp only [MandelDim.tau0]
        field_simp
      rw [h2, h1, deriv_tau0 hf0_ne, deriv_tau0 hw, hwinv]
      field_simp
    have hkey : deriv f₀ u * u ^ 2 / (f₀ u) ^ 2 - 1
        = u ^ 2 * (deriv q u - q u ^ 2) / (1 + u * q u) ^ 2 := by
      rw [hderiv_f, hq_u]
      field_simp
      ring
    have hnum2 : ‖deriv q u - q u ^ 2‖ ≤ A3 + 4 := by
      calc ‖deriv q u - q u ^ 2‖ ≤ ‖deriv q u‖ + ‖q u ^ 2‖ := norm_sub_le _ _
        _ = ‖deriv q u‖ + ‖q u‖ ^ 2 := by rw [norm_pow]
        _ ≤ A3 + 4 := by nlinarith [hq3 u hu_mem, hq_norm_sq]
    have hden_sq : (1 / 4 : ℝ) ≤ ‖1 + u * q u‖ ^ 2 := by
      nlinarith [hden_lb, norm_nonneg (1 + u * q u)]
    rw [hF_deriv, hkey]
    simp only [norm_div, norm_mul, norm_pow]
    have hnum_sq : ‖u‖ ^ 2 * ‖deriv q u - q u ^ 2‖ ≤ ‖u‖ ^ 2 * (A3 + 4) :=
      mul_le_mul_of_nonneg_left hnum2 (by positivity)
    have hnn : 0 ≤ ‖u‖ ^ 2 * ‖deriv q u - q u ^ 2‖ := by positivity
    calc ‖u‖ ^ 2 * ‖deriv q u - q u ^ 2‖ / ‖1 + u * q u‖ ^ 2
        ≤ ‖u‖ ^ 2 * ‖deriv q u - q u ^ 2‖ / (1 / 4) :=
          div_le_div_of_nonneg_left hnn (by norm_num) hden_sq
      _ ≤ ‖u‖ ^ 2 * (A3 + 4) / (1 / 4) := div_le_div_of_nonneg_right hnum_sq (by norm_num)
      _ ≤ (4 * (A3 + 4) + 1) * ‖u‖ ^ 2 := by nlinarith [sq_nonneg ‖u‖]
  · -- differentiability
    have hd_tau_fu : DifferentiableAt ℂ MandelDim.tau0 (f₀ u) := differentiableAt_tau0 hf0_ne
    have hd_f_tau : DifferentiableAt ℂ (fun z : ℂ => f₀ (MandelDim.tau0 z)) w :=
      hfd.comp w (differentiableAt_tau0 hw)
    have h := hd_tau_fu.comp w hd_f_tau
    change DifferentiableAt ℂ (MandelDim.tau0 ∘ fun z : ℂ => f₀ (MandelDim.tau0 z)) w at h
    exact h

end

end NTF0


open Set Filter Metric Complex MeasureTheory
open scoped Topology

noncomputable section

/-- **`F₀ = τ₀ ∘ f₀ ∘ τ₀` is a near translation on the two limit regions.**  For every parabolic
germ `f₀` (`f₀ z = z + z² + O(z³)`) there is `ξ > 0` such that
`w ↦ τ₀ (f₀ (τ₀ w))` is a near translation with integrable defect on both
`Qreg (some ξ) none = {Re w + |Im w| > ξ}` and `Qreg none (some (-ξ)) = {|Im w| - Re w > ξ}`. -/
theorem nearTranslation_F0 {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (h₀ : MandelDim.IsParabolicGerm f₀ D₀) :
    ∃ ξ : ℝ, 0 < ξ ∧
      MandelDim.NearTranslationOn (fun w : ℂ => MandelDim.tau0 (f₀ (MandelDim.tau0 w)))
        (MandelDim.Qreg (some (ξ : ℂ)) none) ∧
      MandelDim.NearTranslationOn (fun w : ℂ => MandelDim.tau0 (f₀ (MandelDim.tau0 w)))
        (MandelDim.Qreg none (some (-(ξ : ℂ)))) ∧
      MandelDim.NearTranslationL1 (fun w : ℂ => MandelDim.tau0 (f₀ (MandelDim.tau0 w)))
        (MandelDim.Qreg (some (ξ : ℂ)) none) ∧
      MandelDim.NearTranslationL1 (fun w : ℂ => MandelDim.tau0 (f₀ (MandelDim.tau0 w)))
        (MandelDim.Qreg none (some (-(ξ : ℂ)))) := by
  obtain ⟨hD0open, h0D0, hdiff0, hf00, hd1, hd2⟩ := h₀
  have hFan : AnalyticAt ℂ f₀ 0 := hdiff0.analyticAt (hD0open.mem_nhds h0D0)
  have hF1 : iteratedDeriv 1 f₀ 0 = 1 := by rw [iteratedDeriv_one]; exact hd1
  have hF2 : iteratedDeriv 2 f₀ 0 = 2 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    exact hd2
  set b : ℂ := iteratedDeriv 3 f₀ 0 / 6 with hb
  obtain ⟨q, r', A2, A3, hr'pos, hA2, hA3, hq, hqdiff, hq1, hq2, hq3⟩ :=
    Work.FatouCoord.Petal.exists_parabolic_germ_bounds (b := b) hFan hf00 hF1 hF2
      (by rw [hb]; ring)
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.mp (hD0open.mem_nhds h0D0)
  set r : ℝ := min r' (min ε (1 / 4)) with hrdef
  have hr_le_r' : r ≤ r' := by rw [hrdef]; exact min_le_left _ _
  have hr_le_ε : r ≤ ε := by
    have h : r ≤ min ε (1 / 4) := by rw [hrdef]; exact min_le_right _ _
    exact le_trans h (min_le_left _ _)
  have hr_le4 : r ≤ 1 / 4 := by
    have h : r ≤ min ε (1 / 4) := by rw [hrdef]; exact min_le_right _ _
    exact le_trans h (min_le_right _ _)
  have hrpos : 0 < r := by
    rw [hrdef]; exact lt_min hr'pos (lt_min hεpos (by norm_num))
  have hrD : Metric.ball (0 : ℂ) r ⊆ D₀ :=
    fun z hz => hεsub (Metric.ball_subset_ball hr_le_ε hz)
  have hrsub : Metric.ball (0 : ℂ) r ⊆ Metric.ball (0 : ℂ) r' := Metric.ball_subset_ball hr_le_r'
  obtain ⟨C, K, hCpos, hKpos, hbnd⟩ :=
    NTF0.limit_germ_pointwise_local hD0open hrpos hrD hr_le4 hdiff0 hA2 hA3 (hqdiff.mono hrsub)
      (fun u hu => hq u (hrsub hu)) (fun u hu => hq1 u (hrsub hu))
      (fun u hu => hq2 u (hrsub hu)) (fun u hu => hq3 u (hrsub hu))
  set ξ : ℝ := max (2 / r)
    (max (64 * C) (max (Real.sqrt (128 * K) + 1) (64 * Real.pi * K + 1))) with hξdef
  have hξpos : 0 < ξ := by
    rw [hξdef]
    exact lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hξ1 : 2 / r ≤ ξ := by rw [hξdef]; exact le_max_left _ _
  have hξ2 : 64 * C ≤ ξ := by
    rw [hξdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hξ3 : Real.sqrt (128 * K) + 1 ≤ ξ := by
    rw [hξdef]
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hξ4 : 64 * Real.pi * K + 1 ≤ ξ := by
    rw [hξdef]
    exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have h2ξ : 2 / ξ ≤ r := by
    rw [div_le_iff₀ hξpos]
    have h := hξ1
    rw [div_le_iff₀ hrpos] at h
    linarith
  have hC32 : C * (2 / ξ) ≤ 1 / 32 := by
    have h : 2 * C ≤ ξ / 32 := by linarith [hξ2]
    calc C * (2 / ξ) = 2 * C / ξ := by ring
      _ ≤ (ξ / 32) / ξ := div_le_div_of_nonneg_right h hξpos.le
      _ = 1 / 32 := by field_simp
  have hK32 : K * (2 / ξ) ^ 2 ≤ 1 / 32 := by
    have hsq : 128 * K ≤ ξ ^ 2 := by
      have h1 : Real.sqrt (128 * K) ≤ ξ := by linarith [hξ3]
      have h2 : (Real.sqrt (128 * K)) ^ 2 = 128 * K := Real.sq_sqrt (by positivity)
      have h3 : (Real.sqrt (128 * K)) ^ 2 ≤ ξ ^ 2 :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
      linarith
    have h : 4 * K ≤ ξ ^ 2 / 32 := by linarith
    calc K * (2 / ξ) ^ 2 = 4 * K / ξ ^ 2 := by field_simp; ring
      _ ≤ (ξ ^ 2 / 32) / ξ ^ 2 := div_le_div_of_nonneg_right h (by positivity)
      _ = 1 / 32 := by field_simp
  -- the common argument, for any region satisfying the two structural properties
  have region : ∀ (Q : Set ℂ), (∀ z ∈ Q, ξ / 2 < ‖z‖) →
      (∀ x : ℝ, (∀ y : ℝ, (x : ℂ) + y * I ∈ Q) → ξ ≤ |x|) →
      MandelDim.NearTranslationL1 (fun w : ℂ => MandelDim.tau0 (f₀ (MandelDim.tau0 w))) Q := by
    intro Q hQmem hline
    have hmem : ∀ z ∈ Q, MandelDim.tau0 z ∈ Metric.ball (0 : ℂ) r := by
      intro z hz
      have hlt : 1 / ‖z‖ < 1 / (ξ / 2) :=
        one_div_lt_one_div_of_lt (by linarith [hξpos]) (hQmem z hz)
      have h2 : 1 / (ξ / 2) = 2 / ξ := by ring
      rw [h2] at hlt
      rw [Metric.mem_ball, dist_zero_right, NTF0.norm_tau0]
      exact lt_of_lt_of_le hlt h2ξ
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro z hz
      have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith [hQmem z hz, hξpos])
      exact ((hbnd z hz0 (hmem z hz)).2.2.2).differentiableWithinAt
    · intro z hz
      have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith [hQmem z hz, hξpos])
      obtain ⟨-, hv, hd, -⟩ := hbnd z hz0 (hmem z hz)
      have hzu : ‖MandelDim.tau0 z‖ ≤ 2 / ξ := by
        have hlt : 1 / ‖z‖ < 1 / (ξ / 2) :=
          one_div_lt_one_div_of_lt (by linarith [hξpos]) (hQmem z hz)
        have h2 : 1 / (ξ / 2) = 2 / ξ := by ring
        rw [h2] at hlt
        rw [NTF0.norm_tau0]
        exact hlt.le
      refine ⟨?_, ?_⟩
      · calc ‖MandelDim.tau0 (f₀ (MandelDim.tau0 z)) - (z + 1)‖ ≤ C * ‖MandelDim.tau0 z‖ := hv
          _ ≤ C * (2 / ξ) := mul_le_mul_of_nonneg_left hzu hCpos.le
          _ ≤ 1 / 32 := hC32
      · calc ‖deriv (fun w : ℂ => MandelDim.tau0 (f₀ (MandelDim.tau0 w))) z - 1‖
            ≤ K * ‖MandelDim.tau0 z‖ ^ 2 := hd
          _ ≤ K * (2 / ξ) ^ 2 := mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (norm_nonneg _) hzu 2) hKpos.le
          _ ≤ 1 / 32 := hK32
    · intro x hx
      have hxa : ξ ≤ |x| := hline x hx
      have hx0 : x ≠ 0 := by
        intro h; rw [h, abs_zero] at hxa; linarith [hξpos]
      have hpt : ∀ y : ℝ, ‖deriv (fun w : ℂ => MandelDim.tau0 (f₀ (MandelDim.tau0 w)))
            ((x : ℂ) + y * I) - 1‖ ≤ K * (x ^ 2 + y ^ 2)⁻¹ := by
        intro y
        set w : ℂ := (x : ℂ) + y * I with hwdef
        have hwQ : w ∈ Q := hx y
        have hwp : 0 < ‖w‖ := by linarith [hQmem w hwQ, hξpos]
        have hw0 : w ≠ 0 := norm_pos_iff.mp hwp
        obtain ⟨-, -, hd, -⟩ := hbnd w hw0 (hmem w hwQ)
        have hnorm : ‖MandelDim.tau0 w‖ ^ 2 = (x ^ 2 + y ^ 2)⁻¹ := by
          have hwn2 : ‖w‖ ^ 2 = x ^ 2 + y ^ 2 := by
            rw [Complex.sq_norm, Complex.normSq_apply]
            simp [hwdef]
            ring
          rw [NTF0.norm_tau0, one_div, inv_pow, ← hwn2]
        calc ‖deriv (fun w : ℂ => MandelDim.tau0 (f₀ (MandelDim.tau0 w))) w - 1‖
            ≤ K * ‖MandelDim.tau0 w‖ ^ 2 := hd
          _ = K * (x ^ 2 + y ^ 2)⁻¹ := by rw [hnorm]
      calc ∫⁻ y : ℝ, ENNReal.ofReal ‖deriv (fun w : ℂ => MandelDim.tau0 (f₀ (MandelDim.tau0 w)))
              ((x : ℂ) + y * I) - 1‖
          ≤ ∫⁻ y : ℝ, ENNReal.ofReal (K * (x ^ 2 + y ^ 2)⁻¹) :=
            lintegral_mono (fun y => ENNReal.ofReal_le_ofReal (hpt y))
        _ ≤ ENNReal.ofReal (K * Real.pi / |x|) :=
            NTF0.lintegral_cauchy_density_const hKpos.le hx0
        _ ≤ ENNReal.ofReal (1 / 64) := by
            apply ENNReal.ofReal_le_ofReal
            have h1 : 64 * Real.pi * K ≤ |x| := le_trans (by linarith [hξ4]) hxa
            rw [div_le_iff₀ (abs_pos.mpr hx0)]
            nlinarith [h1]
  have hRmem : ∀ z ∈ MandelDim.Qreg (some (ξ : ℂ)) none, ξ / 2 < ‖z‖ :=
    fun z hz => NTF0.norm_gt_of_mem_right hz
  have hRline : ∀ x : ℝ, (∀ y : ℝ, (x : ℂ) + y * I ∈ MandelDim.Qreg (some (ξ : ℂ)) none) →
      ξ ≤ |x| := by
    intro x hx
    have h := NTF0.line_re_ge hx
    rw [abs_of_nonneg (by linarith [hξpos])]
    exact h
  have hLmem : ∀ z ∈ MandelDim.Qreg none (some (-(ξ : ℂ))), ξ / 2 < ‖z‖ :=
    fun z hz => NTF0.norm_gt_of_mem_left hz
  have hLline : ∀ x : ℝ, (∀ y : ℝ, (x : ℂ) + y * I ∈ MandelDim.Qreg none (some (-(ξ : ℂ)))) →
      ξ ≤ |x| := by
    intro x hx
    have h := NTF0.line_re_le hx
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hR := region (MandelDim.Qreg (some (ξ : ℂ)) none) hRmem hRline
  have hL := region (MandelDim.Qreg none (some (-(ξ : ℂ)))) hLmem hLline
  exact ⟨ξ, hξpos, hR.1, hL.1, hR, hL⟩

end

end Work.Pert
