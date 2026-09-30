import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Existence of a smooth cutoff with a quadratically decaying Mellin transform

We construct an explicit smooth bump function `bumpFn` which is `1` on `[1/2, 2]` and vanishes
outside `[1/4, 4]`, and we prove that its "Mellin transform"
`t ↦ ∫_{1/4}^{4} y^{it} φ(y) dy` decays like `1/(1+t^2)`.

The decay is obtained by integrating by parts twice: an antiderivative of `y^{it}` is
`y^{1+it}/(1+it)`, and of that, `y^{2+it}/((1+it)(2+it))`. Since `φ` (and its first derivative)
vanish at the endpoints, the boundary terms disappear. The crucial analytic input is that after
the substitution `y ↦ y^{it}` the two antiderivatives have norms bounded by `y/|1+it|` and
`y^2/|(1+it)(2+it)|`, and `|(1+it)(2+it)| ≥ 1+t^2`.

To avoid one-sided endpoints we integrate over the slightly larger interval `[1/8, 8]`, on which
`φ` and `φ'` vanish near *both* endpoints (since `φ` is constantly zero there), and then observe
that the integrand vanishes identically outside `[1/4, 4]`.
-/

namespace Work.BMF

open scoped Interval Topology
open MeasureTheory

/-- The smooth bump function `φ y = h(4y-1) · h(2 - y/2)` where `h = Real.smoothTransition`.
It equals `1` on `[1/2, 2]` and `0` outside `[1/4, 4]`. -/
noncomputable def bumpFn (y : ℝ) : ℝ :=
  Real.smoothTransition (4 * y - 1) * Real.smoothTransition (2 - y / 2)

lemma bumpFn_contDiff (k : ℕ) : ContDiff ℝ k bumpFn := by
  unfold bumpFn; fun_prop

lemma bumpFn_nonneg (y : ℝ) : 0 ≤ bumpFn y := by
  unfold bumpFn
  exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

lemma bumpFn_eq_one : ∀ y ∈ Set.Icc (1 / 2 : ℝ) 2, bumpFn y = 1 := by
  intro y hy
  rw [Set.mem_Icc] at hy
  unfold bumpFn
  rw [Real.smoothTransition.one_of_one_le (by linarith : (1 : ℝ) ≤ 4 * y - 1),
      Real.smoothTransition.one_of_one_le (by linarith : (1 : ℝ) ≤ 2 - y / 2)]
  ring

lemma bumpFn_eq_zero : ∀ y : ℝ, y ≤ 1 / 4 ∨ 4 ≤ y → bumpFn y = 0 := by
  intro y hy
  unfold bumpFn
  rcases hy with h | h
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith : 4 * y - 1 ≤ 0), zero_mul]
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith : 2 - y / 2 ≤ 0), mul_zero]

lemma bumpFn_eighth : bumpFn (1 / 8) = 0 := bumpFn_eq_zero _ (Or.inl (by norm_num))

lemma bumpFn_eight : bumpFn 8 = 0 := bumpFn_eq_zero _ (Or.inr (by norm_num))

/-- `φ` vanishes identically on a neighbourhood of any point below `1/4`, hence so does `φ'`. -/
lemma deriv_bumpFn_eq_zero_of_lt {y : ℝ} (hy : y < 1 / 4) : deriv bumpFn y = 0 := by
  have hev : bumpFn =ᶠ[𝓝 y] (fun _ => 0) := by
    apply Filter.eventually_of_mem (isOpen_Iio.mem_nhds (Set.mem_Iio.mpr hy))
    intro z hz
    exact bumpFn_eq_zero z (Or.inl (le_of_lt hz))
  exact ((hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq hev).deriv

/-- `φ` vanishes identically on a neighbourhood of any point above `4`, hence so does `φ'`. -/
lemma deriv_bumpFn_eq_zero_of_gt {y : ℝ} (hy : 4 < y) : deriv bumpFn y = 0 := by
  have hev : bumpFn =ᶠ[𝓝 y] (fun _ => 0) := by
    apply Filter.eventually_of_mem (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr hy))
    intro z hz
    exact bumpFn_eq_zero z (Or.inr (le_of_lt hz))
  exact ((hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq hev).deriv

/-- The map `y ↦ y^{it}` (with `y > 0`) is continuous at `y`. -/
lemma continuousAt_ofReal_cpow (t : ℝ) {y : ℝ} (hy : 0 < y) :
    ContinuousAt (fun y : ℝ => (y : ℂ) ^ (Complex.I * (t : ℂ))) y :=
  (continuousAt_cpow_const (by rwa [Complex.ofReal_mem_slitPlane])).comp
    Complex.continuous_ofReal.continuousAt

/-- On the positive reals, the antiderivative `y ↦ y^{1+it}/(1+it)` of `y ↦ y^{it}`. -/
lemma hasDerivAt_cpow_F (t : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ (Complex.I * (t : ℂ) + 1) / (Complex.I * (t : ℂ) + 1))
      ((y : ℂ) ^ (Complex.I * (t : ℂ))) y := by
  have hc1 : (Complex.I * (t : ℂ) + 1) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [Complex.mul_re, Complex.add_re] at hre
  have h := (hasDerivAt_ofReal_cpow_const (ne_of_gt hy) hc1).div_const (Complex.I * (t : ℂ) + 1)
  have hsub : Complex.I * (t : ℂ) + 1 - 1 = Complex.I * (t : ℂ) := by ring
  rw [hsub] at h
  convert h using 1
  field_simp

/-- On the positive reals, the antiderivative `y ↦ y^{2+it}/((1+it)(2+it))` of
`y ↦ y^{1+it}/(1+it)`. -/
lemma hasDerivAt_cpow_G (t : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ (Complex.I * (t : ℂ) + 2) /
        ((Complex.I * (t : ℂ) + 1) * (Complex.I * (t : ℂ) + 2)))
      ((y : ℂ) ^ (Complex.I * (t : ℂ) + 1) / (Complex.I * (t : ℂ) + 1)) y := by
  have hc1 : (Complex.I * (t : ℂ) + 1) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [Complex.mul_re, Complex.add_re] at hre
  have hc2 : (Complex.I * (t : ℂ) + 2) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [Complex.mul_re, Complex.add_re] at hre
  have h := (hasDerivAt_ofReal_cpow_const (ne_of_gt hy) hc2).div_const
    ((Complex.I * (t : ℂ) + 1) * (Complex.I * (t : ℂ) + 2))
  have hsub : Complex.I * (t : ℂ) + 2 - 1 = Complex.I * (t : ℂ) + 1 := by ring
  rw [hsub] at h
  convert h using 1
  field_simp

/-- `|(1+it)(2+it)| ≥ 1 + t²`, the key lower bound producing the quadratic decay. -/
lemma one_add_sq_le_norm (t : ℝ) :
    1 + t ^ 2 ≤ ‖(Complex.I * (t : ℂ) + 1) * (Complex.I * (t : ℂ) + 2)‖ := by
  have h2 : ‖(Complex.I * (t : ℂ) + 1) * (Complex.I * (t : ℂ) + 2)‖ ^ 2
      = (1 + t ^ 2) * (4 + t ^ 2) := by
    rw [Complex.sq_norm, Complex.normSq_mul]
    congr 1
    · rw [Complex.normSq_apply]
      simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]; ring
    · rw [Complex.normSq_apply]
      simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]; ring
  set D := ‖(Complex.I * (t : ℂ) + 1) * (Complex.I * (t : ℂ) + 2)‖ with hD
  have hkey : (D - (1 + t ^ 2)) * (D + (1 + t ^ 2)) = D ^ 2 - (1 + t ^ 2) ^ 2 := by ring
  have hnn : 0 ≤ D ^ 2 - (1 + t ^ 2) ^ 2 := by rw [h2]; nlinarith [sq_nonneg t]
  have hprod : 0 ≤ (D - (1 + t ^ 2)) * (D + (1 + t ^ 2)) := by rw [hkey]; exact hnn
  have hpos : 0 < D + (1 + t ^ 2) := by positivity
  have := nonneg_of_mul_nonneg_left hprod hpos
  linarith

/-- The integrand vanishes outside `[1/4, 4]`, so the integral over `[1/8, 8]` agrees with the
integral over `[1/4, 4]`. -/
lemma integral_shift (t : ℝ) :
    ∫ y in (1 / 4 : ℝ)..4, (y : ℂ) ^ (Complex.I * (t : ℂ)) * (bumpFn y : ℂ)
      = ∫ y in (1 / 8 : ℝ)..8, (y : ℂ) ^ (Complex.I * (t : ℂ)) * (bumpFn y : ℂ) := by
  rw [intervalIntegral.integral_of_le (by norm_num : (1 / 8 : ℝ) ≤ 8),
      intervalIntegral.integral_of_le (by norm_num : (1 / 4 : ℝ) ≤ 4)]
  symm
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
  · exact measurableSet_Ioc
  · intro x hx
    rw [Set.mem_Ioc] at hx ⊢
    exact ⟨lt_of_le_of_lt (by norm_num : (1 / 8 : ℝ) ≤ 1 / 4) hx.1,
      le_trans hx.2 (by norm_num : (4 : ℝ) ≤ 8)⟩
  · intro x hx
    rw [Set.mem_sdiff] at hx
    obtain ⟨hxt, hxs⟩ := hx
    by_cases h4 : 4 ≤ x
    · rw [bumpFn_eq_zero x (Or.inr h4), Complex.ofReal_zero, mul_zero]
    · rw [not_le] at h4
      have hxle : x ≤ 1 / 4 := by
        by_contra h
        rw [not_le] at h
        exact hxs (by rw [Set.mem_Ioc]; exact ⟨h, le_of_lt h4⟩)
      rw [bumpFn_eq_zero x (Or.inl hxle), Complex.ofReal_zero, mul_zero]

/-- Two integrations by parts turn `∫ y^{it} φ(y) dy` into `∫ y^{2+it} φ''(y) dy /((1+it)(2+it))`. -/
lemma integral_ibp (t : ℝ) :
    ∫ y in (1 / 8 : ℝ)..8, (y : ℂ) ^ (Complex.I * (t : ℂ)) * (bumpFn y : ℂ)
      = ∫ y in (1 / 8 : ℝ)..8, (y : ℂ) ^ (Complex.I * (t : ℂ) + 2) /
          ((Complex.I * (t : ℂ) + 1) * (Complex.I * (t : ℂ) + 2)) *
            (((deriv (deriv bumpFn) y : ℝ) : ℂ)) := by
  have hfd : Differentiable ℝ bumpFn := (bumpFn_contDiff 1).differentiable (by norm_num)
  have hfd2 : Differentiable ℝ (deriv bumpFn) :=
    ContDiff.differentiable_deriv_two (bumpFn_contDiff 2)
  have hcd : Continuous (deriv bumpFn) := (bumpFn_contDiff 1).continuous_deriv (by norm_num)
  have hcdd : Continuous (deriv (deriv bumpFn)) := by
    have hC2' : ContDiff ℝ 1 (deriv bumpFn) := by
      simpa using ContDiff.iterate_deriv' (𝕜 := ℝ) 1 1 (bumpFn_contDiff 2)
    exact hC2'.continuous_deriv le_rfl
  -- first integration by parts
  have hu1 : ∀ y ∈ Set.uIcc (1 / 8 : ℝ) 8,
      HasDerivAt (fun y : ℝ => (y : ℂ) ^ (Complex.I * (t : ℂ) + 1) / (Complex.I * (t : ℂ) + 1))
        ((y : ℂ) ^ (Complex.I * (t : ℂ))) y := by
    intro y hy
    rw [Set.uIcc_of_le (by norm_num : (1 / 8 : ℝ) ≤ 8)] at hy
    rw [Set.mem_Icc] at hy
    exact hasDerivAt_cpow_F t (by linarith [hy.1])
  have hv1 : ∀ y ∈ Set.uIcc (1 / 8 : ℝ) 8,
      HasDerivAt (fun y : ℝ => (bumpFn y : ℂ)) (((deriv bumpFn y : ℝ) : ℂ)) y := by
    intro y hy
    exact HasDerivAt.ofReal_comp ((hfd y).hasDerivAt)
  have hu1' : IntervalIntegrable (fun y : ℝ => (y : ℂ) ^ (Complex.I * (t : ℂ)))
      volume (1 / 8) 8 := by
    apply ContinuousOn.intervalIntegrable
    intro y hy
    rw [Set.uIcc_of_le (by norm_num : (1 / 8 : ℝ) ≤ 8)] at hy
    rw [Set.mem_Icc] at hy
    exact (continuousAt_ofReal_cpow t (by linarith [hy.1])).continuousWithinAt
  have hv1' : IntervalIntegrable (fun y : ℝ => ((deriv bumpFn y : ℝ) : ℂ))
      volume (1 / 8) 8 :=
    (Complex.continuous_ofReal.comp hcd).intervalIntegrable (1 / 8) 8
  have h1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu1 hv1 hu1' hv1'
  simp only [bumpFn_eight, bumpFn_eighth, Complex.ofReal_zero, mul_zero, sub_zero,
    zero_sub] at h1
  -- second integration by parts
  have hu2 : ∀ y ∈ Set.uIcc (1 / 8 : ℝ) 8,
      HasDerivAt (fun y : ℝ => (y : ℂ) ^ (Complex.I * (t : ℂ) + 2) /
          ((Complex.I * (t : ℂ) + 1) * (Complex.I * (t : ℂ) + 2)))
        ((y : ℂ) ^ (Complex.I * (t : ℂ) + 1) / (Complex.I * (t : ℂ) + 1)) y := by
    intro y hy
    rw [Set.uIcc_of_le (by norm_num : (1 / 8 : ℝ) ≤ 8)] at hy
    rw [Set.mem_Icc] at hy
    exact hasDerivAt_cpow_G t (by linarith [hy.1])
  have hv2 : ∀ y ∈ Set.uIcc (1 / 8 : ℝ) 8,
      HasDerivAt (fun y : ℝ => (((deriv bumpFn y : ℝ) : ℂ)))
        (((deriv (deriv bumpFn) y : ℝ) : ℂ)) y := by
    intro y hy
    exact HasDerivAt.ofReal_comp ((hfd2 y).hasDerivAt)
  have hu2' : IntervalIntegrable (fun y : ℝ => (y : ℂ) ^ (Complex.I * (t : ℂ) + 1) /
      (Complex.I * (t : ℂ) + 1)) volume (1 / 8) 8 := by
    apply ContinuousOn.intervalIntegrable
    intro y hy
    rw [Set.uIcc_of_le (by norm_num : (1 / 8 : ℝ) ≤ 8)] at hy
    rw [Set.mem_Icc] at hy
    exact (hasDerivAt_cpow_F t (by linarith [hy.1])).continuousAt.continuousWithinAt
  have hv2' : IntervalIntegrable (fun y : ℝ => ((deriv (deriv bumpFn) y : ℝ) : ℂ))
      volume (1 / 8) 8 :=
    (Complex.continuous_ofReal.comp hcdd).intervalIntegrable (1 / 8) 8
  have h2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu2 hv2 hu2' hv2'
  simp only [deriv_bumpFn_eq_zero_of_gt (by norm_num : (4 : ℝ) < 8), Complex.ofReal_zero,
    mul_zero, sub_zero, zero_sub, deriv_bumpFn_eq_zero_of_lt (by norm_num : (1 / 8 : ℝ) < 1 / 4)]
    at h2
  have key1 : (∫ y in (1 / 8 : ℝ)..8, (y : ℂ) ^ (Complex.I * (t : ℂ)) * (bumpFn y : ℂ)) =
      -∫ y in (1 / 8 : ℝ)..8, (y : ℂ) ^ (Complex.I * (t : ℂ) + 1) / (Complex.I * (t : ℂ) + 1) *
          (((deriv bumpFn y : ℝ) : ℂ)) := by
    rw [h1]; simp
  rw [key1, h2]

/-- Norm bound on the integrated-by-parts expression. -/
lemma integral_norm_bound (t : ℝ) :
    ‖∫ y in (1 / 8 : ℝ)..8, (y : ℂ) ^ (Complex.I * (t : ℂ) + 2) /
        ((Complex.I * (t : ℂ) + 1) * (Complex.I * (t : ℂ) + 2)) *
          (((deriv (deriv bumpFn) y : ℝ) : ℂ))‖
      ≤ (64 * (∫ y in (1 / 8 : ℝ)..8, ‖(((deriv (deriv bumpFn) y : ℝ) : ℂ))‖) + 1) / (1 + t ^ 2) := by
  have hcdd : Continuous (deriv (deriv bumpFn)) := by
    have hC2' : ContDiff ℝ 1 (deriv bumpFn) := by
      simpa using ContDiff.iterate_deriv' (𝕜 := ℝ) 1 1 (bumpFn_contDiff 2)
    exact hC2'.continuous_deriv le_rfl
  have hψcont : ContinuousOn (fun y : ℝ => (((deriv (deriv bumpFn) y : ℝ) : ℂ)))
      (Set.uIcc (1 / 8) 8) :=
    (Complex.continuous_ofReal.comp hcdd).continuousOn
  have hGcont : ContinuousOn (fun y : ℝ => (y : ℂ) ^ (Complex.I * (t : ℂ) + 2) /
      ((Complex.I * (t : ℂ) + 1) * (Complex.I * (t : ℂ) + 2))) (Set.uIcc (1 / 8) 8) := by
    intro y hy
    rw [Set.uIcc_of_le (by norm_num : (1 / 8 : ℝ) ≤ 8)] at hy
    rw [Set.mem_Icc] at hy
    exact (hasDerivAt_cpow_G t (by linarith [hy.1])).continuousAt.continuousWithinAt
  have hf_int : IntervalIntegrable
      (fun y : ℝ => ‖(y : ℂ) ^ (Complex.I * (t : ℂ) + 2) /
        ((Complex.I * (t : ℂ) + 1) * (Complex.I * (t : ℂ) + 2))‖ *
          ‖(((deriv (deriv bumpFn) y : ℝ) : ℂ))‖) volume (1 / 8) 8 :=
    (hGcont.norm.mul hψcont.norm).intervalIntegrable
  have hg_int : IntervalIntegrable
      (fun y : ℝ => (64 / (1 + t ^ 2)) * ‖(((deriv (deriv bumpFn) y : ℝ) : ℂ))‖)
      volume (1 / 8) 8 :=
    (continuousOn_const.mul hψcont.norm).intervalIntegrable
  have hK : ∀ y ∈ Set.Icc (1 / 8 : ℝ) 8,
      ‖(y : ℂ) ^ (Complex.I * (t : ℂ) + 2) / ((Complex.I * (t : ℂ) + 1) * (Complex.I * (t : ℂ) + 2))‖
        ≤ 64 / (1 + t ^ 2) := by
    intro y hy
    have hypos : 0 < y := by linarith [hy.1]
    have hnum : ‖(y : ℂ) ^ (Complex.I * (t : ℂ) + 2)‖ = y ^ 2 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hypos]
      have hre : (Complex.I * (t : ℂ) + 2).re = 2 := by
        simp [Complex.mul_re, Complex.add_re]
      rw [hre, Real.rpow_two]
    have hc1 : (Complex.I * (t : ℂ) + 1) ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp [Complex.mul_re, Complex.add_re] at hre
    have hc2 : (Complex.I * (t : ℂ) + 2) ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp [Complex.mul_re, Complex.add_re] at hre
    have hdenpos : 0 < ‖(Complex.I * (t : ℂ) + 1) * (Complex.I * (t : ℂ) + 2)‖ :=
      norm_pos_iff.mpr (mul_ne_zero hc1 hc2)
    rw [norm_div, hnum]
    rw [div_le_div_iff₀ hdenpos (by positivity)]
    have hy2 : y ^ 2 ≤ 64 := by nlinarith [hy.1, hy.2]
    exact mul_le_mul hy2 (one_add_sq_le_norm t) (by positivity) (by norm_num)
  calc ‖∫ y in (1 / 8 : ℝ)..8, (y : ℂ) ^ (Complex.I * (t : ℂ) + 2) /
        ((Complex.I * (t : ℂ) + 1) * (Complex.I * (t : ℂ) + 2)) *
          (((deriv (deriv bumpFn) y : ℝ) : ℂ))‖
      ≤ ∫ y in (1 / 8 : ℝ)..8, ‖(y : ℂ) ^ (Complex.I * (t : ℂ) + 2) /
          ((Complex.I * (t : ℂ) + 1) * (Complex.I * (t : ℂ) + 2)) *
            (((deriv (deriv bumpFn) y : ℝ) : ℂ))‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ = ∫ y in (1 / 8 : ℝ)..8, ‖(y : ℂ) ^ (Complex.I * (t : ℂ) + 2) /
          ((Complex.I * (t : ℂ) + 1) * (Complex.I * (t : ℂ) + 2))‖ *
            ‖(((deriv (deriv bumpFn) y : ℝ) : ℂ))‖ := by
        apply intervalIntegral.integral_congr
        intro y hy
        exact norm_mul _ _
    _ ≤ ∫ y in (1 / 8 : ℝ)..8, (64 / (1 + t ^ 2)) * ‖(((deriv (deriv bumpFn) y : ℝ) : ℂ))‖ := by
        apply intervalIntegral.integral_mono_on (by norm_num) hf_int hg_int
        intro y hy
        exact mul_le_mul_of_nonneg_right (hK y hy) (norm_nonneg _)
    _ = (64 / (1 + t ^ 2)) * (∫ y in (1 / 8 : ℝ)..8, ‖(((deriv (deriv bumpFn) y : ℝ) : ℂ))‖) :=
        intervalIntegral.integral_const_mul _ _
    _ ≤ (64 * (∫ y in (1 / 8 : ℝ)..8, ‖(((deriv (deriv bumpFn) y : ℝ) : ℂ))‖) + 1) / (1 + t ^ 2) := by
        rw [div_mul_eq_mul_div]
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith

theorem smoothing_exists :
    ∃ (φ : ℝ → ℝ) (C : ℝ), 0 < C ∧ (∀ k : ℕ, ContDiff ℝ k φ) ∧
      (∀ y : ℝ, 0 ≤ φ y) ∧
      (∀ y ∈ Set.Icc (1 / 2 : ℝ) 2, φ y = 1) ∧
      (∀ y : ℝ, y ≤ 1 / 4 ∨ 4 ≤ y → φ y = 0) ∧
      (∀ t : ℝ, ‖∫ y in (1 / 4 : ℝ)..4, (y : ℂ) ^ (Complex.I * (t : ℂ)) * (φ y : ℂ)‖
        ≤ C / (1 + t ^ 2)) := by
  refine ⟨bumpFn, 64 * (∫ y in (1 / 8 : ℝ)..8, ‖(((deriv (deriv bumpFn) y : ℝ) : ℂ))‖) + 1,
    ?_, fun k => bumpFn_contDiff k, bumpFn_nonneg, bumpFn_eq_one, bumpFn_eq_zero, ?_⟩
  · have h : 0 ≤ ∫ y in (1 / 8 : ℝ)..8, ‖(((deriv (deriv bumpFn) y : ℝ) : ℂ))‖ :=
      intervalIntegral.integral_nonneg (by norm_num) (fun y _ => norm_nonneg _)
    linarith
  · intro t
    rw [integral_shift t, integral_ibp t]
    exact integral_norm_bound t

end Work.BMF
