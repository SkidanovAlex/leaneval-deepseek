import Mathlib
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_vertical_bound
import Submission.Commons.Analysis.SpecialFunctions.Trigonometric.arctan_le_self_of_nonneg

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Complex Filter
open scoped Real Topology BigOperators
set_option autoImplicit false
noncomputable section

namespace Commons.Analysis.SpecialFunctions.Gamma

/-! # Lower bound for the imaginary part of the digamma function

For `1/2 ≤ u` and `0 < v` we prove

  `π/2 - u/v - 1/2 ≤ Im ψ(u + i v)`.

The proof uses the Euler series for `ψ` available in the commons
(`digamma_eq_euler_sub_tsum`):

  `ψ(s) = -γ + ∑' n, (1/(n+1) - 1/(s+n))`,  valid for `Re s ≥ 1/4`.

Taking imaginary parts termwise (`Complex.im_tsum`) gives

  `Im ψ(u + i v) = ∑' n, v / ((u+n)^2 + v^2)`,

and each summand is the derivative of `x ↦ arctan ((u+x)/v)`.  Comparing the sum
with the integral `∫_0^∞ v / ((u+x)^2+v^2) dx = π/2 - arctan (u/v)`
(via the antitone sum/integral comparison `AntitoneOn.integral_le_sum_Ico` and the
limit `arctan → π/2`) yields `Im ψ(u+iv) ≥ π/2 - arctan(u/v) ≥ π/2 - u/v - 1/2`,
the last step being `arctan t ≤ t` for `t ≥ 0`. -/

/-! ## The imaginary part of the digamma series terms -/

/-- Imaginary part of `1/(u + i v + n)`. -/
lemma im_inv_shift (u v : ℝ) (n : ℕ) :
    ((((u : ℂ) + (v : ℂ) * Complex.I) + (n : ℂ))⁻¹).im = -v / ((u + (n : ℝ)) ^ 2 + v ^ 2) := by
  rw [Complex.inv_im, Complex.normSq_apply]
  have hre : (((u : ℂ) + (v : ℂ) * Complex.I) + (n : ℂ)).re = u + (n : ℝ) := by simp
  have him : (((u : ℂ) + (v : ℂ) * Complex.I) + (n : ℂ)).im = v := by simp
  rw [hre, him]
  congr 1
  ring

/-- Imaginary part of the Euler series term `1/(n+1) - 1/(u + i v + n)`. -/
lemma im_dgTermC_eq (u v : ℝ) (n : ℕ) :
    (dgTermC ((u : ℂ) + (v : ℂ) * Complex.I) n).im = v / ((u + (n : ℝ)) ^ 2 + v ^ 2) := by
  have h1 : (((n : ℂ) + 1)⁻¹).im = 0 := by
    rw [Complex.inv_im]
    simp [Complex.normSq_apply]
  rw [dgTermC, Complex.sub_im, h1, im_inv_shift]
  ring

/-! ## The integral of the kernel -/

/-- The kernel `x ↦ v / ((u+x)^2 + v^2)` is the derivative of `x ↦ arctan ((u+x)/v)`. -/
lemma hasDerivAt_arctan_kernel (u v x : ℝ) (hv : 0 < v) :
    HasDerivAt (fun y : ℝ => Real.arctan ((u + y) / v)) (v / ((u + x) ^ 2 + v ^ 2)) x := by
  have hvne : v ≠ 0 := ne_of_gt hv
  have h1 : HasDerivAt (fun y : ℝ => (u + y) / v) (1 / v) x :=
    ((hasDerivAt_id x).const_add u).div_const v
  have h2 : HasDerivAt (fun y : ℝ => Real.arctan ((u + y) / v))
      ((1 / (1 + ((u + x) / v) ^ 2)) * (1 / v)) x := by
    simpa only [Function.comp_def] using (Real.hasDerivAt_arctan ((u + x) / v)).comp x h1
  refine h2.congr_deriv ?_
  have h3 : (0 : ℝ) < (u + x) ^ 2 + v ^ 2 := by positivity
  have h4 : (0 : ℝ) < 1 + ((u + x) / v) ^ 2 := by positivity
  field_simp
  ring

/-- Integral of the kernel along any interval. -/
lemma integral_kernel (u v : ℝ) (hv : 0 < v) (a b : ℝ) :
    (∫ x in a..b, v / ((u + x) ^ 2 + v ^ 2)) =
      Real.arctan ((u + b) / v) - Real.arctan ((u + a) / v) := by
  have hcont : Continuous fun x : ℝ => v / ((u + x) ^ 2 + v ^ 2) :=
    continuous_const.div (by fun_prop) (fun x => by positivity)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_arctan_kernel u v x hv) (hcont.intervalIntegrable a b)]

/-! ## Monotonicity and summability of the kernel -/

/-- The kernel is antitone on `[0, c]` for `u > 0`, `v > 0`. -/
lemma antitoneOn_kernel (u v : ℝ) (hu : 0 < u) (hv : 0 < v) (c : ℝ) :
    AntitoneOn (fun x : ℝ => v / ((u + x) ^ 2 + v ^ 2)) (Set.Icc 0 c) := by
  intro x hx y hy hxy
  simp only [Set.mem_Icc] at hx hy
  have h0 : 0 ≤ u + x := by linarith [hx.1]
  have h1 : u + x ≤ u + y := by linarith
  have h2 : (u + x) ^ 2 ≤ (u + y) ^ 2 := pow_le_pow_left₀ h0 h1 2
  have h3 : (0 : ℝ) < (u + x) ^ 2 + v ^ 2 := by positivity
  have h4 : (u + x) ^ 2 + v ^ 2 ≤ (u + y) ^ 2 + v ^ 2 := by linarith
  exact div_le_div_of_nonneg_left hv.le h3 h4

/-- The kernel is summable for `1/2 ≤ u`, `v > 0`. -/
lemma summable_kernel (u v : ℝ) (hu1 : (1 : ℝ) / 2 ≤ u) (hv : 0 < v) :
    Summable (fun n : ℕ => v / ((u + (n : ℝ)) ^ 2 + v ^ 2)) := by
  have hbig : Summable (fun n : ℕ => (4 * v) * (((n : ℝ) + 1) ^ 2)⁻¹) :=
    summable_inv_sq_shift.mul_left (4 * v)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hbig
  have h1 : v / ((u + (n : ℝ)) ^ 2 + v ^ 2) ≤ v / ((u + (n : ℝ)) ^ 2) :=
    div_le_div_of_nonneg_left hv.le (by positivity) (by linarith [sq_nonneg v])
  have h2 : v / ((u + (n : ℝ)) ^ 2) ≤ v / ((((n : ℝ) + 1) / 2) ^ 2) := by
    apply div_le_div_of_nonneg_left hv.le (by positivity)
    have h3 : ((n : ℝ) + 1) / 2 ≤ u + (n : ℝ) := by linarith
    exact pow_le_pow_left₀ (by positivity) h3 2
  have h3 : v / ((((n : ℝ) + 1) / 2) ^ 2) = (4 * v) * (((n : ℝ) + 1) ^ 2)⁻¹ := by
    have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  calc v / ((u + (n : ℝ)) ^ 2 + v ^ 2) ≤ v / ((u + (n : ℝ)) ^ 2) := h1
    _ ≤ v / ((((n : ℝ) + 1) / 2) ^ 2) := h2
    _ = (4 * v) * (((n : ℝ) + 1) ^ 2)⁻¹ := h3

/-! ## The main estimate -/

/-- Euler-series representation of the imaginary part of `ψ(u + iv)`. -/
lemma im_digamma_eq_tsum (u v : ℝ) (hu1 : (1 : ℝ) / 2 ≤ u) :
    (Complex.digamma ((u : ℂ) + (v : ℂ) * Complex.I)).im =
      ∑' n : ℕ, v / ((u + (n : ℝ)) ^ 2 + v ^ 2) := by
  have hs4 : (1 : ℝ) / 4 ≤ (((u : ℂ) + (v : ℂ) * Complex.I)).re := by
    simp
    linarith
  have hsumC : Summable (fun n : ℕ => dgTermC ((u : ℂ) + (v : ℂ) * Complex.I) n) :=
    Summable.of_norm (summable_dgTerm_norm _ hs4)
  rw [digamma_eq_euler_sub_tsum _ hs4, Complex.add_im, Complex.neg_im, Complex.ofReal_im,
    Complex.im_tsum hsumC]
  simp only [neg_zero, zero_add]
  exact tsum_congr (fun n => im_dgTermC_eq u v n)

theorem digamma_im_lower (u v : ℝ) (hu1 : (1 : ℝ) / 2 ≤ u) (hu2 : u ≤ 8) (hv : 0 < v) :
    Real.pi / 2 - u / v - 1 / 2 ≤ (Complex.digamma ((u : ℂ) + (v : ℂ) * Complex.I)).im := by
  have _hu2 : u ≤ 8 := hu2
  have hu : 0 < u := by linarith
  have him := im_digamma_eq_tsum u v hu1
  have hbound : Real.pi / 2 - Real.arctan (u / v) ≤
      ∑' n : ℕ, v / ((u + (n : ℝ)) ^ 2 + v ^ 2) := by
    have hN : ∀ N : ℕ, Real.arctan ((u + (N : ℝ)) / v) - Real.arctan (u / v) ≤
        ∑' n : ℕ, v / ((u + (n : ℝ)) ^ 2 + v ^ 2) := by
      intro N
      have hanti : AntitoneOn (fun x : ℝ => v / ((u + x) ^ 2 + v ^ 2))
          (Set.Icc (↑(0 : ℕ) : ℝ) (↑N : ℝ)) := by
        simpa using antitoneOn_kernel u v hu hv (N : ℝ)
      have h := AntitoneOn.integral_le_sum_Ico
        (f := fun x : ℝ => v / ((u + x) ^ 2 + v ^ 2)) (a := 0) (b := N) (Nat.zero_le N) hanti
      rw [show (↑(0 : ℕ) : ℝ) = 0 from Nat.cast_zero] at h
      rw [integral_kernel u v hv 0 (N : ℝ)] at h
      simp only [add_zero] at h
      have hsum_le : (∑ x ∈ Finset.Ico 0 N, v / ((u + (x : ℝ)) ^ 2 + v ^ 2)) ≤
          ∑' n : ℕ, v / ((u + (n : ℝ)) ^ 2 + v ^ 2) :=
        (summable_kernel u v hu1 hv).sum_le_tsum (Finset.Ico 0 N) (fun i _ => by positivity)
      linarith
    have harg : Tendsto (fun N : ℕ => (u + (N : ℝ)) / v) atTop atTop :=
      (tendsto_atTop_add_const_left atTop u tendsto_natCast_atTop_atTop).atTop_div_const hv
    have harc : Tendsto (fun N : ℕ => Real.arctan ((u + (N : ℝ)) / v)) atTop (𝓝 (Real.pi / 2)) :=
      (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp harg
    have hlim : Tendsto (fun N : ℕ => Real.arctan ((u + (N : ℝ)) / v) - Real.arctan (u / v))
        atTop (𝓝 (Real.pi / 2 - Real.arctan (u / v))) :=
      harc.sub tendsto_const_nhds
    exact le_of_tendsto hlim (Eventually.of_forall hN)
  have harctan : Real.arctan (u / v) ≤ u / v + 1 / 2 := by
    have h :=
      Commons.Analysis.SpecialFunctions.Trigonometric.arctan_le_self_of_nonneg (x := u / v)
        (by positivity)
    linarith
  calc Real.pi / 2 - u / v - 1 / 2 ≤ Real.pi / 2 - Real.arctan (u / v) := by linarith
    _ ≤ ∑' n : ℕ, v / ((u + (n : ℝ)) ^ 2 + v ^ 2) := hbound
    _ = (Complex.digamma ((u : ℂ) + (v : ℂ) * Complex.I)).im := him.symm

end Commons.Analysis.SpecialFunctions.Gamma
