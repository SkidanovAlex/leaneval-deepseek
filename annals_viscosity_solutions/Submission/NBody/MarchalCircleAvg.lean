import Submission.NBody.MarchalBumpAction
import Mathlib

/-!
# Averaging `1/‖u + d e_θ‖` over a circle: reduction to the planar model

This is the (elementary) reduction step of Ferrario--Terracini's averaging theorem `theo:aa` that
is needed for the *common direction* problem of the symmetric-bump argument (see
`Submission/ROADMAP.md`, SESSION 32).

Given `u : E`, a radius `d ≥ 0` and an orthonormal pair `e, f` spanning a 2-plane `P ⊂ E`, write
`e_θ = cos θ • e + sin θ • f` and

  `Φ(u, d) := (1/2π) ∫_θ ‖u + d • e_θ‖⁻¹ dθ` .

The main result, `circle_avg_inv_norm_le`, is

  `Φ(u, d) ≤ Φ(‖u‖ • e, d)`   whenever `‖u‖ ≠ d`,

i.e. **the circle average is maximal when `u` lies in the plane and has maximal norm**.  This is the
pointwise ("convexity") replacement of FT's `aa:nr1`, and it reduces the general-dimension averaging
estimate to the planar one, which is already available in the commons
(`Commons.Analysis.Integral.average_inv_parabolic_circle_neg`).

The proof of `circle_avg_inv_norm_le` is:

* `‖u + d e_θ‖ ≥ ‖u_P + d e_θ‖` where `u_P` is the orthogonal projection of `u` on `P` (a pointwise
  inequality, `circle_avg_inv_norm_pointwise`);
* rotating inside `P` (`circle_avg_inv_norm_rotation`), the average depends only on `‖u_P‖`;
* if `a ≤ b` and `2 b d < b² + d²`, symmetrising `θ ↦ θ + π` turns both averages into
  `∫_θ h(2 a d cos θ) dθ` resp. `∫_θ h(2 b d cos θ) dθ` with
  `h(y) = ½((A + y)^{-1/2} + (A - y)^{-1/2})`, `A = b² + d²`, and `h` is increasing on `[0, A)`
  because it is half the sum of a convex function and its reflection
  (`half_sum_rpow_neg_monoOn`).

All results in this file are fully proved.
-/

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace MeasureTheory
open scoped BigOperators Topology ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace Submission.NBody

/-! ## The elementary monotonicity of `y ↦ ½((A+y)^{-p} + (A-y)^{-p})` -/

/-- The derivative of `y ↦ (A + y) ^ (-p)`. -/
lemma hasDerivAt_add_rpow_neg {A p y : ℝ} (hA : 0 < A) (hy : |y| < A) :
    HasDerivAt (fun y : ℝ => (A + y) ^ (-p)) ((-p) * (A + y) ^ (-p - 1)) y := by
  have h : (0:ℝ) < A + y := by rw [abs_lt] at hy; linarith [hy.1]
  have h1 : HasDerivAt (fun y : ℝ => A + y) 1 y := (hasDerivAt_id y).const_add A
  have h2 := h1.rpow_const (p := -p) (Or.inl h.ne')
  have hval : (1 : ℝ) * (-p) * (A + y) ^ (-p - 1) = (-p) * (A + y) ^ (-p - 1) := by ring
  rw [hval] at h2
  exact h2

/-- The derivative of `y ↦ (A - y) ^ (-p)`. -/
lemma hasDerivAt_sub_rpow_neg {A p y : ℝ} (hA : 0 < A) (hy : |y| < A) :
    HasDerivAt (fun y : ℝ => (A - y) ^ (-p)) (p * (A - y) ^ (-p - 1)) y := by
  have h : (0:ℝ) < A - y := by rw [abs_lt] at hy; linarith [hy.2]
  have h1 : HasDerivAt (fun y : ℝ => A - y) (-1) y := (hasDerivAt_id y).const_sub A
  have h2 := h1.rpow_const (p := -p) (Or.inl h.ne')
  have hval : (-1 : ℝ) * (-p) * (A - y) ^ (-p - 1) = p * (A - y) ^ (-p - 1) := by ring
  rw [hval] at h2
  exact h2

/-- **The elementary monotonicity.**  For `A > 0` and `p > 0` the function
`y ↦ ½((A + y)^{-p} + (A - y)^{-p})` is increasing on `[0, A)`. -/
theorem half_sum_rpow_neg_monoOn {A p : ℝ} (hA : 0 < A) (hp : 0 < p) :
    MonotoneOn (fun y : ℝ => (1/2) * ((A + y) ^ (-p) + (A - y) ^ (-p))) (Set.Ico 0 A) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ico 0 A) ?_ ?_ ?_
  · -- continuity on `Ico 0 A`
    have hcont1 : ContinuousOn (fun y : ℝ => (A + y) ^ (-p)) (Set.Ico 0 A) := by
      refine ContinuousOn.rpow (continuousOn_const.add continuousOn_id) continuousOn_const ?_
      intro y hy; left; have := hy.1; linarith
    have hcont2 : ContinuousOn (fun y : ℝ => (A - y) ^ (-p)) (Set.Ico 0 A) := by
      refine ContinuousOn.rpow (continuousOn_const.sub continuousOn_id) continuousOn_const ?_
      intro y hy; left; have := hy.2; linarith
    exact continuousOn_const.mul (hcont1.add hcont2)
  · -- differentiability on the interior `Ioo 0 A`
    intro y hy
    rw [interior_Ico] at hy
    have hy' : |y| < A := by
      rw [abs_lt]; exact ⟨by linarith [hy.1], hy.2⟩
    have hsum : HasDerivAt (fun y : ℝ => (A + y) ^ (-p) + (A - y) ^ (-p))
        ((-p) * (A + y) ^ (-p - 1) + p * (A - y) ^ (-p - 1)) y :=
      (hasDerivAt_add_rpow_neg hA hy').add (hasDerivAt_sub_rpow_neg hA hy')
    exact (hsum.const_mul (1/2)).differentiableAt.differentiableWithinAt
  · -- nonneg derivative on the interior
    intro y hy
    rw [interior_Ico] at hy
    have hy' : |y| < A := by
      rw [abs_lt]; exact ⟨by linarith [hy.1], hy.2⟩
    have hpos2 : (0:ℝ) < A - y := by rw [abs_lt] at hy'; linarith [hy'.2]
    have hderiv : deriv (fun y : ℝ => (1/2) * ((A + y) ^ (-p) + (A - y) ^ (-p))) y
        = (1/2) * ((-p) * (A + y) ^ (-p - 1) + p * (A - y) ^ (-p - 1)) := by
      have hsum : HasDerivAt (fun y : ℝ => (A + y) ^ (-p) + (A - y) ^ (-p))
          ((-p) * (A + y) ^ (-p - 1) + p * (A - y) ^ (-p - 1)) y :=
        (hasDerivAt_add_rpow_neg hA hy').add (hasDerivAt_sub_rpow_neg hA hy')
      rw [(hsum.const_mul (1/2)).deriv]
    rw [hderiv]
    refine mul_nonneg (by norm_num) ?_
    have hle : A - y ≤ A + y := by linarith [hy.1]
    have hcmp : (A + y) ^ (-p - 1) ≤ (A - y) ^ (-p - 1) :=
      Real.rpow_le_rpow_of_nonpos hpos2 hle (by linarith)
    have h3 : -p * (A + y) ^ (-p - 1) + p * (A - y) ^ (-p - 1)
        = p * ((A - y) ^ (-p - 1) - (A + y) ^ (-p - 1)) := by ring
    rw [h3]
    exact mul_nonneg hp.le (sub_nonneg.mpr hcmp)



variable {d : ℝ}

/-- The phase shift in the circle parametrisation: `∫ θ, F (θ - φ) = ∫ θ, F θ` for a `2π`-periodic
`F`. -/
lemma integral_shift_periodic {F : ℝ → ℝ} (hF : Function.Periodic F (2 * Real.pi)) (φ : ℝ) :
    ∫ θ in (0)..(2 * Real.pi), F (θ - φ) = ∫ θ in (0)..(2 * Real.pi), F θ := by
  rw [intervalIntegral.integral_comp_sub_right F φ]
  have h2 : (0:ℝ) - φ = -φ := by ring
  have h3 : 2 * Real.pi - φ = -φ + 2 * Real.pi := by ring
  rw [h2, h3, hF.intervalIntegral_add_eq (-φ) 0]
  ring_nf



/-- The unit vector of the circle parametrisation. -/
noncomputable def circVec (e f : E) (θ : ℝ) : E := Real.cos θ • e + Real.sin θ • f

@[simp] lemma circVec_add_pi (e f : E) (θ : ℝ) : circVec e f (θ + Real.pi) = -circVec e f θ := by
  simp only [circVec, Real.cos_add_pi, Real.sin_add_pi, neg_smul]
  abel

lemma norm_circVec {e f : E} (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : inner ℝ e f = 0) (θ : ℝ) :
    ‖circVec e f θ‖ = 1 := by
  have h2 : ‖circVec e f θ‖ ^ 2 = 1 := by
    have hcv : circVec e f θ = Real.cos θ • e + Real.sin θ • f := rfl
    rw [hcv, norm_add_sq_real]
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, he, hf]
    rw [mul_one, mul_one, sq_abs, sq_abs]
    rw [real_inner_smul_left, real_inner_smul_right, hef]
    nlinarith [Real.cos_sq_add_sin_sq θ]
  nlinarith [norm_nonneg (circVec e f θ)]

lemma inner_circVec (u : E) (e f : E) (θ : ℝ) :
    inner ℝ u (circVec e f θ)
      = inner ℝ u e * Real.cos θ + inner ℝ u f * Real.sin θ := by
  simp only [circVec, inner_add_right, inner_smul_right]
  ring

lemma norm_add_smul_circVec_sq {d : ℝ} (hd : 0 ≤ d) {e f : E} (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hef : inner ℝ e f = 0) (u : E) (θ : ℝ) :
    ‖u + d • circVec e f θ‖ ^ 2
      = ‖u‖ ^ 2 + d ^ 2 + 2 * d * inner ℝ u (circVec e f θ) := by
  rw [norm_add_sq_real, real_inner_smul_right, norm_smul, norm_circVec he hf hef θ,
    Real.norm_of_nonneg hd]
  ring



lemma circVec_add_two_pi (e f : E) (θ : ℝ) :
    circVec e f (θ + 2 * Real.pi) = circVec e f θ := by
  simp only [circVec, Real.cos_add_two_pi, Real.sin_add_two_pi]

lemma norm_sub_smul_circVec_sq {d : ℝ} (hd : 0 ≤ d) {e f : E} (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hef : inner ℝ e f = 0) (u : E) (θ : ℝ) :
    ‖u - d • circVec e f θ‖ ^ 2
      = ‖u‖ ^ 2 + d ^ 2 - 2 * d * inner ℝ u (circVec e f θ) := by
  have h := norm_add_smul_circVec_sq hd he hf hef u (θ + Real.pi)
  rw [circVec_add_pi, smul_neg, ← sub_eq_add_neg] at h
  have h2 : inner ℝ u (-circVec e f θ) = -inner ℝ u (circVec e f θ) := inner_neg_right ..
  rw [h2] at h
  rw [h]; ring

/-- `‖w‖⁻¹ = X ^ (-1/2)` when `‖w‖² = X ≥ 0`. -/
lemma inv_norm_eq_rpow_neg_half {w : E} {X : ℝ} (hX : 0 ≤ X) (h : ‖w‖ ^ 2 = X) :
    ‖w‖⁻¹ = X ^ (-(1:ℝ)/2) := by
  have hw : ‖w‖ = Real.sqrt X := by
    rw [← h, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg w)]
  rw [hw, Real.sqrt_eq_rpow, ← Real.rpow_neg hX (1/2)]
  norm_num

/-- The circle-parametrisation vector is continuous. -/
lemma continuous_circVec (e f : E) : Continuous (circVec e f) :=
  (Real.continuous_cos.smul continuous_const).add (Real.continuous_sin.smul continuous_const)

/-- The lower bound on `‖u + d e_θ‖` used throughout: `|‖u‖ - d| ≤ ‖u + d e_θ‖`. -/
lemma abs_sub_le_norm_add_smul_circVec {d : ℝ} (hd : 0 ≤ d) {e f : E} (he : ‖e‖ = 1)
    (hf : ‖f‖ = 1) (hef : inner ℝ e f = 0) (u : E) (θ : ℝ) :
    |‖u‖ - d| ≤ ‖u + d • circVec e f θ‖ := by
  have hnorm : ‖d • circVec e f θ‖ = d := by
    rw [norm_smul, norm_circVec he hf hef, mul_one, Real.norm_of_nonneg hd]
  have h1 : ‖u‖ - d ≤ ‖u + d • circVec e f θ‖ := by
    have h := norm_add_le (u + d • circVec e f θ) (-(d • circVec e f θ))
    have h2 : u + d • circVec e f θ + -(d • circVec e f θ) = u := by abel
    rw [h2, norm_neg, hnorm] at h
    linarith
  have h2 : d - ‖u‖ ≤ ‖u + d • circVec e f θ‖ := by
    have h := norm_sub_le (u + d • circVec e f θ) u
    rw [add_sub_cancel_left, hnorm] at h
    linarith
  exact (abs_sub_le_iff.mpr ⟨h1, h2⟩)

/-- **Symmetrisation identity.**  The circle average of `1/‖u + d e_θ‖` equals the circle average of
the symmetrised (half-sum) integrand. -/
theorem integral_inv_norm_eq_halfsum {d : ℝ} (hd : 0 ≤ d) {e f : E} (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hef : inner ℝ e f = 0) (u : E) (hne : ‖u‖ ≠ d) :
    ∫ θ in (0)..(2*Real.pi), (‖u + d • circVec e f θ‖)⁻¹
      = ∫ θ in (0)..(2*Real.pi), (1/2) *
          (((‖u‖ ^ 2 + d ^ 2) + 2 * d * inner ℝ u (circVec e f θ)) ^ (-(1:ℝ)/2)
         + ((‖u‖ ^ 2 + d ^ 2) - 2 * d * inner ℝ u (circVec e f θ)) ^ (-(1:ℝ)/2)) := by
  have hpos : 0 < (‖u‖ - d) ^ 2 := by
    have hne' : ‖u‖ - d ≠ 0 := sub_ne_zero.mpr hne
    positivity
  have hcs : ∀ θ, -‖u‖ ≤ inner ℝ u (circVec e f θ) ∧ inner ℝ u (circVec e f θ) ≤ ‖u‖ := by
    intro θ
    have h := abs_real_inner_le_norm u (circVec e f θ)
    rw [norm_circVec he hf hef θ, mul_one] at h
    exact abs_le.mp h
  set B : ℝ → ℝ := fun θ => (‖u + d • circVec e f θ‖)⁻¹ with hB
  set G : ℝ → ℝ := fun θ => (1/2) *
      (((‖u‖ ^ 2 + d ^ 2) + 2 * d * inner ℝ u (circVec e f θ)) ^ (-(1:ℝ)/2)
     + ((‖u‖ ^ 2 + d ^ 2) - 2 * d * inner ℝ u (circVec e f θ)) ^ (-(1:ℝ)/2)) with hG
  have hBper : Function.Periodic B (2*Real.pi) := fun θ => by
    simp only [hB, circVec_add_two_pi]
  have hBcont : Continuous B := by
    have h1 : Continuous (fun θ : ℝ => ‖u + d • circVec e f θ‖) :=
      continuous_norm.comp (continuous_const.add (continuous_const.smul (continuous_circVec e f)))
    exact h1.inv₀ fun θ => ne_of_gt (lt_of_lt_of_le (abs_pos.mpr (sub_ne_zero.mpr hne))
      (abs_sub_le_norm_add_smul_circVec hd he hf hef u θ))
  have hBint : IntervalIntegrable B volume (0:ℝ) (2*Real.pi) := hBcont.intervalIntegrable _ _
  have hBint' : IntervalIntegrable (fun θ => B (θ + Real.pi)) volume (0:ℝ) (2*Real.pi) :=
    (hBcont.comp (continuous_id.add continuous_const)).intervalIntegrable _ _
  have hshift : ∫ θ in (0)..(2*Real.pi), B (θ + Real.pi) = ∫ θ in (0)..(2*Real.pi), B θ := by
    have h := integral_shift_periodic hBper (-Real.pi)
    simpa using h
  have hpt : ∀ θ, (1/2) * (B θ + B (θ + Real.pi)) = G θ := by
    intro θ
    obtain ⟨hc1, hc2⟩ := hcs θ
    have hA1 : (0:ℝ) ≤ (‖u‖ ^ 2 + d ^ 2) + 2 * d * inner ℝ u (circVec e f θ) := by nlinarith
    have hA2 : (0:ℝ) ≤ (‖u‖ ^ 2 + d ^ 2) - 2 * d * inner ℝ u (circVec e f θ) := by nlinarith
    have hh1 : B θ = ((‖u‖ ^ 2 + d ^ 2) + 2 * d * inner ℝ u (circVec e f θ)) ^ (-(1:ℝ)/2) := by
      simp only [hB]
      exact inv_norm_eq_rpow_neg_half hA1 (norm_add_smul_circVec_sq hd he hf hef u θ)
    have hh2 : B (θ + Real.pi)
        = ((‖u‖ ^ 2 + d ^ 2) - 2 * d * inner ℝ u (circVec e f θ)) ^ (-(1:ℝ)/2) := by
      have hw := inv_norm_eq_rpow_neg_half hA2 (norm_sub_smul_circVec_sq hd he hf hef u θ)
      have h2 : B (θ + Real.pi) = ‖u - d • circVec e f θ‖⁻¹ := by
        simp only [hB, circVec_add_pi, smul_neg, sub_eq_add_neg]
      rw [h2, hw]
    rw [hh1, hh2, hG]
  have hmain : ∫ θ in (0)..(2*Real.pi), (B θ + B (θ + Real.pi))
      = 2 * ∫ θ in (0)..(2*Real.pi), B θ := by
    rw [intervalIntegral.integral_add hBint hBint', hshift]; ring
  have hmain2 : ∫ θ in (0)..(2*Real.pi), (B θ + B (θ + Real.pi))
      = 2 * ∫ θ in (0)..(2*Real.pi), G θ := by
    rw [show (fun θ => B θ + B (θ + Real.pi)) = fun θ => 2 * G θ from
        funext fun θ => by rw [← hpt θ]; ring]
    exact intervalIntegral.integral_const_mul 2 G
  rw [hmain2] at hmain
  linarith



/-- **Polar form of a vector in `ℝ²`.**  For any `α β : ℝ` there is `φ` with
`α = √(α²+β²) cos φ` and `β = √(α²+β²) sin φ`. -/
lemma exists_cos_sin_polar (α β : ℝ) :
    ∃ φ : ℝ, α = Real.sqrt (α ^ 2 + β ^ 2) * Real.cos φ ∧
      β = Real.sqrt (α ^ 2 + β ^ 2) * Real.sin φ := by
  set z : ℂ := (α : ℂ) + (β : ℂ) * Complex.I with hz
  have hre : z.re = α := by simp [hz]
  have him : z.im = β := by simp [hz]
  have hnorm : ‖z‖ = Real.sqrt (α ^ 2 + β ^ 2) := by
    have h2 : ‖z‖ ^ 2 = α ^ 2 + β ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, hre, him]; ring
    have h3 : Real.sqrt (α ^ 2 + β ^ 2) ^ 2 = α ^ 2 + β ^ 2 :=
      Real.sq_sqrt (by positivity)
    nlinarith [norm_nonneg z, Real.sqrt_nonneg (α ^ 2 + β ^ 2)]
  by_cases hz0 : z = 0
  · have hα : α = 0 := by rw [← hre, hz0]; rfl
    have hβ : β = 0 := by rw [← him, hz0]; rfl
    refine ⟨0, ?_, ?_⟩
    · rw [hα, hβ]; simp
    · rw [hα, hβ]; simp
  · have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    refine ⟨z.arg, ?_, ?_⟩
    · rw [Complex.cos_arg hz0, ← hnorm, hre]
      exact (mul_div_cancel₀ _ (ne_of_gt hzpos)).symm
    · rw [Complex.sin_arg z, ← hnorm, him]
      exact (mul_div_cancel₀ _ (ne_of_gt hzpos)).symm



/-- Rotating the argument of a circle integral: `α cos θ + β sin θ` can be replaced by
`√(α²+β²) cos θ`. -/
lemma integral_comp_cos_angle {H : ℝ → ℝ} (α β : ℝ) :
    ∫ θ in (0)..(2*Real.pi), H (α * Real.cos θ + β * Real.sin θ)
      = ∫ θ in (0)..(2*Real.pi), H (Real.sqrt (α ^ 2 + β ^ 2) * Real.cos θ) := by
  obtain ⟨φ, hcos, hsin⟩ := exists_cos_sin_polar α β
  have hpt : ∀ θ, α * Real.cos θ + β * Real.sin θ
      = Real.sqrt (α ^ 2 + β ^ 2) * Real.cos (θ - φ) := by
    intro θ
    have hR : Real.sqrt (α ^ 2 + β ^ 2) * Real.cos (θ - φ)
        = Real.sqrt (α ^ 2 + β ^ 2) * Real.cos φ * Real.cos θ
          + Real.sqrt (α ^ 2 + β ^ 2) * Real.sin φ * Real.sin θ := by
      rw [Real.cos_sub]; ring
    rw [hR, ← hcos, ← hsin]
  have hper : Function.Periodic (fun θ => H (Real.sqrt (α ^ 2 + β ^ 2) * Real.cos θ))
      (2 * Real.pi) := fun θ => by simp only [Real.cos_add_two_pi]
  rw [show (fun θ => H (α * Real.cos θ + β * Real.sin θ))
      = fun θ => H (Real.sqrt (α ^ 2 + β ^ 2) * Real.cos (θ - φ)) from
        funext fun θ => by rw [hpt θ]]
  exact integral_shift_periodic hper φ

/-- Bessel: `√(⟪u,e⟫² + ⟪u,f⟫²) ≤ ‖u‖` for an orthonormal pair `e, f`. -/
lemma sqrt_inner_sq_add_le_norm {e f : E} (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hef : inner ℝ e f = 0) (u : E) :
    Real.sqrt ((inner ℝ u e) ^ 2 + (inner ℝ u f) ^ 2) ≤ ‖u‖ := by
  set w : E := inner ℝ u e • e + inner ℝ u f • f with hw
  have hw2 : ‖w‖ ^ 2 = (inner ℝ u e) ^ 2 + (inner ℝ u f) ^ 2 := by
    rw [hw, norm_add_sq_real]
    simp only [norm_smul, he, hf, mul_one, Real.norm_eq_abs, sq_abs, real_inner_smul_left,
      real_inner_smul_right, hef, mul_zero, add_zero]
  have hinner : inner ℝ u w = (inner ℝ u e) ^ 2 + (inner ℝ u f) ^ 2 := by
    rw [hw, inner_add_right, inner_smul_right, inner_smul_right]
    ring
  have hcs : ‖w‖ ^ 2 ≤ ‖u‖ * ‖w‖ := by
    rw [hw2, ← hinner]
    exact (le_abs_self _).trans (abs_real_inner_le_norm u w)
  have hwle : ‖w‖ ≤ ‖u‖ := by nlinarith [norm_nonneg w, norm_nonneg u, hcs]
  calc Real.sqrt ((inner ℝ u e) ^ 2 + (inner ℝ u f) ^ 2)
      = Real.sqrt (‖w‖ ^ 2) := by rw [hw2]
    _ = ‖w‖ := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg w)]
    _ ≤ ‖u‖ := hwle



/-- `|c * (a * x)| = c * (a * |x|)` for `c, a ≥ 0`. -/
lemma abs_mul_mul_abs {c a x : ℝ} (hc : 0 ≤ c) (ha : 0 ≤ a) :
    |c * (a * x)| = c * (a * |x|) := by
  rw [abs_mul, abs_of_nonneg hc, abs_mul, abs_of_nonneg ha]

/-- **The main reduction.**  The circle average of `1/‖u + d e_θ‖` is at most the circle average
computed at the vector `‖u‖ • e` (same norm, lying in the plane).  This reduces the general
averaging estimate to the planar model. -/
theorem circle_avg_inv_norm_le {d : ℝ} (hd : 0 ≤ d) {e f : E} (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hef : inner ℝ e f = 0) (u : E) (hne : ‖u‖ ≠ d) :
    (1 / (2 * Real.pi)) * ∫ θ in (0)..(2 * Real.pi), (‖u + d • circVec e f θ‖)⁻¹
      ≤ (1 / (2 * Real.pi)) * ∫ θ in (0)..(2 * Real.pi),
          (‖(‖u‖ : ℝ) • e + d • circVec e f θ‖)⁻¹ := by
  set a : ℝ := Real.sqrt ((inner ℝ u e) ^ 2 + (inner ℝ u f) ^ 2) with hadef
  set b : ℝ := ‖u‖ with hbdef
  set A : ℝ := b ^ 2 + d ^ 2 with hAdef
  have hb0 : 0 ≤ b := by rw [hbdef]; exact norm_nonneg u
  have ha0 : 0 ≤ a := by rw [hadef]; exact Real.sqrt_nonneg _
  have hab : a ≤ b := by rw [hadef, hbdef]; exact sqrt_inner_sq_add_le_norm he hf hef u
  have hbd : b ≠ d := by rw [hbdef]; exact hne
  have hApos : 0 < A := by
    rw [hAdef]
    rcases eq_or_lt_of_le hb0 with h | h
    · have hd0 : d ≠ 0 := fun hh => hbd (by rw [h.symm, hh])
      nlinarith [sq_nonneg b, sq_pos_of_ne_zero hd0]
    · nlinarith [sq_nonneg d, sq_pos_of_ne_zero (ne_of_gt h)]
  -- the two integrands are bounded below, hence the bases are bounded away from `0`
  have hbase_lo : ∀ θ : ℝ, (b - d) ^ 2 ≤ A + 2 * d * (a * Real.cos θ) := by
    intro θ
    rw [hAdef]
    have h1 : -b ≤ a * Real.cos θ := by nlinarith [Real.neg_one_le_cos θ, ha0, hab]
    have h2 : a * Real.cos θ ≤ b := by nlinarith [Real.cos_le_one θ, ha0, hab]
    nlinarith
  have hbase_hi : ∀ θ : ℝ, (b - d) ^ 2 ≤ A - 2 * d * (a * Real.cos θ) := by
    intro θ
    rw [hAdef]
    have h1 : -b ≤ a * Real.cos θ := by nlinarith [Real.neg_one_le_cos θ, ha0, hab]
    have h2 : a * Real.cos θ ≤ b := by nlinarith [Real.cos_le_one θ, ha0, hab]
    nlinarith
  have hbd2 : 0 < (b - d) ^ 2 := by
    rcases lt_trichotomy b d with h | h | h
    · nlinarith
    · exact absurd h hbd
    · nlinarith
  -- integrability of the two integrands
  have hcont1 : Continuous (fun θ : ℝ => (A + 2 * d * (a * Real.cos θ)) ^ (-(1:ℝ)/2)) := by
    refine Continuous.rpow_const (by fun_prop) fun θ => Or.inl ?_
    exact ne_of_gt (lt_of_lt_of_le hbd2 (hbase_lo θ))
  have hcont2 : Continuous (fun θ : ℝ => (A - 2 * d * (a * Real.cos θ)) ^ (-(1:ℝ)/2)) := by
    refine Continuous.rpow_const (by fun_prop) fun θ => Or.inl ?_
    exact ne_of_gt (lt_of_lt_of_le hbd2 (hbase_hi θ))
  have hcont3 : Continuous (fun θ : ℝ => (A + 2 * d * (b * Real.cos θ)) ^ (-(1:ℝ)/2)) := by
    refine Continuous.rpow_const (by fun_prop) fun θ => Or.inl ?_
    have h1 : -b ≤ b * Real.cos θ := by nlinarith [Real.neg_one_le_cos θ, hb0]
    have h2 : b * Real.cos θ ≤ b := by nlinarith [Real.cos_le_one θ, hb0]
    have h3 : (b - d) ^ 2 ≤ A + 2 * d * (b * Real.cos θ) := by rw [hAdef]; nlinarith
    exact ne_of_gt (lt_of_lt_of_le hbd2 h3)
  have hcont4 : Continuous (fun θ : ℝ => (A - 2 * d * (b * Real.cos θ)) ^ (-(1:ℝ)/2)) := by
    refine Continuous.rpow_const (by fun_prop) fun θ => Or.inl ?_
    have h1 : -b ≤ b * Real.cos θ := by nlinarith [Real.neg_one_le_cos θ, hb0]
    have h2 : b * Real.cos θ ≤ b := by nlinarith [Real.cos_le_one θ, hb0]
    have h3 : (b - d) ^ 2 ≤ A - 2 * d * (b * Real.cos θ) := by rw [hAdef]; nlinarith
    exact ne_of_gt (lt_of_lt_of_le hbd2 h3)
  have hInta : IntervalIntegrable (fun θ : ℝ => (1/2) *
      ((A + 2 * d * (a * Real.cos θ)) ^ (-(1:ℝ)/2)
        + (A - 2 * d * (a * Real.cos θ)) ^ (-(1:ℝ)/2))) volume (0:ℝ) (2*Real.pi) :=
    ((continuous_const.mul (hcont1.add hcont2))).intervalIntegrable _ _
  have hIntb : IntervalIntegrable (fun θ : ℝ => (1/2) *
      ((A + 2 * d * (b * Real.cos θ)) ^ (-(1:ℝ)/2)
        + (A - 2 * d * (b * Real.cos θ)) ^ (-(1:ℝ)/2))) volume (0:ℝ) (2*Real.pi) :=
    ((continuous_const.mul (hcont3.add hcont4))).intervalIntegrable _ _
  -- the identity rewriting the left-hand side
  have hL : ∫ θ in (0)..(2 * Real.pi), (‖u + d • circVec e f θ‖)⁻¹
      = ∫ θ in (0)..(2 * Real.pi), (1/2) *
          ((A + 2 * d * (a * Real.cos θ)) ^ (-(1:ℝ)/2)
            + (A - 2 * d * (a * Real.cos θ)) ^ (-(1:ℝ)/2)) := by
    rw [integral_inv_norm_eq_halfsum hd he hf hef u hne]
    simp only [inner_circVec]
    rw [hAdef, hadef]
    exact integral_comp_cos_angle (H := fun y => (1/2) *
      (((‖u‖ ^ 2 + d ^ 2) + 2 * d * y) ^ (-(1:ℝ)/2)
        + ((‖u‖ ^ 2 + d ^ 2) - 2 * d * y) ^ (-(1:ℝ)/2))) (inner ℝ u e) (inner ℝ u f)
  -- the identity rewriting the right-hand side
  have hbne : ‖(b : ℝ) • e‖ ≠ d := by rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_nonneg hb0, hbdef]; exact hne
  have hR : ∫ θ in (0)..(2 * Real.pi), (‖(‖u‖ : ℝ) • e + d • circVec e f θ‖)⁻¹
      = ∫ θ in (0)..(2 * Real.pi), (1/2) *
          ((A + 2 * d * (b * Real.cos θ)) ^ (-(1:ℝ)/2)
            + (A - 2 * d * (b * Real.cos θ)) ^ (-(1:ℝ)/2)) := by
    have h1 : ‖(b : ℝ) • e‖ = b := by
      rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_nonneg hb0]
    have h2 : (inner ℝ ((b : ℝ) • e) e) = b := by
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq, he]; ring
    have h3 : (inner ℝ ((b : ℝ) • e) f) = 0 := by
      rw [real_inner_smul_left, hef, mul_zero]
    have h := integral_inv_norm_eq_halfsum hd he hf hef ((b : ℝ) • e) hbne
    rw [show ‖u‖ = b from hbdef.symm]
    rw [h, hAdef]
    simp only [inner_circVec, h1, h2, h3]
    ring_nf
  rw [hL, hR]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine intervalIntegral.integral_mono (by positivity) hInta hIntb ?_
  intro θ
  simp only []
  rw [show -(1:ℝ)/2 = -((1:ℝ)/2) from by norm_num]
  have h2d : (0:ℝ) ≤ 2 * d := by linarith
  have hmono := half_sum_rpow_neg_monoOn (A := A) (p := (1:ℝ)/2) hApos (by norm_num)
  have Gabs : ∀ y : ℝ, (1/2) * ((A + y) ^ (-((1:ℝ)/2)) + (A - y) ^ (-((1:ℝ)/2)))
      = (1/2) * ((A + |y|) ^ (-((1:ℝ)/2)) + (A - |y|) ^ (-((1:ℝ)/2))) := by
    intro y
    rcases le_or_gt 0 y with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h]; ring_nf
  have e1 : |2 * d * (a * Real.cos θ)| = 2 * d * (a * |Real.cos θ|) := abs_mul_mul_abs h2d ha0
  have e2 : |2 * d * (b * Real.cos θ)| = 2 * d * (b * |Real.cos θ|) := abs_mul_mul_abs h2d hb0
  have hcosle : |Real.cos θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
  have hle : 2 * d * (a * |Real.cos θ|) ≤ 2 * d * (b * |Real.cos θ|) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hab (abs_nonneg _)) h2d
  have hlt : 2 * d * (b * |Real.cos θ|) < A := by
    have h4 : 2 * d * b < A := by rw [hAdef]; nlinarith [hbd2, hb0, hd]
    have h5 : (0:ℝ) ≤ 2 * d * b := by positivity
    nlinarith
  rw [Gabs (2 * d * (a * Real.cos θ)), Gabs (2 * d * (b * Real.cos θ)), e1, e2]
  exact hmono (Set.mem_Ico.mpr ⟨by positivity, lt_of_le_of_lt hle hlt⟩)
    (Set.mem_Ico.mpr ⟨by positivity, hlt⟩) hle

end Submission.NBody
