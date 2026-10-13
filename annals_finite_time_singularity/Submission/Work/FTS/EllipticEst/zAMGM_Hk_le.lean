/-
Copyright: work module for the Elgindi finite-time singularity project.

# The radial weighted Agmon/AM-GM interpolation `zAMGM_Hk_le`

Target:

  `Work.FTS.EllipticEst.zAMGM_Hk_le`:

for every `n` there is a universal `C > 0` such that for every `0 < α ≤ 1`, every `g` smooth on
`(0,∞)` for which the `ρ = w²`-weighted `L²`-norms of `rDzIter (n+2) g` and of `rDzIter n g` are
finite,

  `α |rDzIter (n+1) g|_ρ ≤ C (α² |rDzIter (n+2) g|_ρ + |rDzIter n g|_ρ)`,

where `|f|_ρ = √(∫₀^∞ w(z)² f(z)² dz)` and `w(z) = (1+z)²/z²` is the radial weight of the paper.

This is the one-dimensional *Agmon–Nirenberg* (geometric-mean) interpolation for the operator
`D = z ∂_z` on the weighted space `L²(ρ dz)`, with the sharp `α²`/`1` scaling that makes the
intermediate derivative disappear as `α → 0`.

## Route

Write `h = rDzIter n g`, `h₁ = Dh = rDzIter (n+1) g`, `h₂ = D h₁ = rDzIter (n+2) g` and
`X = ∫ρh₁²`, `P = ∫ρh²`, `R = ∫ρh₂²`.  The proof has two ingredients.

* **The integration by parts.**  With `u = ρ z h₁` (so that `u h' = ρ h₁²`) and
  `u' = (ρz)' h₁ + ρ h₂`, `|(ρz)'| ≤ 3ρ`:

  `X = -∫ u' h + [u h] ≤ ∫ (3ρ|h₁||h| + ρ|h₂||h|)`,

  the boundary term `ρ z h h₁` vanishing at both ends
  (`Work.FTS.EllipticEst.Aux.boundary_rho_tendsto`).  Young's inequality with the weights `3` and
  `α²` turns the right-hand side into `½X + (9/2)P + ½α²R + ½α⁻²P`, whence

  `X ≤ (9 + α⁻²) P + α² R`.

* **The arithmetic.**  `α√X ≤ α√((9+α⁻²)P + α²R) ≤ √(9α²+1)√P + α²√R ≤ 4(α²√R + √P)` for
  `α ≤ 1`.

The first ingredient also needs the smoothness of the iterates `rDzIter k g` on `(0,∞)`
(`Work.FTS.EllipticEst.Aux.rDzIter_contDiffOn`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.EllipticEst.GbarSetup
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

/-! ## The weight `ρ = w²` and its elementary properties -/

private def rho (z : ℝ) : ℝ := (Work.Spaces.w z) ^ 2

private lemma rho_eq (z : ℝ) : rho z = (1 + z) ^ 4 / z ^ 4 := by
  simp only [rho, Work.Spaces.w, div_pow]
  ring

private lemma rho_nonneg (z : ℝ) : 0 ≤ rho z := by
  rw [rho_eq]; positivity

private lemma rho_pos {z : ℝ} (hz : 0 < z) : 0 < rho z := by
  rw [rho_eq]
  exact div_pos (by positivity) (by positivity)

private lemma contDiffOn_rho : ContDiffOn ℝ ⊤ rho (Set.Ioi (0 : ℝ)) := by
  have h : rho = fun z : ℝ => (1 + z) ^ 4 / z ^ 4 := funext rho_eq
  rw [h]
  exact ContDiffOn.div (by fun_prop) (by fun_prop)
    (fun z hz => pow_ne_zero 4 (ne_of_gt hz))

private lemma deriv_rhoz (z : ℝ) (hz : 0 < z) :
    deriv (fun w : ℝ => rho w * w) z = (z - 3) / (1 + z) * rho z := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hfun : (fun w : ℝ => rho w * w) = fun w : ℝ => (1 + w) ^ 4 / w ^ 3 := by
    funext w
    rcases eq_or_ne w 0 with rfl | hw
    · norm_num [rho, Work.Spaces.w]
    · rw [rho_eq]
      field_simp
  rw [hfun]
  have hd1 : DifferentiableAt ℝ (fun w : ℝ => (1 + w) ^ 4) z := by fun_prop
  have hd2 : DifferentiableAt ℝ (fun w : ℝ => w ^ 3) z := by fun_prop
  have hd3 : (fun w : ℝ => w ^ 3) z ≠ 0 := by simpa using pow_ne_zero 3 hz0
  rw [show (fun w : ℝ => (1 + w) ^ 4 / w ^ 3)
      = (fun w : ℝ => (1 + w) ^ 4) / (fun w : ℝ => w ^ 3) from rfl]
  rw [deriv_div hd1 hd2 hd3]
  have hv1 : deriv (fun w : ℝ => (1 + w) ^ 4) z = 4 * (1 + z) ^ 3 := by
    change deriv ((fun w : ℝ => 1 + w) ^ 4) z = 4 * (1 + z) ^ 3
    rw [deriv_pow (by fun_prop : DifferentiableAt ℝ (fun w : ℝ => 1 + w) z)]
    simp
  have hv2 : deriv (fun w : ℝ => w ^ 3) z = 3 * z ^ 2 := by
    change deriv ((fun w : ℝ => w) ^ 3) z = 3 * z ^ 2
    rw [deriv_pow (by fun_prop : DifferentiableAt ℝ (fun w : ℝ => w) z)]
    simp
  rw [hv1, hv2, rho_eq]
  field_simp
  ring

private lemma abs_deriv_rhoz_le (z : ℝ) (hz : 0 < z) :
    |deriv (fun w : ℝ => rho w * w) z| ≤ 3 * rho z := by
  have h1 : 0 < 1 + z := by linarith
  have h2 : |z - 3| ≤ 3 * (1 + z) := by
    rcases le_total 3 z with h | h
    · rw [abs_of_nonneg (by linarith)]; linarith
    · rw [abs_of_nonpos (by linarith)]; linarith
  have h3 : |z - 3| / (1 + z) ≤ 3 := by
    rw [div_le_iff₀ h1]; linarith
  rw [deriv_rhoz z hz, abs_mul, abs_of_nonneg (le_of_lt (rho_pos hz)), abs_div,
    abs_of_pos h1]
  exact mul_le_mul_of_nonneg_right h3 (le_of_lt (rho_pos hz))

/-! ## Young's inequality and the elementary square-root lemmas -/

private lemma amgm2 (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

private lemma youngB (r a b μ : ℝ) (hr : 0 ≤ r) (hμ : 0 < μ) :
    r * |a| * |b| ≤ (1 / 2) * (μ * (r * a ^ 2) + μ⁻¹ * (r * b ^ 2)) := by
  have hsqrt : Real.sqrt μ * Real.sqrt μ⁻¹ = 1 := by
    rw [← Real.sqrt_mul (le_of_lt hμ), mul_inv_cancel₀ (ne_of_gt hμ), Real.sqrt_one]
  have h := amgm2 (Real.sqrt μ * |a|) (Real.sqrt μ⁻¹ * |b|)
  rw [mul_pow, mul_pow, Real.sq_sqrt (le_of_lt hμ),
    Real.sq_sqrt (le_of_lt (inv_pos.mpr hμ)), sq_abs, sq_abs] at h
  have hleft : 2 * (Real.sqrt μ * |a|) * (Real.sqrt μ⁻¹ * |b|) = 2 * |a| * |b| := by
    calc 2 * (Real.sqrt μ * |a|) * (Real.sqrt μ⁻¹ * |b|)
        = 2 * (Real.sqrt μ * Real.sqrt μ⁻¹) * (|a| * |b|) := by ring
      _ = 2 * |a| * |b| := by rw [hsqrt]; ring
  rw [hleft] at h
  have h2 : (1 / 2) * r * (2 * |a| * |b|) ≤ (1 / 2) * r * (μ * a ^ 2 + μ⁻¹ * b ^ 2) :=
    mul_le_mul_of_nonneg_left h (by positivity)
  calc r * |a| * |b| = (1 / 2) * r * (2 * |a| * |b|) := by ring
    _ ≤ (1 / 2) * r * (μ * a ^ 2 + μ⁻¹ * b ^ 2) := h2
    _ = (1 / 2) * (μ * (r * a ^ 2) + μ⁻¹ * (r * b ^ 2)) := by ring

private lemma youngA (r a b : ℝ) (hr : 0 ≤ r) :
    3 * r * |a| * |b| ≤ (3 / 2) * ((1 / 3) * (r * a ^ 2) + 3 * (r * b ^ 2)) := by
  have h := youngB r a b (1 / 3) hr (by norm_num)
  have h' : (1 / 3 : ℝ)⁻¹ = 3 := by norm_num
  rw [h'] at h
  linarith [h]

private lemma sqrt_add_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have h : a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    have h1 := Real.sq_sqrt ha
    have h2 := Real.sq_sqrt hb
    have h3 : 0 ≤ Real.sqrt a * Real.sqrt b :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    nlinarith [h1, h2, h3]
  calc Real.sqrt (a + b) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt a + Real.sqrt b := Real.sqrt_sq (by positivity)

/-! ## The core estimate -/

/-- **The weighted Agmon inequality, in the form needed by `zAMGM_Hk_le`.**

For `0 < α ≤ 1`, functions `h, h₁ = z ∂_z h, h₂ = z ∂_z h₁` smooth on `(0,∞)` whose
`ρ = w²`-weighted `L²`-norms are finite and whose boundary term `ρ z h h₁` vanishes at `0` and at
`∞`,

  `α √(∫ρh₁²) ≤ 4 (α² √(∫ρh₂²) + √(∫ρh²))`.

The proof is the integration by parts `∫ρh₁² = -∫ (ρ z h₁)' h + [ρ z h h₁]` together with the
pointwise bound `|(ρz)'| ≤ 3ρ` and Young's inequality; see the module header. -/
private theorem zAMGM_core (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (h h1 h2 : ℝ → ℝ)
    (hd1 : ∀ z, h1 z = z * deriv h z) (hd2 : ∀ z, h2 z = z * deriv h1 z)
    (hs : ContDiffOn ℝ ⊤ h (Set.Ioi 0)) (hs1 : ContDiffOn ℝ ⊤ h1 (Set.Ioi 0))
    (hs2 : ContDiffOn ℝ ⊤ h2 (Set.Ioi 0))
    (hP : MeasureTheory.IntegrableOn (fun z => rho z * h z ^ 2) (Set.Ioi 0))
    (hX : MeasureTheory.IntegrableOn (fun z => rho z * h1 z ^ 2) (Set.Ioi 0))
    (hR : MeasureTheory.IntegrableOn (fun z => rho z * h2 z ^ 2) (Set.Ioi 0))
    (hbd0 : Tendsto (fun z => rho z * z * h z * h1 z) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hbdT : Tendsto (fun z => rho z * z * h z * h1 z) atTop (nhds 0)) :
    α * Real.sqrt (∫ z in Set.Ioi (0 : ℝ), rho z * h1 z ^ 2)
      ≤ 4 * (α ^ 2 * Real.sqrt (∫ z in Set.Ioi (0 : ℝ), rho z * h2 z ^ 2)
          + Real.sqrt (∫ z in Set.Ioi (0 : ℝ), rho z * h z ^ 2)) := by
  have hd1' : ∀ z ∈ Set.Ioi (0 : ℝ), deriv h z = h1 z / z := by
    intro z hz
    rw [hd1 z, mul_div_cancel_left₀ _ (ne_of_gt hz)]
  have hd2' : ∀ z ∈ Set.Ioi (0 : ℝ), deriv h1 z = h2 z / z := by
    intro z hz
    rw [hd2 z, mul_div_cancel_left₀ _ (ne_of_gt hz)]
  set X : ℝ := ∫ z in Set.Ioi (0 : ℝ), rho z * h1 z ^ 2 with hXeq
  set P : ℝ := ∫ z in Set.Ioi (0 : ℝ), rho z * h z ^ 2 with hPeq
  set R : ℝ := ∫ z in Set.Ioi (0 : ℝ), rho z * h2 z ^ 2 with hReq
  -- the integration by parts
  set u : ℝ → ℝ := fun z => rho z * z * h1 z with hueq
  have hu_smooth : ContDiffOn ℝ ⊤ u (Set.Ioi 0) := by
    rw [hueq]
    exact (contDiffOn_rho.mul contDiffOn_id).mul hs1
  have hu_deriv : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt u (deriv u x) x := fun x hx =>
    ((hu_smooth.differentiableOn (by simp)).differentiableAt (isOpen_Ioi.mem_nhds hx)).hasDerivAt
  have hh_deriv : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt h (deriv h x) x := fun x hx =>
    ((hs.differentiableOn (by simp)).differentiableAt (isOpen_Ioi.mem_nhds hx)).hasDerivAt
  have hdu : ∀ z ∈ Set.Ioi (0 : ℝ),
      deriv u z = deriv (fun w : ℝ => rho w * w) z * h1 z + rho z * h2 z := by
    intro z hz
    have hz0 : z ≠ 0 := ne_of_gt hz
    have hc : DifferentiableAt ℝ (fun w : ℝ => rho w * w) z :=
      ((contDiffOn_rho.mul contDiffOn_id).differentiableOn (by simp)).differentiableAt
        (isOpen_Ioi.mem_nhds hz)
    have hd : DifferentiableAt ℝ h1 z :=
      (hs1.differentiableOn (by simp)).differentiableAt (isOpen_Ioi.mem_nhds hz)
    have hsub : (rho z * z) * (h2 z / z) = rho z * h2 z := by
      field_simp
    have hmain : deriv (fun z : ℝ => rho z * z * h1 z) z
        = deriv (fun w : ℝ => rho w * w) z * h1 z + (rho z * z) * deriv h1 z := by
      change deriv ((fun w : ℝ => rho w * w) * h1) z
        = deriv (fun w : ℝ => rho w * w) z * h1 z + (rho z * z) * deriv h1 z
      exact deriv_mul hc hd
    rw [hueq]
    rw [hmain, hd2' z hz, hsub]
  have hpt : ∀ z ∈ Set.Ioi (0 : ℝ), ‖deriv u z * h z‖
      ≤ 3 * rho z * |h1 z| * |h z| + rho z * |h2 z| * |h z| := by
    intro z hz
    rw [Real.norm_eq_abs, abs_mul, hdu z hz]
    have hA := abs_deriv_rhoz_le z hz
    have hb : |rho z * h2 z| = rho z * |h2 z| := by
      rw [abs_mul, abs_of_pos (rho_pos hz)]
    calc |deriv (fun w : ℝ => rho w * w) z * h1 z + rho z * h2 z| * |h z|
        ≤ (|deriv (fun w : ℝ => rho w * w) z * h1 z| + |rho z * h2 z|) * |h z| :=
          mul_le_mul_of_nonneg_right (abs_add_le _ _) (abs_nonneg _)
      _ = (|deriv (fun w : ℝ => rho w * w) z| * |h1 z| + rho z * |h2 z|) * |h z| := by
          rw [abs_mul, hb]
      _ ≤ (3 * rho z * |h1 z| + rho z * |h2 z|) * |h z| := by
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
          exact add_le_add (mul_le_mul_of_nonneg_right hA (abs_nonneg _)) le_rfl
      _ = 3 * rho z * |h1 z| * |h z| + rho z * |h2 z| * |h z| := by ring
  -- integrability of the two pieces
  have hG1 : MeasureTheory.IntegrableOn
      (fun z => (3 / 2) * ((1 / 3) * (rho z * h1 z ^ 2) + 3 * (rho z * h z ^ 2)))
      (Set.Ioi 0) :=
    ((hX.const_mul (1 / 3)).add (hP.const_mul 3)).const_mul (3 / 2)
  have hint1 : MeasureTheory.IntegrableOn (fun z => 3 * rho z * |h1 z| * |h z|)
      (Set.Ioi 0) := by
    refine Integrable.mono' hG1 ?_ ?_
    · exact (((continuousOn_const.mul contDiffOn_rho.continuousOn).mul hs1.continuousOn.abs).mul
        hs.continuousOn.abs).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards with z
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
        (rho_nonneg z)) (abs_nonneg _)) (abs_nonneg _))]
      exact youngA (rho z) (h1 z) (h z) (rho_nonneg z)
  have hI1 : ∫ z in Set.Ioi (0 : ℝ), 3 * rho z * |h1 z| * |h z| ≤
      (3 / 2) * ((1 / 3) * X + 3 * P) := by
    have hmono := integral_mono hint1 hG1 (fun z => youngA (rho z) (h1 z) (h z) (rho_nonneg z))
    calc ∫ z in Set.Ioi (0 : ℝ), 3 * rho z * |h1 z| * |h z|
        ≤ ∫ z in Set.Ioi (0 : ℝ),
            (3 / 2) * ((1 / 3) * (rho z * h1 z ^ 2) + 3 * (rho z * h z ^ 2)) := hmono
      _ = (3 / 2) * ((1 / 3) * X + 3 * P) := by
          rw [integral_const_mul, integral_add (hX.const_mul (1 / 3)) (hP.const_mul 3),
            integral_const_mul, integral_const_mul, ← hXeq, ← hPeq]
  -- second piece
  have hG2 : MeasureTheory.IntegrableOn
      (fun z => (1 / 2) * (α ^ 2 * (rho z * h2 z ^ 2) + (α ^ 2)⁻¹ * (rho z * h z ^ 2)))
      (Set.Ioi 0) :=
    ((hR.const_mul (α ^ 2)).add (hP.const_mul ((α ^ 2)⁻¹))).const_mul (1 / 2)
  have hint2 : MeasureTheory.IntegrableOn (fun z => rho z * |h2 z| * |h z|) (Set.Ioi 0) := by
    refine Integrable.mono' hG2 ?_ ?_
    · exact (((contDiffOn_rho.continuousOn.mul hs2.continuousOn.abs).mul
        hs.continuousOn.abs)).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards with z
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (rho_nonneg z)
        (abs_nonneg _)) (abs_nonneg _))]
      exact youngB (rho z) (h2 z) (h z) (α ^ 2) (rho_nonneg z) (pow_pos hα 2)
  have hI2 : ∫ z in Set.Ioi (0 : ℝ), rho z * |h2 z| * |h z|
      ≤ (1 / 2) * (α ^ 2 * R + (α ^ 2)⁻¹ * P) := by
    have hmono := integral_mono hint2 hG2
      (fun z => youngB (rho z) (h2 z) (h z) (α ^ 2) (rho_nonneg z) (pow_pos hα 2))
    calc ∫ z in Set.Ioi (0 : ℝ), rho z * |h2 z| * |h z|
        ≤ ∫ z in Set.Ioi (0 : ℝ),
            (1 / 2) * (α ^ 2 * (rho z * h2 z ^ 2) + (α ^ 2)⁻¹ * (rho z * h z ^ 2)) := hmono
      _ = (1 / 2) * (α ^ 2 * R + (α ^ 2)⁻¹ * P) := by
          rw [integral_const_mul, integral_add (hR.const_mul (α ^ 2)) (hP.const_mul ((α ^ 2)⁻¹)),
            integral_const_mul, integral_const_mul, ← hReq, ← hPeq]
  -- the IBP itself
  have huv : MeasureTheory.IntegrableOn (u * deriv h) (Set.Ioi 0) := by
    have heq : (u * deriv h) = fun z => rho z * h1 z ^ 2 := by
      funext z
      simp only [Pi.mul_apply, hueq, hd1 z]
      ring
    rw [heq]; exact hX
  have hIntF : MeasureTheory.IntegrableOn (fun z => deriv u z * h z) (Set.Ioi 0) := by
    refine Integrable.mono' (hint1.add hint2) ?_ ?_
    · exact ((hu_smooth.continuousOn_deriv_of_isOpen isOpen_Ioi le_top).mul
        hs.continuousOn).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with z hz
      exact hpt z hz
  have hbd0' : Tendsto (u * h) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have heq : (u * h) = fun z => rho z * z * h z * h1 z := by
      funext z; rw [Pi.mul_apply, hueq]; ring
    rw [heq]; exact hbd0
  have hbdT' : Tendsto (u * h) atTop (nhds 0) := by
    have heq : (u * h) = fun z => rho z * z * h z * h1 z := by
      funext z; rw [Pi.mul_apply, hueq]; ring
    rw [heq]; exact hbdT
  have hIBP := integral_Ioi_mul_deriv_eq_deriv_mul (u := u) (v := h) (u' := deriv u)
      (v' := deriv h) (a := 0) (a' := 0) (b' := 0) hu_deriv hh_deriv huv hIntF hbd0' hbdT'
  have hXint : X = -∫ z in Set.Ioi (0 : ℝ), deriv u z * h z := by
    have heq : (fun z => u z * deriv h z) = fun z => rho z * h1 z ^ 2 := by
      funext z
      simp only [hueq, hd1 z]
      ring
    rw [hXeq]
    simp only [← heq]
    simpa using hIBP
  -- assemble
  have hstep1 : -∫ z in Set.Ioi (0 : ℝ), deriv u z * h z
      ≤ ∫ z in Set.Ioi (0 : ℝ), ‖deriv u z * h z‖ := by
    have h := norm_integral_le_integral_norm (fun z => deriv u z * h z)
      (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    rw [Real.norm_eq_abs] at h
    exact (neg_le_abs _).trans h
  have hstep2 : ∫ z in Set.Ioi (0 : ℝ), ‖deriv u z * h z‖
      ≤ ∫ z in Set.Ioi (0 : ℝ), (3 * rho z * |h1 z| * |h z| + rho z * |h2 z| * |h z|) := by
    refine integral_mono_ae hIntF.norm (hint1.add hint2) ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with z hz
    exact hpt z hz
  have hstep3 : ∫ z in Set.Ioi (0 : ℝ), (3 * rho z * |h1 z| * |h z| + rho z * |h2 z| * |h z|)
      = (∫ z in Set.Ioi (0 : ℝ), 3 * rho z * |h1 z| * |h z|)
        + ∫ z in Set.Ioi (0 : ℝ), rho z * |h2 z| * |h z| :=
    integral_add hint1 hint2
  have hmid : -∫ z in Set.Ioi (0 : ℝ), deriv u z * h z
      ≤ (3 / 2) * ((1 / 3) * X + 3 * P) + (1 / 2) * (α ^ 2 * R + (α ^ 2)⁻¹ * P) := by
    refine hstep1.trans (hstep2.trans ?_)
    rw [hstep3]
    exact add_le_add hI1 hI2
  have hfinal : X ≤ (3 / 2) * ((1 / 3) * X + 3 * P) + (1 / 2) * (α ^ 2 * R + (α ^ 2)⁻¹ * P) := by
    nth_rewrite 1 [hXint]
    exact hmid
  have hXle : X ≤ (9 + (α ^ 2)⁻¹) * P + α ^ 2 * R := by
    have h1 : (3 / 2) * ((1 / 3) * X + 3 * P) = (1 / 2) * X + (9 / 2) * P := by ring
    have h2 : (1 / 2) * (α ^ 2 * R + (α ^ 2)⁻¹ * P) = (α ^ 2 / 2) * R + ((α ^ 2)⁻¹ / 2) * P := by
      ring
    rw [h1, h2] at hfinal
    linarith
  -- final arithmetic
  have hXnn : 0 ≤ X := by
    rw [hXeq]
    exact setIntegral_nonneg measurableSet_Ioi (fun z _ => mul_nonneg (rho_nonneg z) (sq_nonneg _))
  have hPnn : 0 ≤ P := by
    rw [hPeq]
    exact setIntegral_nonneg measurableSet_Ioi (fun z _ => mul_nonneg (rho_nonneg z) (sq_nonneg _))
  have hRnn : 0 ≤ R := by
    rw [hReq]
    exact setIntegral_nonneg measurableSet_Ioi (fun z _ => mul_nonneg (rho_nonneg z) (sq_nonneg _))
  have hfin : α * Real.sqrt X ≤ 4 * (α ^ 2 * Real.sqrt R + Real.sqrt P) := by
    have h1 : α * Real.sqrt X ≤ α * Real.sqrt ((9 + (α ^ 2)⁻¹) * P + α ^ 2 * R) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hXle) (le_of_lt hα)
    refine h1.trans ?_
    have hA : 0 ≤ (9 + (α ^ 2)⁻¹) * P :=
      mul_nonneg (by positivity) hPnn
    have hB : 0 ≤ α ^ 2 * R := mul_nonneg (sq_nonneg α) hRnn
    have h2 : α * Real.sqrt ((9 + (α ^ 2)⁻¹) * P + α ^ 2 * R)
        ≤ α * (Real.sqrt ((9 + (α ^ 2)⁻¹) * P) + Real.sqrt (α ^ 2 * R)) :=
      mul_le_mul_of_nonneg_left (sqrt_add_le _ _ hA hB) (le_of_lt hα)
    refine h2.trans ?_
    rw [mul_add]
    have e1 : α * Real.sqrt ((9 + (α ^ 2)⁻¹) * P) = Real.sqrt (9 * α ^ 2 + 1) * Real.sqrt P := by
      rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 9 + (α ^ 2)⁻¹)]
      have hsq : α * Real.sqrt (9 + (α ^ 2)⁻¹) = Real.sqrt (α ^ 2 * (9 + (α ^ 2)⁻¹)) := by
        rw [Real.sqrt_mul (sq_nonneg α), Real.sqrt_sq (le_of_lt hα)]
      rw [← mul_assoc, hsq,
        show α ^ 2 * (9 + (α ^ 2)⁻¹) = 9 * α ^ 2 + 1 by field_simp]
    have e2 : α * Real.sqrt (α ^ 2 * R) = α ^ 2 * Real.sqrt R := by
      rw [Real.sqrt_mul (sq_nonneg α), Real.sqrt_sq (le_of_lt hα)]
      ring
    rw [e1, e2]
    have h3 : Real.sqrt (9 * α ^ 2 + 1) ≤ 4 := by
      have h4 : 9 * α ^ 2 + 1 ≤ 16 := by nlinarith [sq_nonneg α, hα1]
      calc Real.sqrt (9 * α ^ 2 + 1) ≤ Real.sqrt 16 := Real.sqrt_le_sqrt h4
        _ = 4 := by norm_num
    nlinarith [h3, Real.sqrt_nonneg P, Real.sqrt_nonneg R, sq_nonneg α]
  exact hfin

/-! ## The smoothness of the iterates `rDzIter k g` -/

private lemma rDzIter_contDiffOn_loc (k : ℕ) (g : ℝ → ℝ)
    (hg : ContDiffOn ℝ ⊤ g (Set.Ioi 0)) :
    ContDiffOn ℝ ⊤ (rDzIter k g) (Set.Ioi 0) := by
  induction k with
  | zero => simpa using hg
  | succ k ih =>
      rw [rDzIter_succ]
      have h1 : ContDiffOn ℝ ⊤ (deriv (rDzIter k g)) (Set.Ioi 0) :=
        ih.deriv_of_isOpen isOpen_Ioi le_top
      rw [show rDz (rDzIter k g) = fun z => z * deriv (rDzIter k g) z from rfl]
      exact (contDiffOn_id (𝕜 := ℝ) (n := ⊤) (s := Set.Ioi (0 : ℝ))).mul h1

private lemma rDzIter_hasDerivAt_loc (k : ℕ) (g : ℝ → ℝ)
    (hg : ContDiffOn ℝ ⊤ g (Set.Ioi 0)) :
    ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt (rDzIter k g) (rDzIter (k + 1) g z / z) z := by
  intro z hz
  have hdiff : DifferentiableAt ℝ (rDzIter k g) z :=
    ((rDzIter_contDiffOn_loc k g hg).differentiableOn (by simp)).differentiableAt
      (isOpen_Ioi.mem_nhds hz)
  have hval : rDzIter (k + 1) g z / z = deriv (rDzIter k g) z := by
    simp only [rDzIter_succ, rDz]
    rw [mul_div_cancel_left₀ _ (ne_of_gt hz)]
  rw [hval]
  exact hdiff.hasDerivAt

/-! ## The boundary term `w² z h h₁`

The one input of the integration by parts in `zAMGM_core` that is not an elementary estimate: the
boundary term `w(z)² z h(z) h₁(z)` vanishes both at `z → 0⁺` and at `z → ∞`.

Route: the functions `u = w h`, `v = w h₁` are, in the logarithmic variable, the profiles
`P(t) = e^{t/2}w(e^t)h(e^t)`, `Q(t) = e^{t/2}w(e^t)h₁(e^t)`, and `w(z)² z h h₁ = P(log z) Q(log z)`.
The three finiteness hypotheses say exactly that `P, P', Q, Q'` are square-integrable, hence also
that `P ^ 2`, `Q ^ 2` have integrable derivatives; the Mathlib lemma
`tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi` (applied to `P ^ 2` and `Q ^ 2`, and its `Iic`
counterpart) then gives `P, Q → 0` at both ends of the logarithmic line, whence the product.
The substitution `z = e^t` in the integrals is `integrableOn_comp_log_Ioi_zero`. -/

private lemma hasDerivAt_w (z : ℝ) (hz : 0 < z) :
    HasDerivAt Work.Spaces.w (-2 * Work.Spaces.w z / (z * (1 + z))) z := by
  have hnum : HasDerivAt (fun y : ℝ => (1 + y) ^ 2) (2 * (1 + z)) z := by
    have h : HasDerivAt (fun y : ℝ => 1 + y) (1 : ℝ) z := by
      simpa using (hasDerivAt_id z).const_add (1 : ℝ)
    have h2 := h.fun_pow 2
    simpa [pow_one, Nat.cast_ofNat] using h2
  have hden : HasDerivAt (fun y : ℝ => y ^ 2) (2 * z) z := by
    have h := (hasDerivAt_id z).fun_pow 2
    simpa [pow_one, Nat.cast_ofNat] using h
  have hdiv := hnum.div hden (by positivity)
  refine hdiv.congr_deriv ?_
  simp only [Work.Spaces.w]
  field_simp
  ring

private lemma differentiableAt_w {z : ℝ} (hz : 0 < z) : DifferentiableAt ℝ Work.Spaces.w z :=
  (hasDerivAt_w z hz).differentiableAt

private lemma deriv_w (z : ℝ) (hz : 0 < z) :
    deriv Work.Spaces.w z = -2 * Work.Spaces.w z / (z * (1 + z)) := (hasDerivAt_w z hz).deriv

/-- The logarithmic profile `t ↦ e^{t/2}·u(e^t)` of `z ↦ √z·u(z)`. -/
private lemma hasDerivAt_profile (u u' : ℝ → ℝ) (t : ℝ)
    (hu : HasDerivAt u (u' (Real.exp t)) (Real.exp t)) :
    HasDerivAt (fun s => Real.exp (s / 2) * u (Real.exp s))
      (Real.exp (t / 2) * (u (Real.exp t) / 2 + Real.exp t * u' (Real.exp t))) t := by
  have hcomp : HasDerivAt (fun s => u (Real.exp s)) (u' (Real.exp t) * Real.exp t) t :=
    hu.comp t (Real.hasDerivAt_exp t)
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (s / 2)) (Real.exp (t / 2) / 2) t := by
    have hlin : HasDerivAt (fun s : ℝ => s / 2) (1 / 2 : ℝ) t := by
      simpa using (hasDerivAt_id t).div_const (2 : ℝ)
    have h := (Real.hasDerivAt_exp (t / 2)).comp t hlin
    refine h.congr_deriv ?_
    ring
  have hmain := hexp.mul hcomp
  refine hmain.congr_deriv ?_
  ring

/-- `hasDerivAt_profile` for `u = w·h`, with the derivative expressed through `h₁ = z ∂_z h`. -/
private lemma hasDerivAt_profile_wmul (h h1 : ℝ → ℝ)
    (hdiff : ∀ z ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ h z)
    (hd : ∀ z : ℝ, h1 z = z * deriv h z) (t : ℝ) :
    HasDerivAt (fun s => Real.exp (s / 2) * (Work.Spaces.w (Real.exp s) * h (Real.exp s)))
      (Real.exp (t / 2) * (Work.Spaces.w (Real.exp t) * h1 (Real.exp t)
        + Work.Spaces.w (Real.exp t) * h (Real.exp t) * (1 / 2 - 2 / (1 + Real.exp t)))) t := by
  have hz : (0 : ℝ) < Real.exp t := Real.exp_pos t
  have hh : HasDerivAt h (deriv h (Real.exp t)) (Real.exp t) := (hdiff _ hz).hasDerivAt
  have hw : HasDerivAt Work.Spaces.w (deriv Work.Spaces.w (Real.exp t)) (Real.exp t) :=
    (differentiableAt_w hz).hasDerivAt
  have hprod : HasDerivAt (fun y => Work.Spaces.w y * h y)
      (deriv Work.Spaces.w (Real.exp t) * h (Real.exp t)
        + Work.Spaces.w (Real.exp t) * deriv h (Real.exp t)) (Real.exp t) := hw.mul hh
  have hmain := hasDerivAt_profile (fun y => Work.Spaces.w y * h y)
    (fun y => deriv Work.Spaces.w y * h y + Work.Spaces.w y * deriv h y) t hprod
  refine hmain.congr_deriv ?_
  rw [deriv_w (Real.exp t) hz, hd (Real.exp t)]
  have hz0 : Real.exp t ≠ 0 := ne_of_gt hz
  have hz1 : 1 + Real.exp t ≠ 0 := by positivity
  field_simp
  ring

/-- The key algebraic identities for the logarithmic profiles. -/
private lemma half_mul_eq (x : ℝ) (hx : 0 < x) :
    Real.exp (Real.log x / 2) * Real.exp (Real.log x / 2) = x := by
  rw [← Real.exp_add, show Real.log x / 2 + Real.log x / 2 = Real.log x by ring, Real.exp_log hx]

private lemma half_sq_eq (x : ℝ) (hx : 0 < x) :
    Real.exp (Real.log x / 2) ^ 2 = x := by
  rw [sq, half_mul_eq x hx]

private lemma inv_sq_mul (x A : ℝ) (hx : 0 < x) :
    x⁻¹ * (Real.exp (Real.log x / 2) * A) ^ 2 = A ^ 2 := by
  rw [mul_pow, half_sq_eq x hx]
  field_simp

private lemma inv_two_mul (x A B : ℝ) (hx : 0 < x) :
    x⁻¹ * (2 * (Real.exp (Real.log x / 2) * A) * (Real.exp (Real.log x / 2) * B))
      = 2 * A * B := by
  rw [show 2 * (Real.exp (Real.log x / 2) * A) * (Real.exp (Real.log x / 2) * B)
      = (Real.exp (Real.log x / 2) * Real.exp (Real.log x / 2)) * (2 * A * B) by ring,
    half_mul_eq x hx]
  field_simp

/-- The pointwise product identity: the product of the two `√z`-profiles is `w² z h h₁`. -/
private lemma profile_mul (h h1 : ℝ → ℝ) (z : ℝ) (hz : 0 < z) :
    (Real.exp (Real.log z / 2) * (Work.Spaces.w (Real.exp (Real.log z)) * h (Real.exp (Real.log z))))
      * (Real.exp (Real.log z / 2)
          * (Work.Spaces.w (Real.exp (Real.log z)) * h1 (Real.exp (Real.log z))))
    = Work.Spaces.w z ^ 2 * z * h z * h1 z := by
  rw [Real.exp_log hz]
  rw [show (Real.exp (Real.log z / 2) * (Work.Spaces.w z * h z))
      * (Real.exp (Real.log z / 2) * (Work.Spaces.w z * h1 z))
      = (Real.exp (Real.log z / 2) * Real.exp (Real.log z / 2))
        * ((Work.Spaces.w z * h z) * (Work.Spaces.w z * h1 z)) by ring,
    half_mul_eq z hz]
  ring

private lemma c_abs_le (x : ℝ) (hx : 0 < x) : |(1 / 2 : ℝ) - 2 / (1 + x)| ≤ 3 / 2 := by
  have hp : 0 < 1 + x := by linarith
  have h2 : 2 / (1 + x) ≤ 2 := by
    rw [div_le_iff₀ hp]; linarith
  have h3 : 0 ≤ 2 / (1 + x) := by positivity
  rw [abs_le]
  constructor <;> linarith

/-- `(a + b·c)² ≤ 2a² + (9/2)b²` for `|c| ≤ 3/2`. -/
private lemma sq_add_mul_le (a b c : ℝ) (hc : |c| ≤ 3 / 2) :
    (a + b * c) ^ 2 ≤ 2 * a ^ 2 + (9 / 2) * b ^ 2 := by
  have h1 : (a + b * c) ^ 2 ≤ 2 * a ^ 2 + 2 * (b * c) ^ 2 := by
    nlinarith [sq_nonneg (a - b * c)]
  have h2 : (b * c) ^ 2 ≤ (9 / 4) * b ^ 2 := by
    have h3 : b ^ 2 * c ^ 2 ≤ b ^ 2 * (9 / 4) :=
      mul_le_mul_of_nonneg_left (by nlinarith [hc, abs_nonneg c, sq_abs c]) (sq_nonneg b)
    nlinarith [h3]
  nlinarith [h1, h2]

/-- `|2a(b + a·c)| ≤ 4a² + b²` for `|c| ≤ 3/2`. -/
private lemma abs_two_mul_add_mul_le (a b c : ℝ) (hc : |c| ≤ 3 / 2) :
    |2 * a * (b + a * c)| ≤ 4 * a ^ 2 + b ^ 2 := by
  have h1 : |b + a * c| ≤ |b| + |a| * |c| := by
    calc |b + a * c| ≤ |b| + |a * c| := abs_add_le _ _
      _ = |b| + |a| * |c| := by rw [abs_mul]
  have h2 : |2 * a * (b + a * c)| ≤ 2 * |a| * (|b| + |a| * |c|) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have h3 : 0 ≤ 2 * |a| := by positivity
    nlinarith [h1, h3]
  have h4 : 2 * |a| * |b| ≤ a ^ 2 + b ^ 2 := by
    nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]
  have h5 : 2 * |a| * (|a| * |c|) ≤ 3 * a ^ 2 := by
    have h6 : |a| * |c| ≤ |a| * (3 / 2) := mul_le_mul_of_nonneg_left hc (abs_nonneg a)
    nlinarith [h6, abs_nonneg a, sq_abs a]
  nlinarith [h2, h4, h5]

/-- The main boundary statement: for `h` smooth on `(0,∞)` with finite `w²`-weighted `L²`-norms
of `h`, `h₁ = z∂_z h` and `h₂ = z∂_z h₁`, the boundary term `w² z h h₁` vanishes at `0` and `∞`. -/
private theorem boundary_tendsto (h h1 : ℝ → ℝ)
    (hs : ContDiffOn ℝ ⊤ h (Set.Ioi 0)) (hs1 : ContDiffOn ℝ ⊤ h1 (Set.Ioi 0))
    (hd : ∀ z : ℝ, h1 z = z * deriv h z)
    (hP : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * h z ^ 2) (Set.Ioi 0))
    (hX : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * h1 z ^ 2) (Set.Ioi 0))
    (hR : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * (z * deriv h1 z) ^ 2) (Set.Ioi 0)) :
    Filter.Tendsto (fun z => (Work.Spaces.w z) ^ 2 * z * h z * h1 z)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun z => (Work.Spaces.w z) ^ 2 * z * h z * h1 z) Filter.atTop (nhds 0) := by
  classical
  have hdiff : ∀ z ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ h z := fun z hz =>
    (hs.differentiableOn (by simp)).differentiableAt (isOpen_Ioi.mem_nhds hz)
  have hdiff1 : ∀ z ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ h1 z := fun z hz =>
    (hs1.differentiableOn (by simp)).differentiableAt (isOpen_Ioi.mem_nhds hz)
  have hc_w : ContinuousOn Work.Spaces.w (Set.Ioi 0) := by
    rw [show Work.Spaces.w = fun z : ℝ => (1 + z) ^ 2 / z ^ 2 from rfl]
    exact ContinuousOn.div (by fun_prop) (by fun_prop)
      (fun z hz => pow_ne_zero 2 (ne_of_gt hz))
  have hc_h : ContinuousOn h (Set.Ioi 0) := hs.continuousOn
  have hc_h1 : ContinuousOn h1 (Set.Ioi 0) := hs1.continuousOn
  have hc_d1 : ContinuousOn (deriv h1) (Set.Ioi 0) :=
    hs1.continuousOn_deriv_of_isOpen isOpen_Ioi le_top
  have hc_c : ContinuousOn (fun x : ℝ => (1 / 2 : ℝ) - 2 / (1 + x)) (Set.Ioi 0) := by
    refine ContinuousOn.sub continuousOn_const (ContinuousOn.div continuousOn_const
      ((continuousOn_const (c := (1 : ℝ))).add continuousOn_id) ?_)
    intro x hx
    have : (0 : ℝ) < 1 + x := by linarith [Set.mem_Ioi.mp hx]
    positivity
  set F : ℝ → ℝ := fun t => Real.exp (t / 2) * (Work.Spaces.w (Real.exp t) * h (Real.exp t)) with hF
  set G : ℝ → ℝ := fun t => Real.exp (t / 2) * (Work.Spaces.w (Real.exp t) * h1 (Real.exp t)) with hG
  set F' : ℝ → ℝ := fun t => Real.exp (t / 2) * (Work.Spaces.w (Real.exp t) * h1 (Real.exp t)
      + Work.Spaces.w (Real.exp t) * h (Real.exp t) * (1 / 2 - 2 / (1 + Real.exp t))) with hFp
  set G' : ℝ → ℝ := fun t => Real.exp (t / 2)
      * (Work.Spaces.w (Real.exp t) * (Real.exp t * deriv h1 (Real.exp t))
        + Work.Spaces.w (Real.exp t) * h1 (Real.exp t) * (1 / 2 - 2 / (1 + Real.exp t))) with hGp
  have hFderiv : ∀ t, HasDerivAt F (F' t) t := by
    intro t
    simpa only [hF, hFp] using hasDerivAt_profile_wmul h h1 hdiff hd t
  have hGderiv : ∀ t, HasDerivAt G (G' t) t := by
    intro t
    simpa only [hG, hGp] using
      hasDerivAt_profile_wmul h1 (fun z => z * deriv h1 z) hdiff1 (fun z => rfl) t
  -- integrability of `F²`, `F'²`, `G²`, `G'²` by the logarithmic substitution
  have hF2 : Integrable (fun t => F t ^ 2) := by
    refine (integrableOn_comp_log_Ioi_zero (fun t => F t ^ 2)).mp ?_
    have heq : (fun x => x⁻¹ • F (Real.log x) ^ 2)
        =ᵐ[volume.restrict (Set.Ioi 0)] (fun x => (Work.Spaces.w x) ^ 2 * h x ^ 2) := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
      have hx0 : 0 < x := hx
      simp only [hF, smul_eq_mul, Real.exp_log hx0]
      simpa only [Pi.pow_apply, mul_pow] using inv_sq_mul x (Work.Spaces.w x * h x) hx0
    exact hP.congr heq.symm
  have hF'2 : Integrable (fun t => F' t ^ 2) := by
    refine (integrableOn_comp_log_Ioi_zero (fun t => F' t ^ 2)).mp ?_
    have hbd : MeasureTheory.IntegrableOn
        (fun x => 2 * ((Work.Spaces.w x) ^ 2 * h1 x ^ 2)
          + (9 / 2) * ((Work.Spaces.w x) ^ 2 * h x ^ 2)) (Set.Ioi 0) :=
      (hX.const_mul 2).add (hP.const_mul (9 / 2))
    have heq : (fun x => x⁻¹ • F' (Real.log x) ^ 2) =ᵐ[volume.restrict (Set.Ioi 0)]
        (fun x => (Work.Spaces.w x * h1 x
          + Work.Spaces.w x * h x * (1 / 2 - 2 / (1 + x))) ^ 2) := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
      have hx0 : 0 < x := hx
      simp only [hFp, smul_eq_mul, Real.exp_log hx0]
      simpa only [Pi.pow_apply, mul_pow] using inv_sq_mul x (Work.Spaces.w x * h1 x
        + Work.Spaces.w x * h x * (1 / 2 - 2 / (1 + x))) hx0
    have hcont : ContinuousOn (fun x => (Work.Spaces.w x * h1 x
        + Work.Spaces.w x * h x * (1 / 2 - 2 / (1 + x))) ^ 2) (Set.Ioi 0) :=
      (((hc_w.mul hc_h1).add ((hc_w.mul hc_h).mul hc_c))).pow 2
    have hsm : MeasureTheory.IntegrableOn (fun x => (Work.Spaces.w x * h1 x
        + Work.Spaces.w x * h x * (1 / 2 - 2 / (1 + x))) ^ 2) (Set.Ioi 0) := by
      refine Integrable.mono' hbd (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
      have hx0 : 0 < x := hx
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      calc (Work.Spaces.w x * h1 x + Work.Spaces.w x * h x * ((1 : ℝ) / 2 - 2 / (1 + x))) ^ 2
          ≤ 2 * (Work.Spaces.w x * h1 x) ^ 2 + (9 / 2) * (Work.Spaces.w x * h x) ^ 2 :=
            sq_add_mul_le _ _ _ (c_abs_le x hx0)
        _ = 2 * ((Work.Spaces.w x) ^ 2 * h1 x ^ 2)
              + (9 / 2) * ((Work.Spaces.w x) ^ 2 * h x ^ 2) := by ring
    exact hsm.congr heq.symm
  have hG2 : Integrable (fun t => G t ^ 2) := by
    refine (integrableOn_comp_log_Ioi_zero (fun t => G t ^ 2)).mp ?_
    have heq : (fun x => x⁻¹ • G (Real.log x) ^ 2)
        =ᵐ[volume.restrict (Set.Ioi 0)] (fun x => (Work.Spaces.w x) ^ 2 * h1 x ^ 2) := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
      have hx0 : 0 < x := hx
      simp only [hG, smul_eq_mul, Real.exp_log hx0]
      simpa only [Pi.pow_apply, mul_pow] using inv_sq_mul x (Work.Spaces.w x * h1 x) hx0
    exact hX.congr heq.symm
  have hG'2 : Integrable (fun t => G' t ^ 2) := by
    refine (integrableOn_comp_log_Ioi_zero (fun t => G' t ^ 2)).mp ?_
    have hbd : MeasureTheory.IntegrableOn
        (fun x => 2 * ((Work.Spaces.w x) ^ 2 * (x * deriv h1 x) ^ 2)
          + (9 / 2) * ((Work.Spaces.w x) ^ 2 * h1 x ^ 2)) (Set.Ioi 0) :=
      (hR.const_mul 2).add (hX.const_mul (9 / 2))
    have heq : (fun x => x⁻¹ • G' (Real.log x) ^ 2) =ᵐ[volume.restrict (Set.Ioi 0)]
        (fun x => (Work.Spaces.w x * (x * deriv h1 x)
          + Work.Spaces.w x * h1 x * (1 / 2 - 2 / (1 + x))) ^ 2) := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
      have hx0 : 0 < x := hx
      simp only [hGp, smul_eq_mul, Real.exp_log hx0]
      simpa only [Pi.pow_apply, mul_pow] using inv_sq_mul x (Work.Spaces.w x * (x * deriv h1 x)
        + Work.Spaces.w x * h1 x * (1 / 2 - 2 / (1 + x))) hx0
    have hcont : ContinuousOn (fun x => (Work.Spaces.w x * (x * deriv h1 x)
        + Work.Spaces.w x * h1 x * (1 / 2 - 2 / (1 + x))) ^ 2) (Set.Ioi 0) :=
      (((hc_w.mul (continuousOn_id.mul hc_d1)).add ((hc_w.mul hc_h1).mul hc_c))).pow 2
    have hsm : MeasureTheory.IntegrableOn (fun x => (Work.Spaces.w x * (x * deriv h1 x)
        + Work.Spaces.w x * h1 x * (1 / 2 - 2 / (1 + x))) ^ 2) (Set.Ioi 0) := by
      refine Integrable.mono' hbd (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
      have hx0 : 0 < x := hx
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      calc (Work.Spaces.w x * (x * deriv h1 x)
            + Work.Spaces.w x * h1 x * ((1 : ℝ) / 2 - 2 / (1 + x))) ^ 2
          ≤ 2 * (Work.Spaces.w x * (x * deriv h1 x)) ^ 2
              + (9 / 2) * (Work.Spaces.w x * h1 x) ^ 2 :=
            sq_add_mul_le _ _ _ (c_abs_le x hx0)
        _ = 2 * ((Work.Spaces.w x) ^ 2 * (x * deriv h1 x) ^ 2)
              + (9 / 2) * ((Work.Spaces.w x) ^ 2 * h1 x ^ 2) := by ring
    exact hsm.congr heq.symm
  -- integrability of the cross terms `2 F F'`, `2 G G'`
  have hFF' : Integrable (fun t => 2 * F t * F' t) := by
    refine (integrableOn_comp_log_Ioi_zero (fun t => 2 * F t * F' t)).mp ?_
    have hbd : MeasureTheory.IntegrableOn
        (fun x => 4 * ((Work.Spaces.w x) ^ 2 * h x ^ 2)
          + ((Work.Spaces.w x) ^ 2 * h1 x ^ 2)) (Set.Ioi 0) :=
      (hP.const_mul 4).add hX
    have heq : (fun x => x⁻¹ • (2 * F (Real.log x) * F' (Real.log x)))
        =ᵐ[volume.restrict (Set.Ioi 0)]
        (fun x => 2 * (Work.Spaces.w x * h x)
          * (Work.Spaces.w x * h1 x + Work.Spaces.w x * h x * (1 / 2 - 2 / (1 + x)))) := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
      have hx0 : 0 < x := hx
      simp only [hF, hFp, smul_eq_mul, Real.exp_log hx0]
      exact inv_two_mul x (Work.Spaces.w x * h x)
        (Work.Spaces.w x * h1 x + Work.Spaces.w x * h x * (1 / 2 - 2 / (1 + x))) hx0
    have hcont : ContinuousOn (fun x => 2 * (Work.Spaces.w x * h x)
        * (Work.Spaces.w x * h1 x + Work.Spaces.w x * h x * (1 / 2 - 2 / (1 + x))))
        (Set.Ioi 0) :=
      (continuousOn_const.mul (hc_w.mul hc_h)).mul
        (((hc_w.mul hc_h1).add ((hc_w.mul hc_h).mul hc_c)))
    have hsm : MeasureTheory.IntegrableOn (fun x => 2 * (Work.Spaces.w x * h x)
        * (Work.Spaces.w x * h1 x + Work.Spaces.w x * h x * (1 / 2 - 2 / (1 + x))))
        (Set.Ioi 0) := by
      refine Integrable.mono' hbd (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
      have hx0 : 0 < x := hx
      rw [Real.norm_eq_abs]
      calc |2 * (Work.Spaces.w x * h x)
            * (Work.Spaces.w x * h1 x + Work.Spaces.w x * h x * ((1 : ℝ) / 2 - 2 / (1 + x)))|
          ≤ 4 * (Work.Spaces.w x * h x) ^ 2 + (Work.Spaces.w x * h1 x) ^ 2 :=
            abs_two_mul_add_mul_le _ _ _ (c_abs_le x hx0)
        _ = 4 * ((Work.Spaces.w x) ^ 2 * h x ^ 2) + ((Work.Spaces.w x) ^ 2 * h1 x ^ 2) := by ring
    exact hsm.congr heq.symm
  have hGG' : Integrable (fun t => 2 * G t * G' t) := by
    refine (integrableOn_comp_log_Ioi_zero (fun t => 2 * G t * G' t)).mp ?_
    have hbd : MeasureTheory.IntegrableOn
        (fun x => 4 * ((Work.Spaces.w x) ^ 2 * h1 x ^ 2)
          + ((Work.Spaces.w x) ^ 2 * (x * deriv h1 x) ^ 2)) (Set.Ioi 0) :=
      (hX.const_mul 4).add hR
    have heq : (fun x => x⁻¹ • (2 * G (Real.log x) * G' (Real.log x)))
        =ᵐ[volume.restrict (Set.Ioi 0)]
        (fun x => 2 * (Work.Spaces.w x * h1 x)
          * (Work.Spaces.w x * (x * deriv h1 x)
            + Work.Spaces.w x * h1 x * (1 / 2 - 2 / (1 + x)))) := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
      have hx0 : 0 < x := hx
      simp only [hG, hGp, smul_eq_mul, Real.exp_log hx0]
      exact inv_two_mul x (Work.Spaces.w x * h1 x)
        (Work.Spaces.w x * (x * deriv h1 x)
          + Work.Spaces.w x * h1 x * (1 / 2 - 2 / (1 + x))) hx0
    have hcont : ContinuousOn (fun x => 2 * (Work.Spaces.w x * h1 x)
        * (Work.Spaces.w x * (x * deriv h1 x)
          + Work.Spaces.w x * h1 x * (1 / 2 - 2 / (1 + x)))) (Set.Ioi 0) :=
      (continuousOn_const.mul (hc_w.mul hc_h1)).mul
        (((hc_w.mul (continuousOn_id.mul hc_d1)).add ((hc_w.mul hc_h1).mul hc_c)))
    have hsm : MeasureTheory.IntegrableOn (fun x => 2 * (Work.Spaces.w x * h1 x)
        * (Work.Spaces.w x * (x * deriv h1 x)
          + Work.Spaces.w x * h1 x * (1 / 2 - 2 / (1 + x)))) (Set.Ioi 0) := by
      refine Integrable.mono' hbd (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
      have hx0 : 0 < x := hx
      rw [Real.norm_eq_abs]
      calc |2 * (Work.Spaces.w x * h1 x)
            * (Work.Spaces.w x * (x * deriv h1 x)
              + Work.Spaces.w x * h1 x * ((1 : ℝ) / 2 - 2 / (1 + x)))|
          ≤ 4 * (Work.Spaces.w x * h1 x) ^ 2 + (Work.Spaces.w x * (x * deriv h1 x)) ^ 2 :=
            abs_two_mul_add_mul_le _ _ _ (c_abs_le x hx0)
        _ = 4 * ((Work.Spaces.w x) ^ 2 * h1 x ^ 2)
              + ((Work.Spaces.w x) ^ 2 * (x * deriv h1 x) ^ 2) := by ring
    exact hsm.congr heq.symm
  -- the decay of `F` and `G` at both ends
  have hF2deriv : ∀ x : ℝ, HasDerivAt (fun t => F t ^ 2) (2 * F x * F' x) x := by
    intro x
    have hd : DifferentiableAt ℝ (fun t => F t ^ 2) x := (hFderiv x).differentiableAt.fun_pow 2
    have h := hd.hasDerivAt
    refine h.congr_deriv ?_
    rw [deriv_fun_pow (hFderiv x).differentiableAt 2, (hFderiv x).deriv]
    ring
  have hG2deriv : ∀ x : ℝ, HasDerivAt (fun t => G t ^ 2) (2 * G x * G' x) x := by
    intro x
    have hd : DifferentiableAt ℝ (fun t => G t ^ 2) x := (hGderiv x).differentiableAt.fun_pow 2
    have h := hd.hasDerivAt
    refine h.congr_deriv ?_
    rw [deriv_fun_pow (hGderiv x).differentiableAt 2, (hGderiv x).deriv]
    ring
  have sq_tendsto_zero : ∀ {u : ℝ → ℝ} {l : Filter ℝ}
      (h : Filter.Tendsto (fun t => u t ^ 2) l (nhds 0)), Filter.Tendsto u l (nhds 0) := by
    intro u l h
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h2 : Filter.Tendsto (fun t => Real.sqrt (u t ^ 2)) l (nhds 0) := by
      have h3 := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp h
      simpa only [Function.comp_def, Real.sqrt_zero] using h3
    refine h2.congr' ?_
    filter_upwards with t
    rw [Real.norm_eq_abs, Real.sqrt_sq_eq_abs]
  have hFdecay : Filter.Tendsto F Filter.atBot (nhds 0) ∧
      Filter.Tendsto F Filter.atTop (nhds 0) := by
    have htop : Filter.Tendsto (fun t => F t ^ 2) Filter.atTop (nhds 0) :=
      tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := 0)
        (fun x _ => hF2deriv x) hFF'.integrableOn hF2.integrableOn
    have hbot : Filter.Tendsto (fun t => F t ^ 2) Filter.atBot (nhds 0) :=
      tendsto_zero_of_hasDerivAt_of_integrableOn_Iic (a := 0)
        (fun x _ => hF2deriv x) hFF'.integrableOn hF2.integrableOn
    exact ⟨sq_tendsto_zero hbot, sq_tendsto_zero htop⟩
  have hGdecay : Filter.Tendsto G Filter.atBot (nhds 0) ∧
      Filter.Tendsto G Filter.atTop (nhds 0) := by
    have htop : Filter.Tendsto (fun t => G t ^ 2) Filter.atTop (nhds 0) :=
      tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := 0)
        (fun x _ => hG2deriv x) hGG'.integrableOn hG2.integrableOn
    have hbot : Filter.Tendsto (fun t => G t ^ 2) Filter.atBot (nhds 0) :=
      tendsto_zero_of_hasDerivAt_of_integrableOn_Iic (a := 0)
        (fun x _ => hG2deriv x) hGG'.integrableOn hG2.integrableOn
    exact ⟨sq_tendsto_zero hbot, sq_tendsto_zero htop⟩
  -- assembly
  constructor
  · have h1' : Filter.Tendsto (fun z => F (Real.log z))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
      hFdecay.1.comp Real.tendsto_log_nhdsGT_zero
    have h2' : Filter.Tendsto (fun z => G (Real.log z))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
      hGdecay.1.comp Real.tendsto_log_nhdsGT_zero
    have hmul : Filter.Tendsto (fun z => F (Real.log z) * G (Real.log z))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      simpa only [mul_zero] using h1'.mul h2'
    refine hmul.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    simp only [hF, hG]
    exact profile_mul h h1 z hz
  · have h1' : Filter.Tendsto (fun z => F (Real.log z)) Filter.atTop (nhds 0) :=
      hFdecay.2.comp Real.tendsto_log_atTop
    have h2' : Filter.Tendsto (fun z => G (Real.log z)) Filter.atTop (nhds 0) :=
      hGdecay.2.comp Real.tendsto_log_atTop
    have hmul : Filter.Tendsto (fun z => F (Real.log z) * G (Real.log z))
        Filter.atTop (nhds 0) := by
      simpa only [mul_zero] using h1'.mul h2'
    refine hmul.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with z hz
    have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz
    simp only [hF, hG]
    exact profile_mul h h1 z hz0


/-- The boundary term `ρ z h h₁` vanishes at `0` and at `∞` for `h = rDzIter n g`. -/
private lemma boundary_rho (n : ℕ) (g : ℝ → ℝ) (hg : ContDiffOn ℝ ⊤ g (Set.Ioi 0))
    (hP : MeasureTheory.IntegrableOn (fun z => rho z * (rDzIter n g z) ^ 2) (Set.Ioi 0))
    (hX : MeasureTheory.IntegrableOn (fun z => rho z * (rDzIter (n + 1) g z) ^ 2) (Set.Ioi 0))
    (hR : MeasureTheory.IntegrableOn (fun z => rho z * (rDzIter (n + 2) g z) ^ 2) (Set.Ioi 0)) :
    Tendsto (fun z => rho z * z * rDzIter n g z * rDzIter (n + 1) g z)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Tendsto (fun z => rho z * z * rDzIter n g z * rDzIter (n + 1) g z) atTop (nhds 0) := by
  have hs : ContDiffOn ℝ ⊤ (rDzIter n g) (Set.Ioi 0) := rDzIter_contDiffOn_loc n g hg
  have hs1 : ContDiffOn ℝ ⊤ (rDzIter (n + 1) g) (Set.Ioi 0) :=
    rDzIter_contDiffOn_loc (n + 1) g hg
  have hd : ∀ z : ℝ, rDzIter (n + 1) g z = z * deriv (rDzIter n g) z := by
    intro z
    simp only [rDzIter_succ, rDz]
  have hR' : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * (z * deriv (rDzIter (n + 1) g) z) ^ 2)
      (Set.Ioi 0) := by
    have heq : (fun z => (Work.Spaces.w z) ^ 2 * (z * deriv (rDzIter (n + 1) g) z) ^ 2)
        = fun z => rho z * (rDzIter (n + 2) g z) ^ 2 := by
      funext z
      simp only [rho, rDzIter_succ, rDz]
    rw [heq]
    exact hR
  obtain ⟨h0, hT⟩ := boundary_tendsto (rDzIter n g) (rDzIter (n + 1) g) hs hs1 hd
    (by simpa only [rho] using hP) (by simpa only [rho] using hX) hR'
  exact ⟨by simpa only [rho] using h0, by simpa only [rho] using hT⟩

/-- The main theorem: the weighted Agmon interpolation for the radial derivative `D_z = z∂_z`,
uniformly in `α ∈ (0,1]`. -/
theorem zAMGM_Hk_le (n : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (g : ℝ → ℝ), ContDiffOn ℝ ⊤ g (Set.Ioi 0) →
      MeasureTheory.IntegrableOn
          (fun z => (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.rDzIter (n + 2) g z) ^ 2)
          Work.Spaces.Iz →
      MeasureTheory.IntegrableOn
          (fun z => (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.rDzIter n g z) ^ 2)
          Work.Spaces.Iz →
      α * Real.sqrt (∫ z in Work.Spaces.Iz,
              (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.rDzIter (n + 1) g z) ^ 2)
        ≤ C * (α ^ 2 * Real.sqrt (∫ z in Work.Spaces.Iz,
              (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.rDzIter (n + 2) g z) ^ 2)
          + Real.sqrt (∫ z in Work.Spaces.Iz,
              (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.rDzIter n g z) ^ 2)) := by
  refine ⟨4, by norm_num, ?_⟩
  intro α hα hα1 g hg hR hP
  -- integrability over `(0,∞)` versus over `[0,∞)` (the two differ by the null set `{0}`)
  have hiff : ∀ f : ℝ → ℝ, MeasureTheory.IntegrableOn f (Set.Ioi 0) ↔
      MeasureTheory.IntegrableOn f Work.Spaces.Iz := by
    intro f
    rw [Work.Spaces.Iz]
    exact (integrableOn_Ici_iff_integrableOn_Ioi (f := f) (b := 0)).symm
  by_cases hX : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.rDzIter (n + 1) g z) ^ 2)
      Work.Spaces.Iz
  · have hP' : MeasureTheory.IntegrableOn (fun z => rho z * (rDzIter n g z) ^ 2) (Set.Ioi 0) := by
      rw [hiff]
      simpa only [rho] using hP
    have hX' : MeasureTheory.IntegrableOn
        (fun z => rho z * (rDzIter (n + 1) g z) ^ 2) (Set.Ioi 0) := by
      rw [hiff]
      simpa only [rho] using hX
    have hR' : MeasureTheory.IntegrableOn
        (fun z => rho z * (rDzIter (n + 2) g z) ^ 2) (Set.Ioi 0) := by
      rw [hiff]
      simpa only [rho] using hR
    obtain ⟨hb0, hbT⟩ := boundary_rho n g hg hP' hX' hR'
    have hcore := zAMGM_core α hα hα1 (rDzIter n g) (rDzIter (n + 1) g) (rDzIter (n + 2) g)
      (fun z => rfl) (fun z => rfl)
      (rDzIter_contDiffOn_loc n g hg) (rDzIter_contDiffOn_loc (n + 1) g hg)
      (rDzIter_contDiffOn_loc (n + 2) g hg)
      hP' hX' hR' hb0 hbT
    -- transport the integrals along `Iz = Ici 0 =ᵐ Ioi 0`
    have hI : ∀ f : ℝ → ℝ, (∫ z in Work.Spaces.Iz, f z) = ∫ z in Set.Ioi (0 : ℝ), f z := by
      intro f
      rw [Work.Spaces.Iz]
      exact integral_Ici_eq_integral_Ioi
    rw [hI (fun z => (Work.Spaces.w z) ^ 2 * (rDzIter (n + 1) g z) ^ 2),
      hI (fun z => (Work.Spaces.w z) ^ 2 * (rDzIter (n + 2) g z) ^ 2),
      hI (fun z => (Work.Spaces.w z) ^ 2 * (rDzIter n g z) ^ 2)]
    refine hcore.trans (le_of_eq ?_)
    simp only [rho]
  · -- the middle integral is not honest: it is the junk value `0`
    have hzero : (∫ z in Work.Spaces.Iz,
        (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.rDzIter (n + 1) g z) ^ 2) = 0 := by
      rw [integral_undef]
      exact hX
    rw [hzero, Real.sqrt_zero, mul_zero]
    have h2 : 0 ≤ α ^ 2 * Real.sqrt (∫ z in Work.Spaces.Iz,
        (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.rDzIter (n + 2) g z) ^ 2) :=
      mul_nonneg (sq_nonneg α) (Real.sqrt_nonneg _)
    have h3 : 0 ≤ Real.sqrt (∫ z in Work.Spaces.Iz,
        (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.rDzIter n g z) ^ 2) :=
      Real.sqrt_nonneg _
    nlinarith [h2, h3]

end Work.FTS.EllipticEst
