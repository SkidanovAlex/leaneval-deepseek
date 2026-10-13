/-
Copyright: work module for the Elgindi finite-time singularity project.

# Quantitative `θ`-endpoint growth of an angular slice, normalized by the data at `π/4`

This module sharpens `Work.FTS.EllipticEst.H2W.lzeroGrowthBound`.  There the growth bound

  `|u θ| ≤ C_u · (θ⁻¹ + (π/2 - θ)⁻¹)`

was proved with a constant `C_u` that *depends on* `u` (it is built from the Cramer
coefficients `c₁, c₂` of `u` evaluated at the middle point `π/4`).  Here we prove the
*quantitative, uniform* version: there is a universal constant `C` with

  `|u θ| ≤ C · (∫_{Iθ} sin s cos²s |Lzero1 u s| + |u (π/4)| + |deriv u (π/4)|)
              · (θ⁻¹ + (π/2 - θ)⁻¹)`

for every `u` of class `C^∞` on `(0, π/2)` whose weighted source mass is finite.  This is the
form in which the bound is consumed downstream: the right-hand side is a functional of the
*data* (`Lzero1 u` together with the two values at `π/4`), not of `u`'s unknown coefficients.

## The argument

Everything is the argument of `lzeroGrowthBound`, run with the coefficients bounded instead of
evaluated.  On `(0, π/2)` the operator `Lzero1` has the two fundamental solutions
`y₁ = sin 2θ` and `y₂ = LzeroSing` (the singular solution, with `|y₂ θ · cos θ| ≤ B₀` for a
universal `B₀`), with Wronskian `wron y₁ y₂ = -1/cos θ`.  Writing `g = Lzero1 u` and

  `c₁ = -wron(u, y₂)·cos θ`,   `c₂ = -wron(y₁, u)·cos θ`,

one has the exact Cramer representation `u = c₁ y₁ + c₂ y₂`, the exact derivative identities
`c₂' = 2 g ψ`, `c₁' = -g y₂ cos θ` (`ψ = sin θ cos²θ`), and hence

  `|c₂ θ| ≤ |c₂(π/4)| + 2 K`,   `|c₂(π/4)| ≤ |u (π/4)| + |deriv u (π/4)|`,
  `|c₁ θ| ≤ |c₁(π/4)| + B₀ · (weighted mass over a subinterval)`,
  `|c₁(π/4)| ≤ |u (π/4)| + |deriv u (π/4)|`,

where `K = ∫_{Iθ} ψ |g|`.  The last two coefficient bounds are the new input: at the *middle
point* `θ = π/4` the integral in the definition of `LzeroSing` is empty, so
`LzeroSing (π/4) = 0` and `deriv LzeroSing (π/4) = -√2` (the derivative value is `SingY1 (π/4)`),
whence `wron u LzeroSing (π/4) = -√2 · u (π/4)` and
`wron (sin 2·) u (π/4) = deriv u (π/4)`, giving `c₁(π/4) = u (π/4)` and
`c₂(π/4) = -(√2/2)·deriv u (π/4)`.

The two cases `θ ≤ π/4`, `θ ≥ π/4` are converted into the weighted mass `K` with the pointwise
lower bounds `ψ ≥ θ/π` resp. `ψ ≥ (2√2/π²)(π/2-θ)²` (`Lzb.WeightCompare`), the trivial
`|sin 2θ| ≤ 2 min(θ, π/2-θ)`, and `1/cos θ ≤ (π/2)/(π/2-θ)` (`inv_cos_le`); the bookkeeping
inequalities are exactly `arith_left`/`arith_right` of `lzeroGrowthBound`, whose constants
`4|c₁(π/4)| + 16 B₀ K + 2(|c₂(π/4)| + 2K) B₀` are now bounded by `(4 + 22 B₀)(K + |u π/4| +
|deriv u (π/4)|)`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllipticEst.H2W.lzeroGrowthBound
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.SliceB

/-! ## The values of `LzeroSing` and of its derivative at `π/4` -/

/-- `LzeroSing` has derivative `SingY1` on the open angular interval (product rule + FTC). -/
theorem hasDerivAt_LzeroSing_SingY1 : ∀ τ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
    HasDerivAt Work.FTS.EllipticEst.LzeroSing (Work.FTS.EllipticEst.SingY1 τ) τ := by
  intro τ hτ
  have hlin : HasDerivAt (fun t : ℝ => (2 : ℝ) * t) 2 τ := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id τ).const_mul 2
  have hsin : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (2 * Real.cos (2 * τ)) τ :=
    ((Real.hasDerivAt_sin (2 * τ)).comp τ hlin).congr_deriv (by ring)
  have hint : HasDerivAt Work.FTS.EllipticEst.SingInt
      (-(Work.FTS.EllipticEst.LzeroSingIntegrand (Real.pi / 2 - τ))) τ :=
    Work.FTS.EllipticEst.SingInt_hasDerivAt τ hτ
  have hval : 2 * Real.cos (2 * τ) * Work.FTS.EllipticEst.SingInt τ
      + Real.sin (2 * τ) * (-(Work.FTS.EllipticEst.LzeroSingIntegrand (Real.pi / 2 - τ)))
      = Work.FTS.EllipticEst.SingY1 τ := by
    rw [Work.FTS.EllipticEst.SingY1_apply,
      ← Work.FTS.EllipticEst.LzeroAux.sin_mul_integrand τ hτ]
    ring
  rw [show Work.FTS.EllipticEst.LzeroSing
      = fun t : ℝ => Real.sin (2 * t) * Work.FTS.EllipticEst.SingInt t from
    funext fun t => Work.FTS.EllipticEst.LzeroSing_eq_sin_mul_SingInt t]
  exact (hsin.mul hint).congr_deriv hval

/-- `LzeroSing (π/4) = 0`: the reduction-of-order integral is empty there. -/
theorem LzeroSing_pi4 : Work.FTS.EllipticEst.LzeroSing (Real.pi / 4) = 0 := by
  rw [Work.FTS.EllipticEst.LzeroSing_eq_sin_mul_SingInt]
  have h : Real.pi / 2 - Real.pi / 4 = Real.pi / 4 := by ring
  simp [Work.FTS.EllipticEst.SingInt, h]

/-- `deriv LzeroSing (π/4) = -√2` (the value `SingY1 (π/4) = -1/cos(π/4)`). -/
theorem deriv_LzeroSing_pi4 :
    deriv Work.FTS.EllipticEst.LzeroSing (Real.pi / 4) = -Real.sqrt 2 := by
  have hmem : (Real.pi / 4) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  have h := (hasDerivAt_LzeroSing_SingY1 (Real.pi / 4) hmem).deriv
  rw [h, Work.FTS.EllipticEst.SingY1_apply]
  have hS : Work.FTS.EllipticEst.SingInt (Real.pi / 4) = 0 := by
    have h : Real.pi / 2 - Real.pi / 4 = Real.pi / 4 := by ring
    simp [Work.FTS.EllipticEst.SingInt, h]
  rw [hS]
  have h2 : 2 * (Real.pi / 4) = Real.pi / 2 := by ring
  rw [h2, Real.cos_pi_div_two, Real.sin_pi_div_two, Real.cos_pi_div_four, mul_one, mul_zero,
    zero_sub]
  have hsqrt : (1 : ℝ) / (Real.sqrt 2 / 2) = Real.sqrt 2 := by
    have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := by
      have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      rw [sq] at h
      exact h
    field_simp
    linarith
  rw [hsqrt]

/-- `√2 · √2 = 2`. -/
private theorem sq_sqrt_two : Real.sqrt 2 * Real.sqrt 2 = 2 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  rw [sq] at h
  exact h

/-- `deriv (sin 2·) (π/4) = 0`, since `cos (π/2) = 0`. -/
private theorem deriv_sin_two_pi4 :
    deriv (fun t : ℝ => Real.sin (2 * t)) (Real.pi / 4) = 0 := by
  have hlin : HasDerivAt (fun t : ℝ => (2 : ℝ) * t) 2 (Real.pi / 4) := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id (Real.pi / 4)).const_mul 2
  have hsin : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (2 * Real.cos (2 * (Real.pi / 4)))
      (Real.pi / 4) :=
    ((Real.hasDerivAt_sin (2 * (Real.pi / 4))).comp (Real.pi / 4) hlin).congr_deriv (by ring)
  rw [hsin.deriv]
  have h2 : 2 * (Real.pi / 4) = Real.pi / 2 := by ring
  rw [h2, Real.cos_pi_div_two, mul_zero]

/-- **The two Cramer coefficients at the middle point.**  Since `LzeroSing (π/4) = 0` and
`deriv LzeroSing (π/4) = -√2`, the Cramer representation `u = c₁ sin 2θ + c₂ LzeroSing` has
coefficients `c₁(π/4) = u (π/4)` and `c₂(π/4) = -(√2/2)·deriv u (π/4)` there, so both are
dominated by `|u (π/4)| + |deriv u (π/4)|` — with no regularity hypothesis on `u`. -/
theorem cCoefPi4Bound (u : ℝ → ℝ) :
    |Work.FTS.EllipticEst.H2W.cCoef1 u (Real.pi / 4)|
        ≤ |u (Real.pi / 4)| + |deriv u (Real.pi / 4)|
      ∧ |Work.FTS.EllipticEst.H2W.cCoef2 u (Real.pi / 4)|
        ≤ |u (Real.pi / 4)| + |deriv u (Real.pi / 4)| := by
  have hsin2val : Real.sin (2 * (Real.pi / 4)) = 1 := by
    have h2 : 2 * (Real.pi / 4) = Real.pi / 2 := by ring
    rw [h2, Real.sin_pi_div_two]
  have hcos4 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
  have hcos4pos : 0 < Real.cos (Real.pi / 4) := by rw [hcos4]; positivity
  have hc1 : Work.FTS.EllipticEst.H2W.cCoef1 u (Real.pi / 4) = u (Real.pi / 4) := by
    simp only [Work.FTS.EllipticEst.H2W.cCoef1, Work.FTS.EllipticEst.H2W.wron,
      deriv_LzeroSing_pi4, LzeroSing_pi4]
    rw [mul_zero, sub_zero, hcos4]
    linear_combination (u (Real.pi / 4) / 2) * sq_sqrt_two
  have hc2 : Work.FTS.EllipticEst.H2W.cCoef2 u (Real.pi / 4)
      = -(deriv u (Real.pi / 4) * Real.cos (Real.pi / 4)) := by
    simp only [Work.FTS.EllipticEst.H2W.cCoef2, Work.FTS.EllipticEst.H2W.wron,
      deriv_sin_two_pi4, hsin2val]
    ring
  constructor
  · rw [hc1]
    linarith [abs_nonneg (deriv u (Real.pi / 4))]
  · rw [hc2, abs_neg, abs_mul, abs_of_pos hcos4pos]
    have hle : Real.cos (Real.pi / 4) ≤ 1 := by
      rw [hcos4]
      nlinarith [sq_sqrt_two, Real.sqrt_nonneg 2]
    have hstep : Real.cos (Real.pi / 4) * |deriv u (Real.pi / 4)| ≤ |deriv u (Real.pi / 4)| :=
      mul_le_of_le_one_left (abs_nonneg _) hle
    have hstep' : |deriv u (Real.pi / 4)| * Real.cos (Real.pi / 4) ≤ |deriv u (Real.pi / 4)| := by
      simpa only [mul_comm] using hstep
    linarith [hstep', abs_nonneg (u (Real.pi / 4))]

/-! ## The growth of the singular solution -/

/-- The singular solution grows at most like `1/cos` at the angular endpoint:
`|LzeroSing θ| ≤ B₀ (π/2)(π/2 - θ)⁻¹` whenever `|LzeroSing θ · cos θ| ≤ B₀`.  This is Jordan's
inequality `cos θ ≥ (2/π)(π/2 - θ)` (`inv_cos_le`). -/
theorem LzeroSing_cos_growth {B0 : ℝ} (hB0nn : 0 ≤ B0)
    (hB0 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.FTS.EllipticEst.LzeroSing θ * Real.cos θ| ≤ B0) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.FTS.EllipticEst.LzeroSing θ| ≤ B0 * ((Real.pi / 2) * (Real.pi / 2 - θ)⁻¹) := by
  intro θ hθ
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hb : |Work.FTS.EllipticEst.LzeroSing θ| * Real.cos θ ≤ B0 := by
    have h := hB0 θ hθ
    rwa [abs_mul, abs_of_pos hcos] at h
  calc |Work.FTS.EllipticEst.LzeroSing θ| ≤ B0 / Real.cos θ := (le_div_iff₀ hcos).mpr hb
    _ = B0 * (Real.cos θ)⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ B0 * ((Real.pi / 2) * (Real.pi / 2 - θ)⁻¹) :=
        mul_le_mul_of_nonneg_left (inv_cos_le hθ) hB0nn

/-! ## The general two-coefficient growth estimate -/

/-- **The quantitative growth estimate**, with the two Cramer coefficients at `π/4` replaced by
arbitrary upper bounds `Y₁`, `Y₂`.  This is the body of `lzeroGrowthBound`'s proof, with the
pointwise coefficients `|c₁(π/4)|`, `|c₂(π/4)|` abstracted into `Y₁`, `Y₂` (which is what makes
the resulting constant uniform in `u`). -/
theorem growth_bound_general {u : ℝ → ℝ} {B0 Y1 Y2 : ℝ}
    (hu2 : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hder1 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (cCoef1 u)
        (-(Work.FTS.EllipticEst.Lzero1 u θ * Work.FTS.EllipticEst.LzeroSing θ
            * Real.cos θ)) θ)
    (hder2 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (cCoef2 u)
        (Work.FTS.EllipticEst.Lzero1 u θ * Real.sin (2 * θ) * Real.cos θ) θ)
    (hint : IntegrableOn (fun s => psiW s * |Work.FTS.EllipticEst.Lzero1 u s|)
      Work.Spaces.Iθ)
    (hB0pos : 0 < B0)
    (hB0 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.FTS.EllipticEst.LzeroSing θ * Real.cos θ| ≤ B0)
    (hY1 : |cCoef1 u (Real.pi / 4)| ≤ Y1)
    (hY2 : |cCoef2 u (Real.pi / 4)| ≤ Y2) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |u θ| ≤ (4 * Y1 + 16 * B0 * (∫ s in Work.Spaces.Iθ, psiW s * |Lzero1 u s|)
          + 2 * (Y2 + 2 * (∫ s in Work.Spaces.Iθ, psiW s * |Lzero1 u s|)) * B0)
        * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹) := by
  intro θ hθ
  set K : ℝ := ∫ s in Work.Spaces.Iθ, psiW s * |Work.FTS.EllipticEst.Lzero1 u s| with hKdef
  have hKnn : 0 ≤ K := by
    rw [hKdef]
    refine MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun s hs => ?_)
    exact mul_nonneg (psiW_nonneg hs) (abs_nonneg _)
  have hB0nn : 0 ≤ B0 := le_of_lt hB0pos
  have hY1nn : 0 ≤ Y1 := le_trans (abs_nonneg _) hY1
  have hY2nn : 0 ≤ Y2 := le_trans (abs_nonneg _) hY2
  have hθ0 : (0 : ℝ) < θ := hθ.1
  have hθπ : θ < Real.pi / 2 := hθ.2
  have hτ : 0 < Real.pi / 2 - θ := by linarith
  have hinv : 1 ≤ θ⁻¹ + (Real.pi / 2 - θ)⁻¹ := one_le_inv_add hθ
  have hC2nn : 0 ≤ Y2 + 2 * K := by linarith
  have hcramer := cramer_id u hθ
  have hy2 : |Work.FTS.EllipticEst.LzeroSing θ|
      ≤ B0 * ((Real.pi / 2) * (Real.pi / 2 - θ)⁻¹) :=
    LzeroSing_cos_growth hB0nn hB0 θ hθ
  have hc2 : |cCoef2 u θ| ≤ Y2 + 2 * K := by
    have h := abs_cCoef2_sub_le hu2 hder2 hint hθ
    have h' : |cCoef2 u θ - cCoef2 u (Real.pi / 4)| ≤ 2 * K := by
      rw [hKdef]
      exact h
    calc |cCoef2 u θ|
        = |cCoef2 u (Real.pi / 4) + (cCoef2 u θ - cCoef2 u (Real.pi / 4))| := by ring_nf
      _ ≤ |cCoef2 u (Real.pi / 4)| + |cCoef2 u θ - cCoef2 u (Real.pi / 4)| := abs_add_le _ _
      _ ≤ Y2 + 2 * K := by linarith
  rcases le_total θ (Real.pi / 4) with hle | hge
  · -- Case `θ ≤ π/4`
    have hy1 : |Real.sin (2 * θ)| ≤ 2 * θ := by
      rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
        (by linarith [Real.pi_pos]))]
      exact sin_two_mul_le_two_mul (by linarith)
    have hc1 : |cCoef1 u θ| ≤ Y1 + B0 * ((Real.pi / θ) * K) := by
      have h := abs_cCoef1_sub_le_left hu2 hder1 hint hB0nn hB0 hθ0 hle
      have h' : |cCoef1 u θ - cCoef1 u (Real.pi / 4)| ≤ B0 * ((Real.pi / θ) * K) := by
        rw [hKdef]
        exact h
      calc |cCoef1 u θ|
          = |cCoef1 u (Real.pi / 4) + (cCoef1 u θ - cCoef1 u (Real.pi / 4))| := by ring_nf
        _ ≤ |cCoef1 u (Real.pi / 4)| + |cCoef1 u θ - cCoef1 u (Real.pi / 4)| := abs_add_le _ _
        _ ≤ Y1 + B0 * ((Real.pi / θ) * K) := by linarith
    have hsum : |u θ| ≤ (Y1 + B0 * ((Real.pi / θ) * K)) * (2 * θ)
        + (Y2 + 2 * K) * (B0 * ((Real.pi / 2) * (Real.pi / 2 - θ)⁻¹)) := by
      calc |u θ| = |cCoef1 u θ * Real.sin (2 * θ)
            + cCoef2 u θ * Work.FTS.EllipticEst.LzeroSing θ| := by rw [hcramer]
        _ ≤ |cCoef1 u θ * Real.sin (2 * θ)|
              + |cCoef2 u θ * Work.FTS.EllipticEst.LzeroSing θ| := abs_add_le _ _
        _ = |cCoef1 u θ| * |Real.sin (2 * θ)|
              + |cCoef2 u θ| * |Work.FTS.EllipticEst.LzeroSing θ| := by rw [abs_mul, abs_mul]
        _ ≤ (Y1 + B0 * ((Real.pi / θ) * K)) * (2 * θ)
              + (Y2 + 2 * K) * (B0 * ((Real.pi / 2) * (Real.pi / 2 - θ)⁻¹)) := by
            have h1 : |cCoef1 u θ| * |Real.sin (2 * θ)|
                ≤ (Y1 + B0 * ((Real.pi / θ) * K)) * (2 * θ) :=
              mul_le_mul hc1 hy1 (abs_nonneg _) (by positivity)
            have h2 : |cCoef2 u θ| * |Work.FTS.EllipticEst.LzeroSing θ|
                ≤ (Y2 + 2 * K) * (B0 * ((Real.pi / 2) * (Real.pi / 2 - θ)⁻¹)) :=
              mul_le_mul hc2 hy2 (abs_nonneg _) (by positivity)
            linarith
    have hEq : (Y1 + B0 * ((Real.pi / θ) * K)) * (2 * θ)
        + (Y2 + 2 * K) * (B0 * ((Real.pi / 2) * (Real.pi / 2 - θ)⁻¹))
        = 2 * Y1 * θ + 2 * B0 * Real.pi * K
          + (Y2 + 2 * K) * (B0 * (Real.pi / 2)) * (Real.pi / 2 - θ)⁻¹ := by
      field_simp
    have harith := arith_left (C1 := Y1) (C2 := Y2 + 2 * K) (B0 := B0) (K := K) (θ := θ)
      (τ := Real.pi / 2 - θ) hY1nn hC2nn hB0nn hKnn hθ0 hτ
      (by linarith [hle, Real.pi_lt_four]) hinv
    calc |u θ| ≤ (Y1 + B0 * ((Real.pi / θ) * K)) * (2 * θ)
          + (Y2 + 2 * K) * (B0 * ((Real.pi / 2) * (Real.pi / 2 - θ)⁻¹)) := hsum
      _ = 2 * Y1 * θ + 2 * B0 * Real.pi * K
          + (Y2 + 2 * K) * (B0 * (Real.pi / 2)) * (Real.pi / 2 - θ)⁻¹ := hEq
      _ ≤ (4 * Y1 + 16 * B0 * K + 2 * (Y2 + 2 * K) * B0)
          * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹) := harith
  · -- Case `θ ≥ π/4`
    have hy1 : |Real.sin (2 * θ)| ≤ 2 * (Real.pi / 2 - θ) := by
      rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
        (by linarith [Real.pi_pos]))]
      exact sin_two_mul_le_two_sub hge (le_of_lt hθπ)
    have hc1 : |cCoef1 u θ|
        ≤ Y1 + B0 * ((Real.pi ^ 2 / (2 * Real.sqrt 2 * (Real.pi / 2 - θ) ^ 2)) * K) := by
      have h := abs_cCoef1_sub_le_right hu2 hder1 hint hB0nn hB0 hge hθπ
      have h' : |cCoef1 u θ - cCoef1 u (Real.pi / 4)|
          ≤ B0 * ((Real.pi ^ 2 / (2 * Real.sqrt 2 * (Real.pi / 2 - θ) ^ 2)) * K) := by
        rw [hKdef]
        exact h
      calc |cCoef1 u θ|
          = |cCoef1 u (Real.pi / 4) + (cCoef1 u θ - cCoef1 u (Real.pi / 4))| := by ring_nf
        _ ≤ |cCoef1 u (Real.pi / 4)| + |cCoef1 u θ - cCoef1 u (Real.pi / 4)| := abs_add_le _ _
        _ ≤ Y1 + B0 * ((Real.pi ^ 2 / (2 * Real.sqrt 2 * (Real.pi / 2 - θ) ^ 2)) * K) := by
            linarith
    have hsum : |u θ|
        ≤ (Y1 + B0 * ((Real.pi ^ 2 / (2 * Real.sqrt 2 * (Real.pi / 2 - θ) ^ 2)) * K))
            * (2 * (Real.pi / 2 - θ))
          + (Y2 + 2 * K) * (B0 * ((Real.pi / 2) * (Real.pi / 2 - θ)⁻¹)) := by
      calc |u θ| = |cCoef1 u θ * Real.sin (2 * θ)
            + cCoef2 u θ * Work.FTS.EllipticEst.LzeroSing θ| := by rw [hcramer]
        _ ≤ |cCoef1 u θ * Real.sin (2 * θ)|
              + |cCoef2 u θ * Work.FTS.EllipticEst.LzeroSing θ| := abs_add_le _ _
        _ = |cCoef1 u θ| * |Real.sin (2 * θ)|
              + |cCoef2 u θ| * |Work.FTS.EllipticEst.LzeroSing θ| := by rw [abs_mul, abs_mul]
        _ ≤ (Y1 + B0 * ((Real.pi ^ 2 / (2 * Real.sqrt 2 * (Real.pi / 2 - θ) ^ 2)) * K))
              * (2 * (Real.pi / 2 - θ))
              + (Y2 + 2 * K) * (B0 * ((Real.pi / 2) * (Real.pi / 2 - θ)⁻¹)) := by
            have h1 : |cCoef1 u θ| * |Real.sin (2 * θ)|
                ≤ (Y1 + B0 * ((Real.pi ^ 2 / (2 * Real.sqrt 2 * (Real.pi / 2 - θ) ^ 2)) * K))
                  * (2 * (Real.pi / 2 - θ)) :=
              mul_le_mul hc1 hy1 (abs_nonneg _) (by positivity)
            have h2 : |cCoef2 u θ| * |Work.FTS.EllipticEst.LzeroSing θ|
                ≤ (Y2 + 2 * K) * (B0 * ((Real.pi / 2) * (Real.pi / 2 - θ)⁻¹)) :=
              mul_le_mul hc2 hy2 (abs_nonneg _) (by positivity)
            linarith
    have hEq : (Y1 + B0 * ((Real.pi ^ 2 / (2 * Real.sqrt 2 * (Real.pi / 2 - θ) ^ 2)) * K))
        * (2 * (Real.pi / 2 - θ))
        + (Y2 + 2 * K) * (B0 * ((Real.pi / 2) * (Real.pi / 2 - θ)⁻¹))
        = 2 * Y1 * (Real.pi / 2 - θ)
          + B0 * (Real.pi ^ 2 / Real.sqrt 2) * K * (Real.pi / 2 - θ)⁻¹
          + (Y2 + 2 * K) * (B0 * (Real.pi / 2)) * (Real.pi / 2 - θ)⁻¹ := by
      have hc2t : (Real.pi ^ 2 / (2 * Real.sqrt 2 * (Real.pi / 2 - θ) ^ 2))
          * (2 * (Real.pi / 2 - θ)) = (Real.pi ^ 2 / Real.sqrt 2) * (Real.pi / 2 - θ)⁻¹ := by
        have hs2 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
        have hτne : Real.pi / 2 - θ ≠ 0 := ne_of_gt hτ
        field_simp
      have hsplit : (Y1 + B0 * ((Real.pi ^ 2 / (2 * Real.sqrt 2 * (Real.pi / 2 - θ) ^ 2)) * K))
          * (2 * (Real.pi / 2 - θ))
          = Y1 * (2 * (Real.pi / 2 - θ))
            + B0 * K * ((Real.pi ^ 2 / Real.sqrt 2) * (Real.pi / 2 - θ)⁻¹) := by
        rw [show (Y1 + B0 * ((Real.pi ^ 2 / (2 * Real.sqrt 2 * (Real.pi / 2 - θ) ^ 2)) * K))
            * (2 * (Real.pi / 2 - θ))
            = Y1 * (2 * (Real.pi / 2 - θ))
              + B0 * K * ((Real.pi ^ 2 / (2 * Real.sqrt 2 * (Real.pi / 2 - θ) ^ 2))
                  * (2 * (Real.pi / 2 - θ))) by ring,
          hc2t]
      rw [hsplit]
      ring
    have harith := arith_right (C1 := Y1) (C2 := Y2 + 2 * K) (B0 := B0) (K := K) (θ := θ)
      (τ := Real.pi / 2 - θ) hY1nn hC2nn hB0nn hKnn hθ0 hτ
      (by linarith [hge, Real.pi_lt_four]) hinv
    calc |u θ|
        ≤ (Y1 + B0 * ((Real.pi ^ 2 / (2 * Real.sqrt 2 * (Real.pi / 2 - θ) ^ 2)) * K))
            * (2 * (Real.pi / 2 - θ))
          + (Y2 + 2 * K) * (B0 * ((Real.pi / 2) * (Real.pi / 2 - θ)⁻¹)) := hsum
      _ = 2 * Y1 * (Real.pi / 2 - θ)
          + B0 * (Real.pi ^ 2 / Real.sqrt 2) * K * (Real.pi / 2 - θ)⁻¹
          + (Y2 + 2 * K) * (B0 * (Real.pi / 2)) * (Real.pi / 2 - θ)⁻¹ := hEq
      _ ≤ (4 * Y1 + 16 * B0 * K + 2 * (Y2 + 2 * K) * B0)
          * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹) := harith

/-! ## The integral over `Iθ` of an integrand carrying constant terms -/

/-- Over `Iθ = [0, π/2]` (measure `π/2`), the integral of `f + a + b` is `∫ f + (π/2)(a + b)`:
the two constants integrate against the full measure of `Iθ`. -/
theorem setIntegral_Itheta_add_const {f : ℝ → ℝ} (a b : ℝ)
    (hf : IntegrableOn f Work.Spaces.Iθ) :
    (∫ s in Work.Spaces.Iθ, f s + a + b)
      = (∫ s in Work.Spaces.Iθ, f s) + (Real.pi / 2) * (a + b) := by
  have hvol : volume.real Work.Spaces.Iθ = Real.pi / 2 := by
    rw [MeasureTheory.measureReal_def, Work.Spaces.Iθ, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith [Real.pi_pos]), sub_zero]
  have hconst : ∀ c : ℝ, (∫ s in Work.Spaces.Iθ, c) = c * (Real.pi / 2) := by
    intro c
    rw [MeasureTheory.setIntegral_const, smul_eq_mul, hvol]
    ring
  have hvolne : volume Work.Spaces.Iθ ≠ ⊤ := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have ha : IntegrableOn (fun _ : ℝ => a) Work.Spaces.Iθ :=
    integrableOn_const hvolne (by simp)
  have hb : IntegrableOn (fun _ : ℝ => b) Work.Spaces.Iθ :=
    integrableOn_const hvolne (by simp)
  have h1 : IntegrableOn (fun s : ℝ => f s + a) Work.Spaces.Iθ := hf.add ha
  rw [MeasureTheory.integral_add h1 hb, MeasureTheory.integral_add hf ha,
    hconst a, hconst b]
  ring

/-! ## The target -/

theorem lzeroGrowthQuantL1 : ∃ C : ℝ, 0 < C ∧ ∀ (u : ℝ → ℝ),
    (∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2))) →
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2 * |Work.FTS.EllipticEst.Lzero1 u θ|)
      Work.Spaces.Iθ →
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |u θ| ≤ C * (∫ s in Work.Spaces.Iθ,
            Real.sin s * Real.cos s ^ 2 * |Work.FTS.EllipticEst.Lzero1 u s|
          + |u (Real.pi / 4)| + |deriv u (Real.pi / 4)|)
        * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹) := by
  obtain ⟨B0, hB0pos, hB0⟩ := Lzb.LzeroSingCosBoundClean
  refine ⟨4 + 22 * B0, by positivity, ?_⟩
  intro u hu hint θ hθ
  have hu2 : ContDiffOn ℝ 2 u (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hu 2
  obtain ⟨hwr1, hwr2⟩ := Lzb.WronDerivs hu2
  have hder1 := hasDerivAt_cCoef1 (u := u) hwr1
  have hder2 := hasDerivAt_cCoef2 (u := u) hwr2
  have hψint : IntegrableOn (fun s => psiW s * |Work.FTS.EllipticEst.Lzero1 u s|)
      Work.Spaces.Iθ := by
    simpa only [psiW] using hint
  have hB0nn : 0 ≤ B0 := le_of_lt hB0pos
  have hmain := growth_bound_general (u := u) (B0 := B0)
    (Y1 := |u (Real.pi / 4)| + |deriv u (Real.pi / 4)|)
    (Y2 := |u (Real.pi / 4)| + |deriv u (Real.pi / 4)|)
    hu2 hder1 hder2 hψint hB0pos hB0 (cCoefPi4Bound u).1 (cCoefPi4Bound u).2 θ hθ
  have hKnn : 0 ≤ (∫ s in Work.Spaces.Iθ, psiW s * |Work.FTS.EllipticEst.Lzero1 u s|) := by
    refine MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun s hs => ?_)
    exact mul_nonneg (psiW_nonneg hs) (abs_nonneg _)
  have hWnn : 0 ≤ |u (Real.pi / 4)| + |deriv u (Real.pi / 4)| := by positivity
  have hconst : 4 * (|u (Real.pi / 4)| + |deriv u (Real.pi / 4)|)
      + 16 * B0 * (∫ s in Work.Spaces.Iθ, psiW s * |Work.FTS.EllipticEst.Lzero1 u s|)
      + 2 * ((|u (Real.pi / 4)| + |deriv u (Real.pi / 4)|)
          + 2 * (∫ s in Work.Spaces.Iθ, psiW s * |Work.FTS.EllipticEst.Lzero1 u s|)) * B0
      ≤ (4 + 22 * B0) * ((∫ s in Work.Spaces.Iθ, psiW s * |Work.FTS.EllipticEst.Lzero1 u s|)
          + (|u (Real.pi / 4)| + |deriv u (Real.pi / 4)|)) := by
    nlinarith [hKnn, hWnn, hB0nn]
  have hsumpos : 0 ≤ θ⁻¹ + (Real.pi / 2 - θ)⁻¹ := by
    have hθ0 : (0 : ℝ) < θ := hθ.1
    have hτ : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
    positivity
  have key : |u θ| ≤ (4 + 22 * B0) * ((∫ s in Work.Spaces.Iθ,
        psiW s * |Work.FTS.EllipticEst.Lzero1 u s|)
      + (|u (Real.pi / 4)| + |deriv u (Real.pi / 4)|)) * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹) :=
    le_trans hmain (mul_le_mul_of_nonneg_right hconst hsumpos)
  have hWle : (|u (Real.pi / 4)| + |deriv u (Real.pi / 4)|)
      ≤ (Real.pi / 2) * (|u (Real.pi / 4)| + |deriv u (Real.pi / 4)|) := by
    nlinarith [hWnn, Real.pi_gt_three]
  have hJ : (∫ s in Work.Spaces.Iθ,
        Real.sin s * Real.cos s ^ 2 * |Work.FTS.EllipticEst.Lzero1 u s|
          + |u (Real.pi / 4)| + |deriv u (Real.pi / 4)|)
      = (∫ s in Work.Spaces.Iθ, psiW s * |Work.FTS.EllipticEst.Lzero1 u s|)
        + (Real.pi / 2) * (|u (Real.pi / 4)| + |deriv u (Real.pi / 4)|) := by
    have h := setIntegral_Itheta_add_const
      (f := fun s => psiW s * |Work.FTS.EllipticEst.Lzero1 u s|)
      (|u (Real.pi / 4)|) (|deriv u (Real.pi / 4)|) hψint
    simpa only [psiW] using h
  have hKW : (∫ s in Work.Spaces.Iθ, psiW s * |Work.FTS.EllipticEst.Lzero1 u s|)
        + (|u (Real.pi / 4)| + |deriv u (Real.pi / 4)|)
      ≤ (∫ s in Work.Spaces.Iθ,
        Real.sin s * Real.cos s ^ 2 * |Work.FTS.EllipticEst.Lzero1 u s|
          + |u (Real.pi / 4)| + |deriv u (Real.pi / 4)|) := by
    rw [hJ]
    linarith [hWle]
  have hC0nn : 0 ≤ 4 + 22 * B0 := by positivity
  calc |u θ| ≤ (4 + 22 * B0) * ((∫ s in Work.Spaces.Iθ,
        psiW s * |Work.FTS.EllipticEst.Lzero1 u s|)
      + (|u (Real.pi / 4)| + |deriv u (Real.pi / 4)|)) * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹) := key
    _ ≤ ((4 + 22 * B0) * (∫ s in Work.Spaces.Iθ,
          Real.sin s * Real.cos s ^ 2 * |Work.FTS.EllipticEst.Lzero1 u s|
            + |u (Real.pi / 4)| + |deriv u (Real.pi / 4)|))
        * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKW hC0nn) hsumpos

end Work.FTS.EllipticEst.H2W.SliceB
