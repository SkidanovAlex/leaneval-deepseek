import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.OneBodyKin.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.OneBodyKin.profHat_add_sub_linear_le` — the second-order Taylor bound for `profHat`

The bump profile `profHat p = ∫_z χ z · cos⟪p,z⟫ dz` is `C²` with

    `profHat (y+d) - profHat y = ⟪∇profHat y, d⟫ + O(‖d‖²)`,

and since `∇profHat y = -∫_z χ z sin⟪y,z⟫ · z dz`, the linear term is
`-∫_z χ z (inner d z) sin(inner y z)`.  The lemma below is the *quantitative* form of this
Taylor expansion, with the explicit second-order constant `∫_z |χ z| ‖z‖² dz`:

    `|profHat (y+d) - profHat y + ∫_z χ z (inner d z) sin(inner y z)| ≤ (∫_z |χ z| ‖z‖²) ‖d‖²`.

It is the `y`-regularity input for the second-order expansion of `symA`/`symD` in the symbol
bound `Work.OneBodyKin.SymBound` of this chapter (`symA_second_order`, `symD_second_order`).

## The proof, in three steps

1. **The integral identity.**  Unfolding `profHat`, using `∫f - ∫g = ∫(f-g)` and
   `∫f + ∫g = ∫(f+g)` (all integrands are continuous with compact support, hence integrable),

       `profHat (y+d) - profHat y + ∫_z χ z (inner d z) sin⟪y,z⟫
          = ∫_z χ z (cos⟪y+d,z⟫ - cos⟪y,z⟫ + (inner d z) sin⟪y,z⟫)`.

2. **The pointwise trigonometric bound.**  With `a = inner y z`, `t = inner d z` and
   `inner (y+d) z = inner y z + inner d z` (`inner_add_left`), the elementary second-order
   inequality `|cos(a+t) - cos a + t sin a| ≤ t²` (proved from `cos a(cos t - 1) + sin a(t - sin t)`
   and `|cos t - 1| ≤ t²/2`, `|t - sin t| ≤ t²/2`) gives

       `|χ z (cos⟪y+d,z⟫ - cos⟪y,z⟫ + (inner d z) sin⟪y,z⟫)| ≤ |χ z| (inner d z)²
          ≤ |χ z| ‖z‖² ‖d‖²`   (`abs_real_inner_le_norm`).

3. **Integrate.**  `|∫ G| ≤ ∫ |G|` and monotonicity of the integral against the dominating
   function `z ↦ |χ z| ‖z‖² ‖d‖²`, whose integral is `(∫ |χ z| ‖z‖²) · ‖d‖²`
   (`integral_mul_const`).
-/

noncomputable section

open MeasureTheory

namespace Work.OneBodyKin

open Submission.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-! ## Auxiliary lemmas -/

/-- `χ` times a continuous function is integrable: the product is continuous with compact
support, since `χ` has compact support. -/
private lemma integrable_chi_mul {f : ℝ³ → ℝ} (hf : Continuous f) :
    Integrable (fun z : ℝ³ => chi z * f z) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact chi_continuous.mul hf
  · refine HasCompactSupport.mono chi_hasCompactSupport ?_
    intro z hz
    simp only [Function.mem_support] at hz ⊢
    intro h
    exact hz (by rw [h, zero_mul])

/-- **The second-order remainder of the cosine.**  For all real `a`, `t`,

    `|cos (a+t) - cos a + t sin a| ≤ t²`.

Written as `cos a (cos t - 1) + sin a (t - sin t)` (using `cos (a+t) = cos a cos t - sin a sin t`),
the two factors are bounded by `t²/2`: the first from `1 - t²/2 ≤ cos t`,
the second from `|t - sin t| ≤ t²/2` (`|t - sin t| ≤ |t|³/6` for `|t| ≤ 3` and
`|t - sin t| ≤ |t| + 1 ≤ t²/2` for `|t| ≥ 3`). -/
private lemma trig_le (a t : ℝ) :
    |Real.cos (a + t) - Real.cos a + t * Real.sin a| ≤ t ^ 2 := by
  have h1 : |Real.cos t - 1| ≤ t ^ 2 / 2 := by
    have hle : Real.cos t - 1 ≤ 0 := by linarith [Real.cos_le_one t]
    rw [abs_of_nonpos hle]
    linarith [Real.one_sub_sq_div_two_le_cos (x := t)]
  have h2 : |t - Real.sin t| ≤ t ^ 2 / 2 := by
    rcases le_or_gt |t| 3 with h | h
    · have h1' := Real.abs_sub_sin_le t
      have hs : |t| ^ 2 = t ^ 2 := sq_abs t
      have h3 : |t| ^ 3 ≤ 3 * |t| ^ 2 := by nlinarith [h, abs_nonneg t, sq_nonneg |t|]
      linarith
    · have h1' : |t - Real.sin t| ≤ |t| + 1 := by
        calc |t - Real.sin t| = |t + (-Real.sin t)| := by rw [sub_eq_add_neg]
          _ ≤ |t| + |-Real.sin t| := abs_add_le _ _
          _ = |t| + |Real.sin t| := by rw [abs_neg]
          _ ≤ |t| + 1 := by linarith [Real.abs_sin_le_one t]
      have hs : |t| ^ 2 = t ^ 2 := sq_abs t
      have h2' : |t| + 1 ≤ t ^ 2 / 2 := by nlinarith [h, abs_nonneg t, sq_abs t]
      linarith
  have key : Real.cos (a + t) - Real.cos a + t * Real.sin a
      = Real.cos a * (Real.cos t - 1) + Real.sin a * (t - Real.sin t) := by
    rw [Real.cos_add]; ring
  rw [key]
  calc |Real.cos a * (Real.cos t - 1) + Real.sin a * (t - Real.sin t)|
      ≤ |Real.cos a * (Real.cos t - 1)| + |Real.sin a * (t - Real.sin t)| := abs_add_le _ _
    _ = |Real.cos a| * |Real.cos t - 1| + |Real.sin a| * |t - Real.sin t| := by
        rw [abs_mul, abs_mul]
    _ ≤ 1 * (t ^ 2 / 2) + 1 * (t ^ 2 / 2) := by
        apply add_le_add
        · exact mul_le_mul (Real.abs_cos_le_one a) h1 (abs_nonneg _) (by norm_num)
        · exact mul_le_mul (Real.abs_sin_le_one a) h2 (abs_nonneg _) (by norm_num)
    _ = t ^ 2 := by ring

/-! ## The main lemma -/

theorem profHat_add_sub_linear_le (y d : EuclideanSpace ℝ (Fin 3)) :
    |profHat (y + d) - profHat y
        + ∫ z : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.chi z * (inner ℝ d z) * Real.sin (inner ℝ y z)|
      ≤ (∫ z : EuclideanSpace ℝ (Fin 3), |Submission.BoseGases.chi z| * ‖z‖ ^ 2) * ‖d‖ ^ 2 := by
  -- integrability of the three pieces of the unfolded difference
  have hA : Integrable (fun z : ℝ³ => chi z * Real.cos (inner ℝ (y + d) z)) :=
    integrable_chi_mul (by fun_prop)
  have hB : Integrable (fun z : ℝ³ => chi z * Real.cos (inner ℝ y z)) :=
    integrable_chi_mul (by fun_prop)
  have hC : Integrable (fun z : ℝ³ => chi z * (inner ℝ d z) * Real.sin (inner ℝ y z)) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (chi_continuous.mul (by fun_prop)).mul (by fun_prop)
    · refine HasCompactSupport.mono chi_hasCompactSupport ?_
      intro z hz
      simp only [Function.mem_support] at hz ⊢
      intro h
      exact hz (by simp [h])
  have hD : Integrable
      (fun a : ℝ³ => chi a * Real.cos (inner ℝ (y + d) a) - chi a * Real.cos (inner ℝ y a)) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (chi_continuous.mul (by fun_prop)).sub (chi_continuous.mul (by fun_prop))
    · refine HasCompactSupport.mono chi_hasCompactSupport ?_
      intro z hz
      simp only [Function.mem_support] at hz ⊢
      intro h
      exact hz (by simp [h])
  -- Step 1: the integral identity
  have hkey : profHat (y + d) - profHat y
        + (∫ z : ℝ³, chi z * (inner ℝ d z) * Real.sin (inner ℝ y z))
      = ∫ z : ℝ³, chi z * (Real.cos (inner ℝ (y + d) z) - Real.cos (inner ℝ y z)
          + (inner ℝ d z) * Real.sin (inner ℝ y z)) := by
    rw [profHat, profHat]
    rw [← integral_sub hA hB]
    rw [← integral_add hD hC]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    ring
  rw [hkey]
  -- the integrand `G` and its dominating function are integrable
  have hGcont : Continuous (fun z : ℝ³ => chi z * (Real.cos (inner ℝ (y + d) z)
      - Real.cos (inner ℝ y z) + (inner ℝ d z) * Real.sin (inner ℝ y z))) := by
    refine chi_continuous.mul ?_
    exact ((by fun_prop : Continuous (fun z : ℝ³ => Real.cos (inner ℝ (y + d) z))).sub
      (by fun_prop)).add (by fun_prop)
  have hGcs : HasCompactSupport (fun z : ℝ³ => chi z * (Real.cos (inner ℝ (y + d) z)
      - Real.cos (inner ℝ y z) + (inner ℝ d z) * Real.sin (inner ℝ y z))) := by
    refine HasCompactSupport.mono chi_hasCompactSupport ?_
    intro z hz
    simp only [Function.mem_support] at hz ⊢
    intro h
    exact hz (by simp [h])
  have hGint : Integrable (fun z : ℝ³ => |chi z * (Real.cos (inner ℝ (y + d) z)
      - Real.cos (inner ℝ y z) + (inner ℝ d z) * Real.sin (inner ℝ y z))|) :=
    (hGcont.integrable_of_hasCompactSupport hGcs).abs
  have hbase : Integrable (fun z : ℝ³ => |chi z| * ‖z‖ ^ 2) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact chi_continuous.abs.mul (continuous_norm.pow 2)
    · refine HasCompactSupport.mono chi_hasCompactSupport ?_
      intro z hz
      simp only [Function.mem_support] at hz ⊢
      intro h
      exact hz (by simp [h])
  have hHint : Integrable (fun z : ℝ³ => |chi z| * ‖z‖ ^ 2 * ‖d‖ ^ 2) := hbase.mul_const _
  -- Steps 2 and 3
  refine (abs_integral_le_integral_abs.trans ?_)
  refine (integral_mono_ae hGint hHint (Filter.Eventually.of_forall (fun z => ?_))).trans ?_
  · -- pointwise bound
    dsimp only
    rw [abs_mul, inner_add_left]
    have htrig := trig_le (inner ℝ y z) (inner ℝ d z)
    have h2 : (inner ℝ d z) ^ 2 ≤ ‖d‖ ^ 2 * ‖z‖ ^ 2 := by
      have h := abs_real_inner_le_norm d z
      rw [show (inner ℝ d z) ^ 2 = |inner ℝ d z| ^ 2 from (sq_abs _).symm]
      calc |inner ℝ d z| ^ 2 ≤ (‖d‖ * ‖z‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
        _ = ‖d‖ ^ 2 * ‖z‖ ^ 2 := by rw [mul_pow]
    calc |chi z| * |Real.cos (inner ℝ y z + inner ℝ d z) - Real.cos (inner ℝ y z)
            + inner ℝ d z * Real.sin (inner ℝ y z)|
        ≤ |chi z| * (inner ℝ d z) ^ 2 := mul_le_mul_of_nonneg_left htrig (abs_nonneg _)
      _ ≤ |chi z| * (‖d‖ ^ 2 * ‖z‖ ^ 2) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      _ = |chi z| * ‖z‖ ^ 2 * ‖d‖ ^ 2 := by ring
  · -- pull the constant `‖d‖²` out of the integral
    exact (integral_mul_const _ _).le

end Work.OneBodyKin
