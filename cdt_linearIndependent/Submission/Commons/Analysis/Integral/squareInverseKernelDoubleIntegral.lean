import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Commons.Analysis.Integral.integral_tsum_interval

/-!
# `squareInverseKernelDoubleIntegral`

The double integral over the unit square of `1 / (1 + xy + x²y²)` equals the
series `∑ₖ (1/(3k+1)² − 1/(3k+2)²)`.

Mathematical route: for `0 ≤ t < 1` the geometric expansion

    1/(1 + t + t²) = (1 − t)/(1 − t³) = ∑ₖ (t^{3k} − t^{3k+1})

converges.  Since `0 ≤ xy ≤ 1` on the square (equality `xy = 1` only at the
corner `(1,1)`), for every fixed `x ∈ [0,1]` the two functions of `y`

    y ↦ 1/(1 + xy + x²y²)   and   y ↦ ∑ₖ ((xy)^{3k} − (xy)^{3k+1})

agree almost everywhere, hence have equal interval integrals.  Termwise
integration (`integral_tsum_interval`) for each fixed `x` and then once more
over `x` reduces the problem to monomial integrals:

    ∫₀¹ x^m dx = 1/(m+1)   ⟹   ∫₀¹∫₀¹ (xy)^{3k} dydx = 1/(3k+1)²,
    ∫₀¹∫₀¹ (xy)^{3k+1} dydx = 1/(3k+2)²,

which gives exactly the requested series.
-/

noncomputable section

namespace Commons.Analysis.Integral

open MeasureTheory
open scoped Interval BigOperators

/-- The kernel `t ↦ 1/(1+t+t²)`. -/
def inverseQuad (t : ℝ) : ℝ := (1 : ℝ) / (1 + t + t ^ 2)

/-- The `k`-th summand `t ↦ t^(3k) − t^(3k+1)` of the geometric expansion of
`inverseQuad` on `[0,1)`. -/
def inverseQuadSummand (k : ℕ) (t : ℝ) : ℝ := t ^ (3 * k) - t ^ (3 * k + 1)

/-- Geometric identity: `1/(1+t+t²) = ∑ₖ (t^{3k} − t^{3k+1})` for `0 ≤ t < 1`. -/
lemma geomSum_inverseQuad {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (∑' k : ℕ, inverseQuadSummand k t) = inverseQuad t := by
  have ht3 : t ^ 3 < 1 := pow_lt_one₀ ht0 ht1 (by norm_num : (3 : ℕ) ≠ 0)
  have habs : |t ^ 3| < 1 := by
    rw [abs_of_nonneg (pow_nonneg ht0 3)]
    exact ht3
  have hrew : ∀ k : ℕ, inverseQuadSummand k t = (1 - t) * (t ^ 3) ^ k := by
    intro k
    have h1 : t ^ (3 * k + 1) = t ^ (3 * k) * t := by
      rw [pow_add, pow_one]
    rw [inverseQuadSummand, h1, pow_mul]
    ring
  have h1t : 1 - t ≠ 0 := by linarith
  have hden : 1 + t + t ^ 2 ≠ 0 := by
    have h1 : 0 ≤ t ^ 2 := sq_nonneg t
    nlinarith
  calc
    (∑' k : ℕ, inverseQuadSummand k t) = ∑' k : ℕ, (1 - t) * (t ^ 3) ^ k := by
      exact tsum_congr hrew
    _ = (1 - t) * (∑' k : ℕ, (t ^ 3) ^ k) := by
      rw [tsum_mul_left]
    _ = (1 - t) * ((1 - t ^ 3)⁻¹) := by
      rw [tsum_geometric_of_norm_lt_one habs]
    _ = inverseQuad t := by
      rw [inverseQuad]
      have hfac : 1 - t ^ 3 = (1 - t) * (1 + t + t ^ 2) := by ring
      rw [← one_div, hfac]
      field_simp [h1t, hden]

/-- `∫₀¹ x^n = 1/(n+1)` (natural exponents). -/
lemma intervalIntegral_pow_zero_one (n : ℕ) :
    (∫ x in (0 : ℝ)..1, x ^ n) = 1 / ((n : ℝ) + 1) := by
  rw [integral_pow]
  simp

/-- `∫₀¹ x^a / (a+1) dx = 1/(a+1)²`. -/
lemma intervalIntegral_x_pow_succ_div (a : ℕ) :
    (∫ x in (0 : ℝ)..1, x ^ a / ((a + 1 : ℕ) : ℝ)) =
      (1 : ℝ) / (((a + 1 : ℕ) : ℝ) ^ 2) := by
  calc
    (∫ x in (0 : ℝ)..1, x ^ a / ((a + 1 : ℕ) : ℝ))
        = ∫ x in (0 : ℝ)..1, (1 / ((a + 1 : ℕ) : ℝ)) * x ^ a := by
          apply intervalIntegral.integral_congr
          intro x hx
          ring
    _ = (1 / ((a + 1 : ℕ) : ℝ)) * (∫ x in (0 : ℝ)..1, x ^ a) := by
          rw [intervalIntegral.integral_const_mul]
    _ = 1 / (((a + 1 : ℕ) : ℝ) ^ 2) := by
          rw [intervalIntegral_pow_zero_one]
          have hc : ((a + 1 : ℕ) : ℝ) = (a : ℝ) + 1 := by norm_num
          rw [hc]
          have hn : (a : ℝ) + 1 ≠ 0 := by positivity
          field_simp [hn]

/-- `∑ₖ (x³)ᵏ` converges for `0 ≤ x < 1`. -/
lemma summable_pow3 {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Summable fun k : ℕ => x ^ (3 * k) := by
  have hx3 : x ^ 3 < 1 := pow_lt_one₀ hx0 hx1 (by norm_num : (3 : ℕ) ≠ 0)
  have habs : |x ^ 3| < 1 := by
    rw [abs_of_nonneg (pow_nonneg hx0 3)]
    exact hx3
  have hsum : Summable fun k : ℕ => (x ^ 3) ^ k :=
    summable_geometric_of_norm_lt_one habs
  exact hsum.congr (fun k => (pow_mul x 3 k).symm)

/-- Summands of the geometric expansion are non-negative on `[0,1]`. -/
lemma summand_nonneg {k : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ inverseQuadSummand k t := by
  have ht3 : 0 ≤ t ^ (3 * k) := pow_nonneg ht0 _
  have hb : t ^ (3 * k + 1) ≤ t ^ (3 * k) := by
    have hsucc : t ^ (3 * k + 1) = t ^ (3 * k) * t := by
      rw [pow_add, pow_one]
    rw [hsucc]
    calc
      t ^ (3 * k) * t ≤ t ^ (3 * k) * 1 := by
        exact mul_le_mul_of_nonneg_left ht1 ht3
      _ = t ^ (3 * k) := by rw [mul_one]
  exact sub_nonneg.mpr hb

/-- `|t^(3k) − t^(3k+1)| ≤ t^(3k)` on `[0,1]`. -/
lemma norm_summand_le {k : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖inverseQuadSummand k t‖ ≤ t ^ (3 * k) := by
  have hnon : 0 ≤ inverseQuadSummand k t := summand_nonneg ht0 ht1
  rw [Real.norm_eq_abs, abs_of_nonneg hnon]
  unfold inverseQuadSummand
  have hb0 : 0 ≤ t ^ (3 * k + 1) := pow_nonneg ht0 _
  linarith

/-- `t ↦ t^(3k) − t^(3k+1)` is continuous. -/
lemma continuous_summand (k : ℕ) : Continuous (fun t : ℝ => inverseQuadSummand k t) := by
  unfold inverseQuadSummand
  fun_prop

/-- Interval integrability over `y ∈ [0,1]` of the summand at fixed `x`. -/
lemma intervalIntegrable_summand_param (k : ℕ) (x : ℝ) :
    IntervalIntegrable (fun y : ℝ => inverseQuadSummand k (x * y)) volume (0 : ℝ) 1 := by
  exact Continuous.intervalIntegrable
    ((continuous_summand k).comp (by fun_prop : Continuous fun y : ℝ => x * y)) (0 : ℝ) 1

/-- closed form of the inner integral `∫₀¹ ((xy)^(3k) − (xy)^(3k+1)) dy`,
as a polynomial in `x`. -/
lemma innerIntegral_closed {k : ℕ} (x : ℝ) :
    (∫ y in (0 : ℝ)..1, inverseQuadSummand k (x * y)) =
      x ^ (3 * k) / ((3 * k + 1 : ℕ) : ℝ) -
        x ^ (3 * k + 1) / ((3 * k + 2 : ℕ) : ℝ) := by
  have hmul : ∀ n : ℕ, (∫ y in (0 : ℝ)..1, x ^ n * y ^ n) =
      x ^ n / ((n : ℝ) + 1) := by
    intro n
    calc
      (∫ y in (0 : ℝ)..1, x ^ n * y ^ n)
          = x ^ n * (∫ y in (0 : ℝ)..1, y ^ n) := by
            rw [intervalIntegral.integral_const_mul]
      _ = x ^ n / ((n : ℝ) + 1) := by
            rw [intervalIntegral_pow_zero_one]
            ring
  calc
    (∫ y in (0 : ℝ)..1, inverseQuadSummand k (x * y))
        = ∫ y in (0 : ℝ)..1, (x ^ (3 * k) * y ^ (3 * k) -
            x ^ (3 * k + 1) * y ^ (3 * k + 1)) := by
          apply intervalIntegral.integral_congr
          intro y hy
          change inverseQuadSummand k (x * y) =
            x ^ (3 * k) * y ^ (3 * k) - x ^ (3 * k + 1) * y ^ (3 * k + 1)
          simp [inverseQuadSummand, mul_pow]
    _ = (∫ y in (0 : ℝ)..1, x ^ (3 * k) * y ^ (3 * k)) -
          (∫ y in (0 : ℝ)..1, x ^ (3 * k + 1) * y ^ (3 * k + 1)) := by
          rw [intervalIntegral.integral_sub]
          · exact Continuous.intervalIntegrable (by fun_prop) (0 : ℝ) 1
          · exact Continuous.intervalIntegrable (by fun_prop) (0 : ℝ) 1
    _ = x ^ (3 * k) / ((3 * k + 1 : ℕ) : ℝ) -
          x ^ (3 * k + 1) / ((3 * k + 2 : ℕ) : ℝ) := by
          rw [hmul (3 * k), hmul (3 * k + 1)]
          norm_num
          ring

/-- For `0 ≤ x ≤ 1` the `y`-integral of the kernel equals the `y`-integral of
its geometric expansion (they agree almost everywhere in `y`). -/
lemma innerIntegral_geom {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (∫ y in (0 : ℝ)..1, inverseQuad (x * y)) =
      ∫ y in (0 : ℝ)..1, (∑' k : ℕ, inverseQuadSummand k (x * y)) := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [Measure.ae_ne (volume : Measure ℝ) (1 : ℝ)] with y hy
  intro hyI
  have hyI' : y ∈ Set.Ioc (0 : ℝ) 1 := by
    simpa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hyI
  have hy0 : 0 ≤ y := le_of_lt hyI'.1
  have hy1 : y ≤ 1 := hyI'.2
  have hylt : y < 1 := lt_of_le_of_ne hy1 hy
  have hxy0 : 0 ≤ x * y := mul_nonneg hx0 hy0
  have hxylt : x * y < 1 := by
    rcases lt_or_eq_of_le hx1 with hxlt | hxeq
    · calc
        x * y ≤ x * 1 := mul_le_mul_of_nonneg_left hy1 hx0
        _ = x := by rw [mul_one]
        _ < 1 := hxlt
    · rw [hxeq, one_mul]
      exact hylt
  exact (geomSum_inverseQuad (t := x * y) hxy0 hxylt).symm

/-- For `0 ≤ x ≤ 1` the `y`-integral of the norm of a summand equals the
`y`-integral of the (non-negative) summand. -/
lemma norm_inner_eq_inner {k : ℕ} {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (∫ y in (0 : ℝ)..1, ‖inverseQuadSummand k (x * y)‖) =
      (∫ y in (0 : ℝ)..1, inverseQuadSummand k (x * y)) := by
  apply intervalIntegral.integral_congr
  intro y hy
  have hy' : y ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hy
  have hnon : 0 ≤ inverseQuadSummand k (x * y) :=
    summand_nonneg (mul_nonneg hx0 hy'.1) (mul_le_one₀ hx1 hy'.1 hy'.2)
  change ‖inverseQuadSummand k (x * y)‖ = inverseQuadSummand k (x * y)
  rw [Real.norm_eq_abs, abs_of_nonneg hnon]

/-- Inner norm integral bounded by the geometric term `x^(3k)`. -/
lemma innerNormIntegral_le_pow3 {k : ℕ} {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (∫ y in (0 : ℝ)..1, ‖inverseQuadSummand k (x * y)‖) ≤ x ^ (3 * k) := by
  calc
    (∫ y in (0 : ℝ)..1, ‖inverseQuadSummand k (x * y)‖)
        = (∫ y in (0 : ℝ)..1, inverseQuadSummand k (x * y)) := norm_inner_eq_inner hx0 hx1
    _ = x ^ (3 * k) / ((3 * k + 1 : ℕ) : ℝ) -
          x ^ (3 * k + 1) / ((3 * k + 2 : ℕ) : ℝ) := innerIntegral_closed x
    _ ≤ x ^ (3 * k) := by
      have hb0 : 0 ≤ x ^ (3 * k + 1) / ((3 * k + 2 : ℕ) : ℝ) := by
        exact div_nonneg (pow_nonneg hx0 _) (by positivity)
      have h1 : x ^ (3 * k) / ((3 * k + 1 : ℕ) : ℝ) -
            x ^ (3 * k + 1) / ((3 * k + 2 : ℕ) : ℝ) ≤
          x ^ (3 * k) / ((3 * k + 1 : ℕ) : ℝ) := sub_le_self _ hb0
      have hpos : 0 < ((3 * k + 1 : ℕ) : ℝ) := by positivity
      have hc : (1 : ℝ) ≤ ((3 * k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 3 * k + 1)
      have hd : (1 : ℝ) / ((3 * k + 1 : ℕ) : ℝ) ≤ 1 := (div_le_one hpos).mpr hc
      have h2 : x ^ (3 * k) / ((3 * k + 1 : ℕ) : ℝ) ≤ x ^ (3 * k) := by
        have hp : 0 ≤ x ^ (3 * k) := pow_nonneg hx0 _
        calc
          x ^ (3 * k) / ((3 * k + 1 : ℕ) : ℝ)
              = (1 / ((3 * k + 1 : ℕ) : ℝ)) * x ^ (3 * k) := by ring
          _ ≤ 1 * x ^ (3 * k) := by
                exact mul_le_mul_of_nonneg_right hd hp
          _ = x ^ (3 * k) := by rw [one_mul]
      exact le_trans h1 h2

/-- For `0 < x < 1` the `y`-integral commutes with the series over `k`
(absolute summability from the geometric bound `x^(3k)`). -/
lemma innerInterchange {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    (∫ y in (0 : ℝ)..1, (∑' k : ℕ, inverseQuadSummand k (x * y))) =
      (∑' k : ℕ, ∫ y in (0 : ℝ)..1, inverseQuadSummand k (x * y)) := by
  have hsum : Summable (fun k : ℕ =>
      ∫ y in (0 : ℝ)..1, ‖inverseQuadSummand k (x * y)‖) := by
    apply Summable.of_nonneg_of_le
    · intro k
      exact intervalIntegral.integral_nonneg (by norm_num)
        (fun y hy => norm_nonneg (inverseQuadSummand k (x * y)))
    · intro k
      exact innerNormIntegral_le_pow3 (le_of_lt hx0) (le_of_lt hx1)
    · exact summable_pow3 (le_of_lt hx0) hx1
  exact (Commons.Analysis.Integral.integral_tsum_interval
    (f := fun k y => inverseQuadSummand k (x * y))
    (fun k => intervalIntegrable_summand_param k x) hsum).symm


/-- The double monomial integral `∫₀¹∫₀¹ (xy)^n = 1/(n+1)²`. -/
lemma doubleIntegral_pow (n : ℕ) :
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, (x * y) ^ n) =
      1 / (((n : ℝ) + 1) ^ 2) := by
  calc
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, (x * y) ^ n)
        = ∫ x in (0 : ℝ)..1, (x ^ n * (∫ y in (0 : ℝ)..1, y ^ n)) := by
          apply intervalIntegral.integral_congr
          intro x hx
          change (∫ y in (0 : ℝ)..1, (x * y) ^ n) = x ^ n * (∫ y in (0 : ℝ)..1, y ^ n)
          calc
            (∫ y in (0 : ℝ)..1, (x * y) ^ n)
                = ∫ y in (0 : ℝ)..1, (x ^ n * y ^ n) := by
                  apply intervalIntegral.integral_congr
                  intro y hy
                  change (x * y) ^ n = x ^ n * y ^ n
                  exact mul_pow x y n
            _ = x ^ n * (∫ y in (0 : ℝ)..1, y ^ n) := by
                  rw [intervalIntegral.integral_const_mul]
    _ = (∫ x in (0 : ℝ)..1, x ^ n) * (∫ y in (0 : ℝ)..1, y ^ n) := by
          rw [intervalIntegral.integral_mul_const]
    _ = 1 / (((n : ℝ) + 1) ^ 2) := by
          rw [intervalIntegral_pow_zero_one]
          have hn : (n : ℝ) + 1 ≠ 0 := by positivity
          field_simp [hn]

/-- value of the double integral of the `k`-th summand. -/
lemma doubleIntegral_summand (k : ℕ) :
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, inverseQuadSummand k (x * y)) =
      (1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2) -
        (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2) := by
  calc
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, inverseQuadSummand k (x * y))
        = ∫ x in (0 : ℝ)..1, (x ^ (3 * k) / ((3 * k + 1 : ℕ) : ℝ) -
            x ^ (3 * k + 1) / ((3 * k + 2 : ℕ) : ℝ)) := by
          apply intervalIntegral.integral_congr
          intro x hx
          exact innerIntegral_closed x
    _ = (∫ x in (0 : ℝ)..1, x ^ (3 * k) / ((3 * k + 1 : ℕ) : ℝ)) -
          (∫ x in (0 : ℝ)..1, x ^ (3 * k + 1) / ((3 * k + 2 : ℕ) : ℝ)) := by
          rw [intervalIntegral.integral_sub]
          · exact Continuous.intervalIntegrable (by fun_prop) (0 : ℝ) 1
          · exact Continuous.intervalIntegrable (by fun_prop) (0 : ℝ) 1
    _ = (1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2) -
          (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2) := by
          rw [intervalIntegral_x_pow_succ_div (3 * k)]
          rw [intervalIntegral_x_pow_succ_div (3 * k + 1)]

/-- The value terms `1/(3k+1)² − 1/(3k+2)²` are non-negative. -/
lemma valk_nonneg (k : ℕ) :
    0 ≤ (1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2) -
      (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2) := by
  have hle : ((3 * k + 1 : ℕ) : ℝ) ≤ ((3 * k + 2 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 3 * k + 1 ≤ 3 * k + 2)
  have hsq : ((3 * k + 1 : ℕ) : ℝ) ^ 2 ≤ ((3 * k + 2 : ℕ) : ℝ) ^ 2 := by
    nlinarith [hle]
  have hdiv : (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2) ≤
      (1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2) := by
    exact one_div_le_one_div_of_le (by positivity : 0 < ((3 * k + 1 : ℕ) : ℝ) ^ 2) hsq
  exact sub_nonneg.mpr hdiv

/-- `∑ₖ 1/((3k+1):ℝ)²` is summable (p-series). -/
lemma summable_mod1 : Summable (fun k : ℕ => (1 : ℝ) / ((3 * k + 1 : ℕ) : ℝ) ^ 2) := by
  have hs : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2)) :=
    (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num : (1 : ℕ) < 2)
  have hinj : Function.Injective (fun k : ℕ => 3 * k + 1) := by
    intro a b h
    dsimp at h
    omega
  exact hs.comp_injective hinj

/-- `∑ₖ (1/(3k+1)² − 1/(3k+2)²)` is summable. -/
lemma summable_valk :
    Summable (fun k : ℕ => (1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2) -
      (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2)) := by
  apply Summable.of_nonneg_of_le
  · intro k
    exact valk_nonneg k
  · intro k
    have hpos : 0 ≤ (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2) := by positivity
    exact sub_le_self ((1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2)) hpos
  · exact summable_mod1

/-- `x ↦ ∫₀¹ (inverseQuadSummand k (x·y)) dy` is continuous. -/
lemma continuous_yInner (k : ℕ) :
    Continuous (fun x : ℝ => ∫ y in (0 : ℝ)..1, inverseQuadSummand k (x * y)) := by
  have heq : (fun x : ℝ => ∫ y in (0 : ℝ)..1, inverseQuadSummand k (x * y)) =
      (fun x : ℝ => x ^ (3 * k) / ((3 * k + 1 : ℕ) : ℝ) -
        x ^ (3 * k + 1) / ((3 * k + 2 : ℕ) : ℝ)) := by
    funext x
    exact innerIntegral_closed x
  rw [heq]
  fun_prop

/-- summability of the outer sequence of norms of inner integrals. -/
lemma summable_outer :
    Summable (fun k : ℕ => ∫ x in (0 : ℝ)..1,
      ‖(∫ y in (0 : ℝ)..1, inverseQuadSummand k (x * y))‖) := by
  have hterm : ∀ k : ℕ,
      (∫ x in (0 : ℝ)..1, ‖(∫ y in (0 : ℝ)..1, inverseQuadSummand k (x * y))‖) =
        (1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2) -
          (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2) := by
    intro k
    calc
      (∫ x in (0 : ℝ)..1, ‖(∫ y in (0 : ℝ)..1, inverseQuadSummand k (x * y))‖)
          = ∫ x in (0 : ℝ)..1, (∫ y in (0 : ℝ)..1, inverseQuadSummand k (x * y)) := by
            apply intervalIntegral.integral_congr
            intro x hx
            have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by
              simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
            have hnon : 0 ≤ (∫ y in (0 : ℝ)..1, inverseQuadSummand k (x * y)) := by
              apply intervalIntegral.integral_nonneg (by norm_num)
              intro y hy
              exact summand_nonneg (mul_nonneg hx'.1 hy.1) (mul_le_one₀ hx'.2 hy.1 hy.2)
            change ‖(∫ y in (0 : ℝ)..1, inverseQuadSummand k (x * y))‖ =
              (∫ y in (0 : ℝ)..1, inverseQuadSummand k (x * y))
            rw [Real.norm_eq_abs, abs_of_nonneg hnon]
      _ = ∫ x in (0 : ℝ)..1, (x ^ (3 * k) / ((3 * k + 1 : ℕ) : ℝ) -
            x ^ (3 * k + 1) / ((3 * k + 2 : ℕ) : ℝ)) := by
            apply intervalIntegral.integral_congr
            intro x hx
            exact innerIntegral_closed x
      _ = (1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2) -
            (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2) := by
            calc
              (∫ x in (0 : ℝ)..1, (x ^ (3 * k) / ((3 * k + 1 : ℕ) : ℝ) -
                  x ^ (3 * k + 1) / ((3 * k + 2 : ℕ) : ℝ)))
                  = (∫ x in (0 : ℝ)..1, x ^ (3 * k) / ((3 * k + 1 : ℕ) : ℝ)) -
                      (∫ x in (0 : ℝ)..1, x ^ (3 * k + 1) / ((3 * k + 2 : ℕ) : ℝ)) := by
                      rw [intervalIntegral.integral_sub]
                      · exact Continuous.intervalIntegrable (by fun_prop) (0 : ℝ) 1
                      · exact Continuous.intervalIntegrable (by fun_prop) (0 : ℝ) 1
              _ = (1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2) -
                      (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2) := by
                      rw [intervalIntegral_x_pow_succ_div (3 * k)]
                      rw [intervalIntegral_x_pow_succ_div (3 * k + 1)]
  exact (summable_valk.congr fun k => (hterm k).symm)

/-- Exchange of the outer integral in `x` with the series over `k`. -/
lemma outerInterchange :
    (∫ x in (0 : ℝ)..1, (∑' k : ℕ,
        (∫ y in (0 : ℝ)..1, inverseQuadSummand k (x * y)))) =
      (∑' k : ℕ, ∫ x in (0 : ℝ)..1,
        (∫ y in (0 : ℝ)..1, inverseQuadSummand k (x * y))) := by
  exact (Commons.Analysis.Integral.integral_tsum_interval
    (f := fun k x => ∫ y in (0 : ℝ)..1, inverseQuadSummand k (x * y))
    (fun k => Continuous.intervalIntegrable (continuous_yInner k) (0 : ℝ) 1) summable_outer).symm

/-- **The requested identity.** -/
lemma squareInverseKernelDoubleIntegral :
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
        (1 : ℝ) / (1 + x * y + x ^ 2 * y ^ 2))
      = (∑' k : ℕ,
          ((1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2)
            - (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2))) := by
  -- 1) the integrand is `inverseQuad (x * y)`
  have hfirst : (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
        (1 : ℝ) / (1 + x * y + x ^ 2 * y ^ 2)) =
      (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, inverseQuad (x * y)) := by
    refine congrArg (fun h : ℝ → ℝ → ℝ => ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, h x y) ?_
    funext x y
    rw [inverseQuad]
    congr 1
    ring
  -- 2) inner geometric expansion, pointwise in `x ∈ [0,1]`
  have hstep2 : (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, inverseQuad (x * y)) =
      (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
        (∑' k : ℕ, inverseQuadSummand k (x * y))) := by
    apply intervalIntegral.integral_congr
    intro x hx
    change (∫ y in (0 : ℝ)..1, inverseQuad (x * y)) =
      (∫ y in (0 : ℝ)..1, (∑' k : ℕ, inverseQuadSummand k (x * y)))
    have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
    exact innerIntegral_geom hx'.1 hx'.2
  -- 3) termwise integration over `y` for almost every `x` (all `x ∈ (0,1)`)
  have hstep3 : (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
        (∑' k : ℕ, inverseQuadSummand k (x * y))) =
      (∫ x in (0 : ℝ)..1, (∑' k : ℕ,
        (∫ y in (0 : ℝ)..1, inverseQuadSummand k (x * y)))) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne (volume : Measure ℝ) (1 : ℝ)] with x hxne
    intro hxI
    have hxI' : x ∈ Set.Ioc (0 : ℝ) 1 := by
      simpa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hxI
    have hxpos : 0 < x := hxI'.1
    have hxle : x ≤ 1 := hxI'.2
    have hxlt : x < 1 := lt_of_le_of_ne hxle hxne
    change (∫ y in (0 : ℝ)..1, (∑' k : ℕ, inverseQuadSummand k (x * y))) =
      (∑' k : ℕ, ∫ y in (0 : ℝ)..1, inverseQuadSummand k (x * y))
    exact innerInterchange hxpos hxlt
  -- 4) termwise integration over `x`
  have hstep4 : (∫ x in (0 : ℝ)..1, (∑' k : ℕ,
        (∫ y in (0 : ℝ)..1, inverseQuadSummand k (x * y)))) =
      (∑' k : ℕ, ∫ x in (0 : ℝ)..1,
        (∫ y in (0 : ℝ)..1, inverseQuadSummand k (x * y))) := outerInterchange
  -- 5) the monomial double integrals
  have hstep5 : (∑' k : ℕ, ∫ x in (0 : ℝ)..1,
        (∫ y in (0 : ℝ)..1, inverseQuadSummand k (x * y))) =
      (∑' k : ℕ,
          ((1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2)
            - (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2))) := by
    apply tsum_congr
    intro k
    exact doubleIntegral_summand k
  calc
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
        (1 : ℝ) / (1 + x * y + x ^ 2 * y ^ 2))
        = ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, inverseQuad (x * y) := hfirst
    _ = ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
          (∑' k : ℕ, inverseQuadSummand k (x * y)) := hstep2
    _ = ∫ x in (0 : ℝ)..1, (∑' k : ℕ,
          (∫ y in (0 : ℝ)..1, inverseQuadSummand k (x * y))) := hstep3
    _ = ∑' k : ℕ, ∫ x in (0 : ℝ)..1,
          (∫ y in (0 : ℝ)..1, inverseQuadSummand k (x * y)) := hstep4
    _ = ∑' k : ℕ,
          ((1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2)
            - (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2)) := hstep5

end Commons.Analysis.Integral