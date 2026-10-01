/-
# ZeroFreeTables — T10Defs

Shared definitions for the Table 10 row certificates (`table10_62_cert`,
`table10_93_cert`).

The analysis of HB Lemma 7.2's test function at scale `λ` is carried out in terms of
`hb72g u = 32 - 40u² + 20u³ - u⁵ = (2-u)³(4+6u+u²)` and its Laplace transform
`hb72G x = ∫₀² hb72g u · e^{xu} du` (the normalised density of
`HBTable2and3_engine`), linked to the test-function transform by the substitution
`u = λ t`.

For the *lower* bounds of `hb72G` at non-positive arguments we use the Taylor
truncation of the exponential: for `t ≤ 0` and `m` even the alternating partial sum
`Σ_{k<m} t^k/k!` is a lower bound for `e^t`, and integrating against `hb72g ≥ 0`
gives

  `Σ_{k<m} (∫₀² u^k hb72g u du) · y^k/k! ≤ hb72G y`  for `y ≤ 0`.

The moments `∫₀² u^k hb72g u du` are the rationals `GA k` below.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.t23Defs

open scoped BigOperators

noncomputable section
namespace Work.ZeroFreeTables

/-- The `k`-th moment `∫₀² u^k hb72g u du` of HB Lemma 7.2's density, in closed form. -/
def GA (k : ℕ) : ℝ :=
  32 * 2 ^ (k + 1) / ((k : ℝ) + 1) - 40 * 2 ^ (k + 3) / ((k : ℝ) + 3)
    + 20 * 2 ^ (k + 4) / ((k : ℝ) + 4) - 2 ^ (k + 6) / ((k : ℝ) + 6)

/-- The six-term Taylor truncation used as a lower bound for `hb72G` on
non-positive arguments. -/
def Ty6 (y : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 6, GA k * y ^ k / (k.factorial : ℝ)

@[simp] lemma GA_zero : GA 0 = 80/3 := by norm_num [GA]
@[simp] lemma GA_one : GA 1 = 96/7 := by norm_num [GA]
@[simp] lemma GA_two : GA 2 = 32/3 := by norm_num [GA]
@[simp] lemma GA_three : GA 3 = 640/63 := by norm_num [GA]
@[simp] lemma GA_four : GA 4 = 384/35 := by norm_num [GA]
@[simp] lemma GA_five : GA 5 = 1280/99 := by norm_num [GA]

lemma Ty6_eq (y : ℝ) :
    Ty6 y = 80/3 + (96/7) * y + (32/3) * y^2 / 2 + (640/63) * y^3 / 6
      + (384/35) * y^4 / 24 + (1280/99) * y^5 / 120 := by
  unfold Ty6
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  norm_num [GA]

/-! ## The moments as integrals -/

/-- **The moments of HB Lemma 7.2's density.**  `GA k = ∫₀² u^k hb72g u du`. -/
lemma GA_eq (k : ℕ) : GA k = ∫ t in (0:ℝ)..2, t ^ k * hb72g t := by
  have hfun : ∀ t : ℝ, t ^ k * hb72g t
      = 32 * t ^ k - 40 * t ^ (k+2) + 20 * t ^ (k+3) - t ^ (k+5) := by
    intro t
    unfold hb72g
    have e1 : t ^ k * t ^ 2 = t ^ (k+2) := by rw [← pow_add]
    have e2 : t ^ k * t ^ 3 = t ^ (k+3) := by rw [← pow_add]
    have e3 : t ^ k * t ^ 5 = t ^ (k+5) := by rw [← pow_add]
    rw [show t ^ k * (32 - 40 * t ^ 2 + 20 * t ^ 3 - t ^ 5)
        = 32 * t^k - 40 * (t^k * t^2) + 20 * (t^k * t^3) - (t^k * t^5) by ring,
      e1, e2, e3]
  rw [intervalIntegral.integral_congr (fun t _ => hfun t)]
  have h0 : IntervalIntegrable (fun t : ℝ => 32 * t^k) MeasureTheory.volume (0:ℝ) 2 :=
    (by fun_prop : Continuous fun t : ℝ => 32 * t^k).intervalIntegrable _ _
  have h1 : IntervalIntegrable (fun t : ℝ => 40 * t^(k+2)) MeasureTheory.volume (0:ℝ) 2 :=
    (by fun_prop : Continuous fun t : ℝ => 40 * t^(k+2)).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun t : ℝ => 20 * t^(k+3)) MeasureTheory.volume (0:ℝ) 2 :=
    (by fun_prop : Continuous fun t : ℝ => 20 * t^(k+3)).intervalIntegrable _ _
  have h3 : IntervalIntegrable (fun t : ℝ => t^(k+5)) MeasureTheory.volume (0:ℝ) 2 :=
    (by fun_prop : Continuous fun t : ℝ => t^(k+5)).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub ((h0.sub h1).add h2) h3,
      intervalIntegral.integral_add (h0.sub h1) h2,
      intervalIntegral.integral_sub h0 h1,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  rw [integral_pow, integral_pow, integral_pow, integral_pow]
  simp only [zero_pow (Nat.succ_ne_zero k), zero_pow (Nat.succ_ne_zero (k+2)),
    zero_pow (Nat.succ_ne_zero (k+3)), zero_pow (Nat.succ_ne_zero (k+5)), sub_zero]
  unfold GA
  push_cast
  ring

end Work.ZeroFreeTables
