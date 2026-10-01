import Mathlib
import Submission.Work.ZeroFreeTables.testFn72_defs
import Submission.Work.ZeroFreeTables.P9F.exp_series_bounds
import Submission.Work.ZeroFreeTables.tf72f_moment
import Submission.Work.ZeroFreeTables.tf72Fc_neglam_re
import Submission.Work.ZeroFreeTables.tf72Fc_zero_re
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.ZeroFreeTables.TestFn_F_eq_integral
import Submission.Work.ZeroFreeTables.tf72f_gap_mono

open scoped BigOperators
open MeasureTheory
noncomputable section
namespace Work.ZeroFreeTables

/-- The polynomial coinciding with `tf72f (6/7)` on `[0, 7/3]`. -/
lemma tf72f_67_eq (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) (7/3)) :
    tf72f (6/7) t = 32/35 - (288/343)*t^2 + (864/2401)*t^3 - (7776/588245)*t^5 := by
  have h : t ∈ Set.Icc (0:ℝ) (2/(6/7)) := by
    rw [show (2:ℝ)/(6/7) = 7/3 by norm_num]; exact ht
  rw [tf72f_eq_poly (6/7) (by norm_num) t h]
  ring

/-- Closed form of the moments `∫₀^{7/3} t^k f(t) dt` of HB's test function with λ = 6/7. -/
def tf72fL_mom (k : ℕ) : ℝ :=
  (32/35)*(7/3)^(k+1)/((k:ℝ)+1) + (-288/343)*(7/3)^(k+3)/((k:ℝ)+3)
    + (864/2401)*(7/3)^(k+4)/((k:ℝ)+4) + (-7776/588245)*(7/3)^(k+6)/((k:ℝ)+6)

/-- The moments of HB's test function at `λ = 6/7` (delegated to
`Submission.Work.ZeroFreeTables.tf72f_moment`), cast into the local closed form. -/
lemma tf72fL_moment (k : ℕ) :
    (∫ t in (0:ℝ)..(7/3), t^k * tf72f (6/7) t) = tf72fL_mom k :=
  tf72f_moment k

lemma tf72fL_moment_zero : (∫ t in (0:ℝ)..(7/3), tf72f (6/7) t) = tf72fL_mom 0 := by
  rw [show (fun t : ℝ => tf72f (6/7) t) = (fun t : ℝ => t^0 * tf72f (6/7) t) from by
    funext t; simp]
  exact tf72fL_moment 0

/-- `exp (-y) ≥ (1 - y/3)^3` for `0 ≤ y ≤ 3`. -/
lemma tf72fL_exp_neg_ge_cubic (y : ℝ) (_hy0 : 0 ≤ y) (hy : y ≤ 3) :
    (1 - y/3)^3 ≤ Real.exp (-y) := by
  have h1 : 1 - y/3 ≤ Real.exp (-(y/3)) := by
    have := Real.add_one_le_exp (-(y/3)); linarith
  have h2 : (1 - y/3)^3 ≤ (Real.exp (-(y/3)))^3 :=
    pow_le_pow_left₀ (by linarith) h1 3
  have h3 : (Real.exp (-(y/3)))^3 = Real.exp (-y) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rwa [h3] at h2

/-- Upper Taylor bound for `exp` used for the first integral. -/
lemma tf72fL_exp_le_taylor13 (t : ℝ) (ht : 0 ≤ t) (htT : t ≤ 7/3) :
    Real.exp ((792/1000:ℝ)*t) ≤
      (∑ j ∈ Finset.range 13, (((792/1000:ℝ)*t)^j / ((j.factorial:ℕ):ℝ)))
        + (((792/1000:ℝ)*(7/3))^13 / ((Nat.factorial 13:ℕ):ℝ)) * (1 / (1 - (792/1000:ℝ)*(7/3)/13)) := by
  have hw0 : 0 ≤ (792/1000:ℝ)*t := by positivity
  have hwT : (792/1000:ℝ)*t ≤ (792/1000:ℝ)*(7/3) :=
    mul_le_mul_of_nonneg_left htT (by norm_num)
  have hw13 : (792/1000:ℝ)*t < 13 := by
    have : (792/1000:ℝ)*(7/3) < 13 := by norm_num
    linarith
  obtain ⟨_, hub⟩ := P9F.exp_series_bounds 13 (by norm_num) ((792/1000:ℝ)*t) hw0 hw13
  have hnum : ((792/1000:ℝ)*t)^13 ≤ ((792/1000:ℝ)*(7/3))^13 :=
    pow_le_pow_left₀ hw0 hwT 13
  have hdenpos : 0 < (1:ℝ) - (792/1000:ℝ)*(7/3)/13 := by norm_num
  have hle : (1:ℝ) - (792/1000:ℝ)*(7/3)/13 ≤ 1 - ((792/1000:ℝ)*t)/13 := by
    have : ((792/1000:ℝ)*t)/13 ≤ ((792/1000:ℝ)*(7/3))/13 :=
      div_le_div_of_nonneg_right hwT (by norm_num)
    linarith
  have hden : 1/(1 - ((792/1000:ℝ)*t)/13) ≤ 1/(1 - (792/1000:ℝ)*(7/3)/13) :=
    one_div_le_one_div_of_le hdenpos hle
  have hA : ((792/1000:ℝ)*t)^13/((Nat.factorial 13:ℕ):ℝ) ≤ ((792/1000:ℝ)*(7/3))^13/((Nat.factorial 13:ℕ):ℝ) :=
    div_le_div_of_nonneg_right hnum (by positivity)
  have htail := mul_le_mul hA hden (by positivity) (by positivity)
  linarith

lemma tf72fL_upper_arith :
    (∑ j ∈ Finset.range 13, (((792/1000:ℝ)^j / ((j.factorial:ℕ):ℝ)) * tf72fL_mom j))
      + (((792/1000:ℝ)*(7/3))^13 / ((Nat.factorial 13:ℕ):ℝ)) * (1/(1 - (792/1000:ℝ)*(7/3)/13)) * tf72fL_mom 0
      ≤ 761/500 := by
  norm_num [tf72fL_mom, Finset.sum_range_succ, Finset.sum_range_zero]

lemma tf72fL_lower_arith :
    tf72fL_mom 0 - (57/875:ℝ)*tf72fL_mom 1 + ((57/875:ℝ)^2/3)*tf72fL_mom 2 - ((57/875:ℝ)^3/27)*tf72fL_mom 3 ≥ 1709/2000 := by
  norm_num [tf72fL_mom]

lemma tf72fL_int_const_moment (j : ℕ) (cc : ℝ) :
    (∫ t in (0:ℝ)..(7/3), cc * (t^j * tf72f (6/7) t)) = cc * tf72fL_mom j := by
  rw [intervalIntegral.integral_const_mul, tf72fL_moment]

lemma tf72fL_int_taylor_sum :
    (∫ t in (0:ℝ)..(7/3),
        (∑ j ∈ Finset.range 13, (((792/1000:ℝ)*t)^j / ((j.factorial:ℕ):ℝ))) * tf72f (6/7) t)
      = ∑ j ∈ Finset.range 13, (((792/1000:ℝ)^j / ((j.factorial:ℕ):ℝ)) * tf72fL_mom j) := by
  rw [show (∫ t in (0:ℝ)..(7/3),
        (∑ j ∈ Finset.range 13, (((792/1000:ℝ)*t)^j / ((j.factorial:ℕ):ℝ))) * tf72f (6/7) t)
      = ∫ t in (0:ℝ)..(7/3),
        ∑ j ∈ Finset.range 13, ((((792/1000:ℝ)*t)^j / ((j.factorial:ℕ):ℝ)) * tf72f (6/7) t) from by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      rw [Finset.sum_mul]]
  have hfs := intervalIntegral.integral_finsetSum (s := Finset.range 13)
      (f := fun j t => ((((792/1000:ℝ)*t)^j / ((j.factorial:ℕ):ℝ)) * tf72f (6/7) t))
      (μ := volume) (a := (0:ℝ)) (b := 7/3)
      (fun j _ => by
        apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
        refine ContinuousOn.mul ?_ ((tf72f_cont (6/7) (by norm_num)).mono Set.Icc_subset_Ici_self)
        exact (((continuous_const.mul continuous_id).pow j).div_const _).continuousOn)
  rw [hfs]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [show (∫ t in (0:ℝ)..(7/3), (((792/1000:ℝ)*t)^j / ((j.factorial:ℕ):ℝ)) * tf72f (6/7) t)
      = ∫ t in (0:ℝ)..(7/3), ((792/1000:ℝ)^j / ((j.factorial:ℕ):ℝ)) * (t^j * tf72f (6/7) t) from by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      rw [mul_pow]; ring]
  rw [intervalIntegral.integral_const_mul, tf72fL_moment]

theorem tf72fL_upper_bound :
    (∫ t in (0:ℝ)..(7/3), Real.exp ((792/1000:ℝ)*t) * tf72f (6/7) t) ≤ 761/500 := by
  set S : ℝ → ℝ := fun t => ∑ j ∈ Finset.range 13, (((792/1000:ℝ)*t)^j / ((j.factorial:ℕ):ℝ)) with hS
  set R : ℝ := (((792/1000:ℝ)*(7/3))^13 / ((Nat.factorial 13:ℕ):ℝ)) * (1/(1 - (792/1000:ℝ)*(7/3)/13)) with hR
  have hSeval : ∀ t : ℝ, S t = ∑ j ∈ Finset.range 13, (((792/1000:ℝ)*t)^j / ((j.factorial:ℕ):ℝ)) := by
    intro t; simp only [hS]
  have hScont : Continuous S := by rw [hS]; fun_prop
  have htfc : ContinuousOn (tf72f (6/7)) (Set.Icc (0:ℝ) (7/3)) :=
    (tf72f_cont (6/7) (by norm_num)).mono Set.Icc_subset_Ici_self
  have hmono : (∫ t in (0:ℝ)..(7/3), Real.exp ((792/1000:ℝ)*t) * tf72f (6/7) t)
      ≤ ∫ t in (0:ℝ)..(7/3), (S t + R) * tf72f (6/7) t := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
      exact ContinuousOn.mul (by fun_prop) htfc
    · exact ((hScont.continuousOn.add continuousOn_const).mul htfc).intervalIntegrable_of_Icc (by norm_num)
    · intro x hx
      have h1 : Real.exp ((792/1000:ℝ)*x) ≤ S x + R := by
        rw [hSeval x, hR]; exact tf72fL_exp_le_taylor13 x hx.1 hx.2
      exact mul_le_mul_of_nonneg_right h1 (tf72f_nonneg (6/7) (by norm_num) x)
  have hiS : IntervalIntegrable (fun t : ℝ => S t * tf72f (6/7) t) volume (0:ℝ) (7/3) :=
    ((hScont.continuousOn.mul htfc)).intervalIntegrable_of_Icc (by norm_num)
  have hiR : IntervalIntegrable (fun t : ℝ => R * tf72f (6/7) t) volume (0:ℝ) (7/3) :=
    ((continuous_const.continuousOn.mul htfc)).intervalIntegrable_of_Icc (by norm_num)
  have key : (∫ t in (0:ℝ)..(7/3), S t * tf72f (6/7) t)
      = ∫ t in (0:ℝ)..(7/3),
        (∑ j ∈ Finset.range 13, (((792/1000:ℝ)*t)^j / ((j.factorial:ℕ):ℝ))) * tf72f (6/7) t := by
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
  have hSint : (∫ t in (0:ℝ)..(7/3), S t * tf72f (6/7) t)
      = ∑ j ∈ Finset.range 13, (((792/1000:ℝ)^j / ((j.factorial:ℕ):ℝ)) * tf72fL_mom j) := by
    rw [key, tf72fL_int_taylor_sum]
  have hRint : (∫ t in (0:ℝ)..(7/3), R * tf72f (6/7) t) = R * tf72fL_mom 0 := by
    rw [intervalIntegral.integral_const_mul, tf72fL_moment_zero]
  have hRval : (∫ t in (0:ℝ)..(7/3), (S t + R) * tf72f (6/7) t)
      = (∑ j ∈ Finset.range 13, (((792/1000:ℝ)^j / ((j.factorial:ℕ):ℝ)) * tf72fL_mom j)) + R * tf72fL_mom 0 := by
    rw [show (fun t : ℝ => (S t + R) * tf72f (6/7) t)
        = (fun t : ℝ => S t * tf72f (6/7) t + R * tf72f (6/7) t) from by funext t; ring]
    rw [intervalIntegral.integral_add hiS hiR, hSint, hRint]
  calc (∫ t in (0:ℝ)..(7/3), Real.exp ((792/1000:ℝ)*t) * tf72f (6/7) t)
      ≤ ∫ t in (0:ℝ)..(7/3), (S t + R) * tf72f (6/7) t := hmono
    _ = (∑ j ∈ Finset.range 13, (((792/1000:ℝ)^j / ((j.factorial:ℕ):ℝ)) * tf72fL_mom j)) + R * tf72fL_mom 0 := hRval
    _ ≤ 761/500 := by rw [hR]; exact tf72fL_upper_arith

theorem tf72fL_lower_bound :
    (∫ t in (0:ℝ)..(7/3), Real.exp (-(57/875:ℝ)*t) * tf72f (6/7) t) ≥ 1709/2000 := by
  have htfc : ContinuousOn (tf72f (6/7)) (Set.Icc (0:ℝ) (7/3)) :=
    (tf72f_cont (6/7) (by norm_num)).mono Set.Icc_subset_Ici_self
  have hi0 : IntervalIntegrable (fun t : ℝ => tf72f (6/7) t) volume (0:ℝ) (7/3) :=
    htfc.intervalIntegrable_of_Icc (by norm_num)
  have hi1 : IntervalIntegrable (fun t : ℝ => (57/875:ℝ) * (t^1 * tf72f (6/7) t)) volume (0:ℝ) (7/3) := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    refine ContinuousOn.mul continuousOn_const (ContinuousOn.mul ?_ htfc)
    exact (continuous_id.pow 1).continuousOn
  have hi2 : IntervalIntegrable (fun t : ℝ => ((57/875:ℝ)^2/3) * (t^2 * tf72f (6/7) t)) volume (0:ℝ) (7/3) := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    refine ContinuousOn.mul continuousOn_const (ContinuousOn.mul ?_ htfc)
    exact (continuous_id.pow 2).continuousOn
  have hi3 : IntervalIntegrable (fun t : ℝ => ((57/875:ℝ)^3/27) * (t^3 * tf72f (6/7) t)) volume (0:ℝ) (7/3) := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    refine ContinuousOn.mul continuousOn_const (ContinuousOn.mul ?_ htfc)
    exact (continuous_id.pow 3).continuousOn
  have hint : (∫ t in (0:ℝ)..(7/3), (1 - (57/875:ℝ)*t/3)^3 * tf72f (6/7) t)
      = tf72fL_mom 0 - (57/875:ℝ)*tf72fL_mom 1 + ((57/875:ℝ)^2/3)*tf72fL_mom 2 - ((57/875:ℝ)^3/27)*tf72fL_mom 3 := by
    rw [show (∫ t in (0:ℝ)..(7/3), (1 - (57/875:ℝ)*t/3)^3 * tf72f (6/7) t)
        = ∫ t in (0:ℝ)..(7/3), ((tf72f (6/7) t - (57/875:ℝ)*(t^1 * tf72f (6/7) t))
            + (((57/875:ℝ)^2/3)*(t^2 * tf72f (6/7) t) - ((57/875:ℝ)^3/27)*(t^3 * tf72f (6/7) t))) from by
        apply intervalIntegral.integral_congr
        intro t _
        ring]
    rw [intervalIntegral.integral_add (hi0.sub hi1) (hi2.sub hi3),
        intervalIntegral.integral_sub hi0 hi1,
        intervalIntegral.integral_sub hi2 hi3]
    simp only [tf72fL_moment_zero, tf72fL_int_const_moment]
    ring
  have hmono : (∫ t in (0:ℝ)..(7/3), (1 - (57/875:ℝ)*t/3)^3 * tf72f (6/7) t)
      ≤ ∫ t in (0:ℝ)..(7/3), Real.exp (-(57/875:ℝ)*t) * tf72f (6/7) t := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
      refine ContinuousOn.mul ?_ htfc
      fun_prop
    · apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
      exact ContinuousOn.mul (by fun_prop) htfc
    · intro x hx
      have hyp : (1 - (57/875:ℝ)*x/3)^3 ≤ Real.exp (-((57/875:ℝ)*x)) := by
        refine tf72fL_exp_neg_ge_cubic ((57/875:ℝ)*x) (mul_nonneg (by norm_num) hx.1) ?_
        have h1 : (57/875:ℝ)*x ≤ (57/875:ℝ)*(7/3) := mul_le_mul_of_nonneg_left hx.2 (by norm_num)
        have h2 : (57/875:ℝ)*(7/3) ≤ 3 := by norm_num
        linarith
      have h3 : -((57/875:ℝ)*x) = -(57/875:ℝ)*x := by ring
      rw [h3] at hyp
      exact mul_le_mul_of_nonneg_right hyp (tf72f_nonneg (6/7) (by norm_num) x)
  calc 1709/2000 ≤ (∫ t in (0:ℝ)..(7/3), (1 - (57/875:ℝ)*t/3)^3 * tf72f (6/7) t) := by
        rw [hint]; exact tf72fL_lower_arith
    _ ≤ ∫ t in (0:ℝ)..(7/3), Real.exp (-(57/875:ℝ)*t) * tf72f (6/7) t := hmono

theorem tf72f_laplace_counterexample_bounds :
    (∫ t in (0:ℝ)..(2/(6/7)), Real.exp ((792/1000) * t) * tf72f (6/7) t ≤ 761/500) ∧
    (∫ t in (0:ℝ)..(2/(6/7)), Real.exp (-(57/875) * t) * tf72f (6/7) t ≥ 1709/2000) := by
  have hT : (2:ℝ)/(6/7) = 7/3 := by norm_num
  constructor
  · rw [hT]; exact tf72fL_upper_bound
  · rw [hT]; exact tf72fL_lower_bound


/-! ## The `F`-method consequence: the failure of HB (10.7) at `λ = 6/7`

`tf72f_laplace_counterexample_bounds` bounds the two Laplace values
`F(-792/1000) ≤ 761/500` and `F(57/875) ≥ 1709/2000` that the `F`-method combination
`F(−6/7) − F(−λ₁) ≤ 2(F 0 − F(6/7 − λ₁))` needs at `λ₁ = 792/1000`.  Together with the
sharp values `F(0) = 8/9` (`tf72f_intervalIntegral`) and `F(−6/7) = 8/5`
(`integral_exp_tf72f`) they make the combination *false* at the endpoint, with the strict
numerical margin `39/500 − 619/9000 = 7/4500 > 0`:

* `F(−6/7) − F(−792/1000) ≥ 8/5 − 761/500 = 39/500`,
* `2(F 0 − F(57/875)) ≤ 2(8/9 − 1709/2000) = 619/9000`.

The only further input needed to extend the failure to the whole interval
`[0, 792/1000]` is that the comparison function `lam ↦ F(−lam) − 2F(6/7 − lam)` is maximal
at `lam = 792/1000` (the hypothesis `hmono` below, itself a statement about `tf72f (6/7)`
delegated separately). -/

/-- The sharp value `F(-6/7) = 8/5` for HB's test function at `λ = 6/7`. -/
lemma tf72f_exp67_int : (∫ t in (0:ℝ)..(7/3), Real.exp ((6/7:ℝ)*t) * tf72f (6/7) t) = 8/5 := by
  have h := integral_exp_tf72f (6/7) (by norm_num)
  rwa [show (2:ℝ)/(6/7) = 7/3 by norm_num] at h

/-- The sharp value `F(0) = 8/9` for HB's test function at `λ = 6/7`. -/
lemma tf72f_zero_int : (∫ t in (0:ℝ)..(7/3), tf72f (6/7) t) = 8/9 := by
  have h := tf72f_intervalIntegral (6/7) (by norm_num)
  rwa [show (2:ℝ)/(6/7) = 7/3 by norm_num] at h

/-- **The `F`-method combination (HB (10.7)) fails for HB Lemma 7.2's test function at
`λ = 6/7`.**  If the comparison function `lam ↦ F(−lam) − 2F(6/7 − lam)` is maximal at
`lam = 792/1000` (hypothesis `hmono`), then for every `0 ≤ lam₁ ≤ 792/1000`

`F(−6/7) − F(−lam₁) > 2 (F 0 − F(6/7 − lam₁))`;

the endpoint case `lam₁ = 792/1000` is the content of
`tf72f_laplace_counterexample_bounds` together with the sharp values `F(0) = 8/9`,
`F(−6/7) = 8/5`. -/
theorem tf72f_laplace_counterexample_refute
    (hmono : ∀ lam : ℝ, 0 ≤ lam → lam ≤ 792/1000 →
      (∫ t in (0:ℝ)..(7/3), Real.exp (lam * t) * tf72f (6/7) t)
        - 2 * (∫ t in (0:ℝ)..(7/3), Real.exp (-((6/7 - lam) * t)) * tf72f (6/7) t)
      ≤ (∫ t in (0:ℝ)..(7/3), Real.exp ((792/1000:ℝ) * t) * tf72f (6/7) t)
        - 2 * (∫ t in (0:ℝ)..(7/3), Real.exp (-(57/875:ℝ) * t) * tf72f (6/7) t)) :
    ∀ lam₁ : ℝ, 0 ≤ lam₁ → lam₁ ≤ 792/1000 →
      (∫ t in (0:ℝ)..(7/3), Real.exp ((6/7:ℝ) * t) * tf72f (6/7) t)
        - (∫ t in (0:ℝ)..(7/3), Real.exp (lam₁ * t) * tf72f (6/7) t)
      > 2 * ((∫ t in (0:ℝ)..(7/3), tf72f (6/7) t)
        - (∫ t in (0:ℝ)..(7/3), Real.exp (-((6/7 - lam₁) * t)) * tf72f (6/7) t)) := by
  intro lam₁ h0 h1
  have hE := tf72f_exp67_int
  have hZ := tf72f_zero_int
  have hb1 := (tf72f_laplace_counterexample_bounds).1
  have hb2 := (tf72f_laplace_counterexample_bounds).2
  have hm := hmono lam₁ h0 h1
  linarith


/-! ## The engine-facing form of the refutation -/

/-- `T.F` of a test function with `x₀ = 7/3` and `f = tf72f (6/7)` is the explicit
`tf72f (6/7)`-integral. -/
lemma F_eq_tf72f_int (T : TestFn) (hx0 : T.x₀ = 7/3) (hf : T.f = tf72f (6/7)) (z : ℝ) :
    T.F z = ∫ t in (0:ℝ)..(7/3), Real.exp (-(z * t)) * tf72f (6/7) t := by
  rw [TestFn_F_eq_integral, hx0, hf]

/-- **The `F`-method combination (HB (10.7)) fails for HB Lemma 7.2's test function at
`λ = 6/7`**, stated in the `TestFn.F` vocabulary of the `F`-method engine: for every
`0 ≤ lam₁ ≤ 792/1000`,

`F(−6/7) − F(−lam₁) > 2 (F 0 − F(6/7 − lam₁))`.

The hypothesis `hmono` (the comparison function is maximal at `lam = 792/1000`) is the
only extra input; it is discharged unconditionally by `tf72f_gap_mono`
(`Submission.Work.ZeroFreeTables.tf72f_gap_mono`). -/
theorem tf72f_refute_TestFn
    (T : TestFn) (hx0 : T.x₀ = 7/3) (hf : T.f = tf72f (6/7))
    (_hF0 : T.F 0 = 8/9) (_hF6 : T.F (-(6/7)) = 8/5)
    (hmono : ∀ lam : ℝ, 0 ≤ lam → lam ≤ 792/1000 →
      T.F (-lam) - 2 * T.F (6/7 - lam) ≤ T.F (-(792/1000)) - 2 * T.F (57/875)) :
    ∀ lam₁ : ℝ, 0 ≤ lam₁ → lam₁ ≤ 792/1000 →
      T.F (-(6/7)) - T.F (-lam₁) > 2 * (T.F 0 - T.F (6/7 - lam₁)) := by
  have hA : T.F (-(6/7)) = ∫ t in (0:ℝ)..(7/3), Real.exp ((6/7:ℝ) * t) * tf72f (6/7) t := by
    rw [F_eq_tf72f_int T hx0 hf]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [show -((-(6/7:ℝ)) * t) = (6/7:ℝ) * t from by ring]
  have hB : ∀ z : ℝ, T.F (-z) = ∫ t in (0:ℝ)..(7/3), Real.exp (z * t) * tf72f (6/7) t := by
    intro z
    rw [F_eq_tf72f_int T hx0 hf]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [show -((-z) * t) = z * t from by ring]
  have hD : ∀ z : ℝ, T.F z = ∫ t in (0:ℝ)..(7/3), Real.exp (-(z * t)) * tf72f (6/7) t :=
    fun z => F_eq_tf72f_int T hx0 hf z
  have hC : T.F (-(792/1000)) = ∫ t in (0:ℝ)..(7/3),
      Real.exp ((792/1000:ℝ) * t) * tf72f (6/7) t := by
    rw [F_eq_tf72f_int T hx0 hf]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [show -((-(792/1000:ℝ)) * t) = (792/1000:ℝ) * t from by ring]
  have hQ : T.F (57/875) = ∫ t in (0:ℝ)..(7/3),
      Real.exp (-(57/875:ℝ) * t) * tf72f (6/7) t := by
    rw [F_eq_tf72f_int T hx0 hf]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [show -(((57/875:ℝ)) * t) = -(57/875:ℝ) * t from by ring]
  have hmono' : ∀ lam : ℝ, 0 ≤ lam → lam ≤ 792/1000 →
      (∫ t in (0:ℝ)..(7/3), Real.exp (lam * t) * tf72f (6/7) t)
        - 2 * (∫ t in (0:ℝ)..(7/3), Real.exp (-((6/7 - lam) * t)) * tf72f (6/7) t)
      ≤ (∫ t in (0:ℝ)..(7/3), Real.exp ((792/1000:ℝ) * t) * tf72f (6/7) t)
        - 2 * (∫ t in (0:ℝ)..(7/3), Real.exp (-(57/875:ℝ) * t) * tf72f (6/7) t) := by
    intro lam h0 h1
    have hm := hmono lam h0 h1
    rw [hB lam, hD (6/7 - lam), hC, hQ] at hm
    exact hm
  intro lam₁ h0 h1
  have hres := tf72f_laplace_counterexample_refute hmono' lam₁ h0 h1
  rw [tf72f_zero_int] at hres
  rw [hA, hB lam₁, _hF0, hD (6/7 - lam₁)]
  exact hres


/-! ## Unconditional forms (discharging `hmono` via `tf72f_gap_mono`) -/

/-- Unconditional form of `tf72f_laplace_counterexample_refute`: the `F`-method
combination fails for `tf72f (6/7)` on the whole interval `[0, 792/1000]`. -/
theorem tf72f_laplace_counterexample_refute_uncond :
    ∀ lam₁ : ℝ, 0 ≤ lam₁ → lam₁ ≤ 792/1000 →
      (∫ t in (0:ℝ)..(7/3), Real.exp ((6/7:ℝ) * t) * tf72f (6/7) t)
        - (∫ t in (0:ℝ)..(7/3), Real.exp (lam₁ * t) * tf72f (6/7) t)
      > 2 * ((∫ t in (0:ℝ)..(7/3), tf72f (6/7) t)
        - (∫ t in (0:ℝ)..(7/3), Real.exp (-((6/7 - lam₁) * t)) * tf72f (6/7) t)) :=
  tf72f_laplace_counterexample_refute tf72f_gap_mono

/-- Unconditional engine-facing form of the refutation: for **every** test function
`T` with `x₀ = 7/3`, `f = tf72f (6/7)`, `F 0 = 8/9`, `F (-6/7) = 8/5` and every
`0 ≤ lam₁ ≤ 792/1000`, `F(−6/7) − F(−lam₁) > 2 (F 0 − F(6/7 − lam₁))`. -/
theorem tf72f_refute_TestFn_uncond
    (T : TestFn) (hx0 : T.x₀ = 7/3) (hf : T.f = tf72f (6/7))
    (hF0 : T.F 0 = 8/9) (hF6 : T.F (-(6/7)) = 8/5) :
    ∀ lam₁ : ℝ, 0 ≤ lam₁ → lam₁ ≤ 792/1000 →
      T.F (-(6/7)) - T.F (-lam₁) > 2 * (T.F 0 - T.F (6/7 - lam₁)) := by
  refine tf72f_refute_TestFn T hx0 hf hF0 hF6 (fun lam h0 h1 => ?_)
  have hB : T.F (-lam) = ∫ t in (0:ℝ)..(7/3), Real.exp (lam * t) * tf72f (6/7) t := by
    rw [F_eq_tf72f_int T hx0 hf]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [show -((-lam) * t) = lam * t from by ring]
  have hD : T.F (6/7 - lam)
      = ∫ t in (0:ℝ)..(7/3), Real.exp (-((6/7 - lam) * t)) * tf72f (6/7) t :=
    F_eq_tf72f_int T hx0 hf (6/7 - lam)
  have hC : T.F (-(792/1000))
      = ∫ t in (0:ℝ)..(7/3), Real.exp ((792/1000:ℝ) * t) * tf72f (6/7) t := by
    rw [F_eq_tf72f_int T hx0 hf]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [show -((-(792/1000:ℝ)) * t) = (792/1000:ℝ) * t from by ring]
  have hQ : T.F (57/875)
      = ∫ t in (0:ℝ)..(7/3), Real.exp (-(57/875:ℝ) * t) * tf72f (6/7) t := by
    rw [F_eq_tf72f_int T hx0 hf]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [show -(((57/875:ℝ)) * t) = -(57/875:ℝ) * t from by ring]
  rw [hB, hD, hC, hQ]
  exact tf72f_gap_mono lam h0 h1

end Work.ZeroFreeTables
