/-
# ZeroFreeTables.OffAxis — tf72f_moment_step

The "moment step" locating the crossover point `l` in the off-axis argument for
Heath-Brown's test function `tf72f` at the limiting slope `λ = 6/7`.

With `f = tf72f (6/7)`, `A = ∫₀^{7/3} e^{(6/7)t} f`, `B = ∫₀^{7/3} e^{lt} f`,
`C = ∫₀^{7/3} e^{-(6/7-l)t} f` and `u = 6/7 - l > 0`, the hypothesis

`A - B ≤ 2 (∫f - C) + s`   (`0 ≤ s ≤ ε/10000`)

is the inequality `K(u) ≤ s`, where

`K(u) = 2C - B + A - 2∫f = ∫₀^{7/3} (1 - e^{-ut}) (e^{(6/7)t} - 2) f(t) dt`.

The proof establishes the lower bound `K(u) ≥ u/5000` whenever
`0 ≤ u ≤ 6/7 - 792/1000 = 57/875`; then `u > ε/2` forces
`K(u) > ε/10000 ≥ s`, a contradiction, so `l ≤ 792/1000` or `l ≥ 6/7 - ε/2`.

The numerical input on `f` is
`∫₀^{7/3} t e^{(6/7)t} f ≥ 61/50` (true value `56/45`), obtained from the Taylor
bound `e^x ≥ Σ_{k<5} x^k/k!` and the exact moments `tf72f_moment k`, together
with `∫ t f = 8/15`, `∫ t² f = 196/405` and `e^{(6/7)t} ≤ 9` on `[0,7/3]`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.testFn72_defs
import Submission.Work.ZeroFreeTables.tf72f_moment

noncomputable section
open scoped Interval
open MeasureTheory
namespace Work.ZeroFreeTables.OffAxis
open Work.ZeroFreeTables

lemma one_sub_exp_neg_le (x : ℝ) : 1 - Real.exp (-x) ≤ x := by
  linarith [Real.one_sub_le_exp_neg x]

lemma sub_sq_half_le_one_sub_exp_neg (x : ℝ) (hx : 0 ≤ x) :
    x - x^2/2 ≤ 1 - Real.exp (-x) := by
  have hexp : (1:ℝ) + x + x^2/2 ≤ Real.exp x := by
    have h := Real.sum_le_exp_of_nonneg hx 3
    simpa [Finset.sum_range_succ, Nat.factorial, pow_succ, Nat.cast_ofNat] using h
  have hpos : 0 < 1 + x + x^2/2 := by positivity
  have hinv : 1 / Real.exp x ≤ 1 / (1 + x + x^2/2) := one_div_le_one_div_of_le hpos hexp
  have hineq : 1 / (1 + x + x^2/2) ≤ 1 - x + x^2/2 := by
    rw [div_le_iff₀ hpos]; nlinarith [sq_nonneg x]
  rw [Real.exp_neg]
  simp only [one_div] at hinv hineq
  linarith

def S72 (t : ℝ) : ℝ := ∑ k ∈ Finset.range 5, ((6/7:ℝ)*t)^k / (Nat.factorial k : ℝ)

lemma moment1 : (∫ t in (0:ℝ)..(7/3), t^1 * tf72f (6/7) t) = 8/15 := by
  rw [tf72f_moment 1]; norm_num
lemma moment2 : (∫ t in (0:ℝ)..(7/3), t^2 * tf72f (6/7) t) = 196/405 := by
  rw [tf72f_moment 2]; norm_num
lemma moment3 : (∫ t in (0:ℝ)..(7/3), t^3 * tf72f (6/7) t) = 392/729 := by
  rw [tf72f_moment 3]; norm_num
lemma moment4 : (∫ t in (0:ℝ)..(7/3), t^4 * tf72f (6/7) t) = 1372/2025 := by
  rw [tf72f_moment 4]; norm_num
lemma moment5 : (∫ t in (0:ℝ)..(7/3), t^5 * tf72f (6/7) t) = 67228/72171 := by
  rw [tf72f_moment 5]; norm_num

lemma tf72f_contOn : ContinuousOn (fun t : ℝ => tf72f (6/7) t) (Set.uIcc (0:ℝ) (7/3)) :=
  (tf72f_cont (6/7) (by norm_num)).mono (fun x hx => by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 7/3)] at hx
    exact hx.1)

lemma expMoment_lower :
    (61:ℝ)/50 ≤ ∫ t in (0:ℝ)..(7/3), t * Real.exp ((6/7:ℝ)*t) * tf72f (6/7) t := by
  have hpt : ∀ t ∈ Set.Icc (0:ℝ) (7/3),
      t * S72 t * tf72f (6/7) t ≤ t * Real.exp ((6/7:ℝ)*t) * tf72f (6/7) t := by
    intro t ht
    have hSle : S72 t ≤ Real.exp ((6/7:ℝ)*t) := by
      have h := Real.sum_le_exp_of_nonneg (x := (6/7:ℝ)*t) (mul_nonneg (by norm_num) ht.1) 5
      simpa [S72] using h
    have hf0 : 0 ≤ tf72f (6/7) t := tf72f_nonneg (6/7) (by norm_num) t
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSle ht.1) hf0
  have hInt1 : IntervalIntegrable (fun t : ℝ => t * S72 t * tf72f (6/7) t) volume (0:ℝ) (7/3) := by
    have hS : ContinuousOn (fun t : ℝ => S72 t) (Set.uIcc (0:ℝ) (7/3)) := by
      apply continuousOn_finsetSum
      intro k hk
      exact (((continuousOn_const.mul continuousOn_id).pow k).div_const _)
    exact ((continuousOn_id.mul hS).mul tf72f_contOn).intervalIntegrable
  have hInt2 : IntervalIntegrable (fun t : ℝ => t * Real.exp ((6/7:ℝ)*t) * tf72f (6/7) t) volume (0:ℝ) (7/3) := by
    have hcont : ContinuousOn (fun t : ℝ => t * Real.exp ((6/7:ℝ)*t) * tf72f (6/7) t) (Set.uIcc (0:ℝ) (7/3)) :=
      (continuousOn_id.mul (by fun_prop)).mul tf72f_contOn
    exact hcont.intervalIntegrable
  have hmono := intervalIntegral.integral_mono_on (f := fun t => t * S72 t * tf72f (6/7) t)
    (g := fun t => t * Real.exp ((6/7:ℝ)*t) * tf72f (6/7) t) (by norm_num) hInt1 hInt2 hpt
  have hIntS : (∫ t in (0:ℝ)..(7/3), t * S72 t * tf72f (6/7) t)
      = ∑ k ∈ Finset.range 5, ((6/7:ℝ)^k / (Nat.factorial k : ℝ)) *
          (∫ t in (0:ℝ)..(7/3), t^(k+1) * tf72f (6/7) t) := by
    rw [show (∫ t in (0:ℝ)..(7/3), t * S72 t * tf72f (6/7) t)
        = ∫ t in (0:ℝ)..(7/3), ∑ k ∈ Finset.range 5,
            ((6/7:ℝ)^k / (Nat.factorial k : ℝ)) * (t^(k+1) * tf72f (6/7) t) from by
      apply intervalIntegral.integral_congr
      intro t _
      simp only [S72]
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk; rw [mul_pow]; ring_nf]
    rw [intervalIntegral.integral_finsetSum (h := ?_)]
    · apply Finset.sum_congr rfl
      intro k hk
      rw [intervalIntegral.integral_const_mul]
    · intro k hk
      exact ((continuousOn_const.mul ((continuousOn_id.pow _).mul tf72f_contOn))).intervalIntegrable
  have hsum : (61:ℝ)/50 ≤ ∑ k ∈ Finset.range 5, ((6/7:ℝ)^k / (Nat.factorial k : ℝ)) *
          (∫ t in (0:ℝ)..(7/3), t^(k+1) * tf72f (6/7) t) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [moment1, moment2, moment3, moment4, moment5]
    norm_num
  linarith [hmono, hIntS ▸ hsum]

def W72 (t : ℝ) : ℝ := (Real.exp ((6/7:ℝ)*t) - 2) * tf72f (6/7) t

def Kfun (u : ℝ) : ℝ := ∫ t in (0:ℝ)..(7/3), (1 - Real.exp (-(u*t))) * W72 t

lemma exp_lam_le_nine (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) (7/3)) :
    Real.exp ((6/7:ℝ)*t) ≤ 9 := by
  have h2 : (6/7:ℝ)*t ≤ 2 := by nlinarith [ht.1, ht.2]
  calc Real.exp ((6/7:ℝ)*t) ≤ Real.exp 2 := Real.exp_le_exp.mpr h2
    _ = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    _ ≤ 9 := by
      have h3 := Real.exp_one_lt_three
      nlinarith [Real.exp_pos 1]

lemma abs_exp_lam_sub_two_le_nine (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) (7/3)) :
    |Real.exp ((6/7:ℝ)*t) - 2| ≤ 9 := by
  have h1 := exp_lam_le_nine t ht
  have h2 : (1:ℝ) ≤ Real.exp ((6/7:ℝ)*t) := by
    have := Real.exp_le_exp.mpr (show (0:ℝ) ≤ (6/7)*t by nlinarith [ht.1])
    rwa [Real.exp_zero] at this
  rw [abs_le]
  constructor <;> linarith

lemma W72_contOn : ContinuousOn (fun t : ℝ => W72 t) (Set.uIcc (0:ℝ) (7/3)) := by
  unfold W72
  exact ((by fun_prop : ContinuousOn (fun t : ℝ => Real.exp ((6/7:ℝ)*t) - 2) (Set.uIcc (0:ℝ) (7/3)))).mul tf72f_contOn

lemma tsq_absW_le : (∫ t in (0:ℝ)..(7/3), t^2 * |W72 t|) ≤ 196/45 := by
  have hpt : ∀ t ∈ Set.Icc (0:ℝ) (7/3), t^2 * |W72 t| ≤ 9 * (t^2 * tf72f (6/7) t) := by
    intro t ht
    have hf0 : 0 ≤ tf72f (6/7) t := tf72f_nonneg (6/7) (by norm_num) t
    have h9 := abs_exp_lam_sub_two_le_nine t ht
    have hW : |W72 t| ≤ 9 * tf72f (6/7) t := by
      unfold W72
      rw [abs_mul, abs_of_nonneg hf0]
      exact mul_le_mul_of_nonneg_right h9 hf0
    have ht2 : 0 ≤ t^2 := sq_nonneg t
    calc t^2 * |W72 t| ≤ t^2 * (9 * tf72f (6/7) t) := by nlinarith [hW, ht2]
      _ = 9 * (t^2 * tf72f (6/7) t) := by ring
  have h1 : IntervalIntegrable (fun t : ℝ => t^2 * |W72 t|) volume (0:ℝ) (7/3) := by
    have hc : ContinuousOn (fun t : ℝ => t^2 * |W72 t|) (Set.uIcc (0:ℝ) (7/3)) :=
      ((continuousOn_id.pow 2).mul W72_contOn.abs)
    exact hc.intervalIntegrable
  have h2 : IntervalIntegrable (fun t : ℝ => 9 * (t^2 * tf72f (6/7) t)) volume (0:ℝ) (7/3) := by
    have hc : ContinuousOn (fun t : ℝ => 9 * (t^2 * tf72f (6/7) t)) (Set.uIcc (0:ℝ) (7/3)) :=
      continuousOn_const.mul ((continuousOn_id.pow 2).mul tf72f_contOn)
    exact hc.intervalIntegrable
  have hmono := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 7/3) h1 h2 hpt
  have hval : (∫ t in (0:ℝ)..(7/3), 9 * (t^2 * tf72f (6/7) t)) = 196/45 := by
    rw [intervalIntegral.integral_const_mul, moment2]
    norm_num
  rw [hval] at hmono
  exact hmono

lemma tW_lower : (23:ℝ)/150 ≤ ∫ t in (0:ℝ)..(7/3), t * W72 t := by
  have h1 : IntervalIntegrable (fun t : ℝ => t * Real.exp ((6/7:ℝ)*t) * tf72f (6/7) t) volume (0:ℝ) (7/3) := by
    have hc : ContinuousOn (fun t : ℝ => t * Real.exp ((6/7:ℝ)*t) * tf72f (6/7) t) (Set.uIcc (0:ℝ) (7/3)) :=
      (continuousOn_id.mul (by fun_prop)).mul tf72f_contOn
    exact hc.intervalIntegrable
  have h2 : IntervalIntegrable (fun t : ℝ => 2 * (t^1 * tf72f (6/7) t)) volume (0:ℝ) (7/3) := by
    have hc : ContinuousOn (fun t : ℝ => 2 * (t^1 * tf72f (6/7) t)) (Set.uIcc (0:ℝ) (7/3)) :=
      continuousOn_const.mul ((continuousOn_id.pow 1).mul tf72f_contOn)
    exact hc.intervalIntegrable
  have hcongr : (∫ t in (0:ℝ)..(7/3), t * W72 t)
      = (∫ t in (0:ℝ)..(7/3), t * Real.exp ((6/7:ℝ)*t) * tf72f (6/7) t)
        - 2 * (∫ t in (0:ℝ)..(7/3), t^1 * tf72f (6/7) t) := by
    have heq : (fun t : ℝ => t * W72 t)
        = fun t : ℝ => t * Real.exp ((6/7:ℝ)*t) * tf72f (6/7) t
            - 2 * (t^1 * tf72f (6/7) t) := by
      funext t; unfold W72; ring
    rw [heq, intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_const_mul]
  rw [hcongr]
  linarith [expMoment_lower, moment1]

lemma Kfun_lower (u : ℝ) (hu : 0 ≤ u) (hu2 : u ≤ 57/875) : u/5000 ≤ Kfun u := by
  have hg0 : ∀ t ∈ Set.Icc (0:ℝ) (7/3), 0 ≤ u*t - (1 - Real.exp (-(u*t))) := by
    intro t ht
    have := one_sub_exp_neg_le (u*t)
    linarith
  have hgub : ∀ t ∈ Set.Icc (0:ℝ) (7/3), u*t - (1 - Real.exp (-(u*t))) ≤ (u*t)^2/2 := by
    intro t ht
    have hx : 0 ≤ u*t := mul_nonneg hu ht.1
    have := sub_sq_half_le_one_sub_exp_neg (u*t) hx
    linarith
  have hcontg : ContinuousOn (fun t : ℝ => u*t - (1 - Real.exp (-(u*t)))) (Set.uIcc (0:ℝ) (7/3)) :=
    (continuousOn_const.mul continuousOn_id).sub (continuousOn_const.sub (by fun_prop))
  have hgI : IntervalIntegrable (fun t : ℝ => (u*t - (1 - Real.exp (-(u*t)))) * W72 t) volume (0:ℝ) (7/3) :=
    (hcontg.mul W72_contOn).intervalIntegrable
  have hgabsI : IntervalIntegrable (fun t : ℝ => (u*t - (1 - Real.exp (-(u*t)))) * |W72 t|) volume (0:ℝ) (7/3) :=
    (hcontg.mul W72_contOn.abs).intervalIntegrable
  have htWI : IntervalIntegrable (fun t : ℝ => u*t * W72 t) volume (0:ℝ) (7/3) :=
    (((continuousOn_const.mul continuousOn_id).mul W72_contOn)).intervalIntegrable
  have hsplit : Kfun u = u * (∫ t in (0:ℝ)..(7/3), t * W72 t)
      - (∫ t in (0:ℝ)..(7/3), (u*t - (1 - Real.exp (-(u*t)))) * W72 t) := by
    rw [Kfun]
    have heq : (fun t : ℝ => (1 - Real.exp (-(u*t))) * W72 t)
        = fun t : ℝ => u*t * W72 t - (u*t - (1 - Real.exp (-(u*t)))) * W72 t := by
      funext t; ring
    rw [heq, intervalIntegral.integral_sub htWI hgI]
    rw [show (∫ t in (0:ℝ)..(7/3), u*t * W72 t) = u * (∫ t in (0:ℝ)..(7/3), t * W72 t) from by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _; ring]
  rw [hsplit]
  have hstep1 : (∫ t in (0:ℝ)..(7/3), (u*t - (1 - Real.exp (-(u*t)))) * W72 t)
      ≤ ∫ t in (0:ℝ)..(7/3), (u*t - (1 - Real.exp (-(u*t)))) * |W72 t| := by
    apply intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 7/3) hgI hgabsI
    intro t ht
    have hg := hg0 t ht
    nlinarith [le_abs_self (W72 t)]
  have hstep2 : (∫ t in (0:ℝ)..(7/3), (u*t - (1 - Real.exp (-(u*t)))) * |W72 t|)
      ≤ (u^2/2) * (∫ t in (0:ℝ)..(7/3), t^2 * |W72 t|) := by
    have h2 : IntervalIntegrable (fun t : ℝ => (u^2/2) * (t^2 * |W72 t|)) volume (0:ℝ) (7/3) :=
      (continuousOn_const.mul ((continuousOn_id.pow 2).mul W72_contOn.abs)).intervalIntegrable
    have hmono := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 7/3) hgabsI h2 (fun t ht => by
      have hg := hgub t ht
      have ha : 0 ≤ |W72 t| := abs_nonneg _
      nlinarith)
    rw [intervalIntegral.integral_const_mul] at hmono
    exact hmono
  have hA : u * (23/150) ≤ u * (∫ t in (0:ℝ)..(7/3), t * W72 t) :=
    mul_le_mul_of_nonneg_left tW_lower hu
  have hB : (u^2/2) * (∫ t in (0:ℝ)..(7/3), t^2 * |W72 t|) ≤ (u^2/2) * (196/45) :=
    mul_le_mul_of_nonneg_left tsq_absW_le (by positivity)
  have hb1 : (∫ t in (0:ℝ)..(7/3), (u*t - (1 - Real.exp (-(u*t)))) * |W72 t|) ≤ (u^2/2) * (196/45) :=
    le_trans hstep2 hB
  have hb2 : (∫ t in (0:ℝ)..(7/3), (u*t - (1 - Real.exp (-(u*t)))) * W72 t) ≤ (u^2/2) * (196/45) :=
    le_trans hstep1 hb1
  have hkey : u * (23/150) - (u^2/2) * (196/45) ≤ u * (∫ t in (0:ℝ)..(7/3), t * W72 t)
      - (∫ t in (0:ℝ)..(7/3), (u*t - (1 - Real.exp (-(u*t)))) * W72 t) := by linarith [hb2, hA]
  have hfin : u/5000 ≤ u * (23/150) - (u^2/2) * (196/45) := by
    have h1 : u^2 * (98/45) ≤ u * ((57:ℝ)/875 * (98/45)) := by
      nlinarith [mul_le_mul_of_nonneg_left hu2 hu, hu]
    have hnum : (57:ℝ)/875 * (98/45) ≤ 23/150 - 1/5000 := by norm_num
    have h2 : u * ((57:ℝ)/875 * (98/45)) ≤ u * (23/150 - 1/5000) :=
      mul_le_mul_of_nonneg_left hnum hu
    have he : (u^2/2) * (196/45) = u^2 * (98/45) := by ring
    nlinarith [h1, h2, he]
  linarith [hkey, hfin]

end Work.ZeroFreeTables.OffAxis

namespace Work.ZeroFreeTables.OffAxis
open Work.ZeroFreeTables

lemma K_identity (l : ℝ) :
    2 * (∫ t in (0:ℝ)..(7/3), Real.exp (-(((6/7:ℝ) - l) * t)) * tf72f (6/7) t)
      - (∫ t in (0:ℝ)..(7/3), Real.exp (l*t) * tf72f (6/7) t)
      + (∫ t in (0:ℝ)..(7/3), Real.exp ((6/7:ℝ)*t) * tf72f (6/7) t)
      - 2 * (∫ t in (0:ℝ)..(7/3), tf72f (6/7) t)
    = Kfun ((6/7:ℝ) - l) := by
  have hfI : IntervalIntegrable (fun t : ℝ => tf72f (6/7) t) volume (0:ℝ) (7/3) :=
    tf72f_contOn.intervalIntegrable
  have hT1 : IntervalIntegrable (fun t : ℝ => Real.exp ((6/7:ℝ)*t) * tf72f (6/7) t) volume (0:ℝ) (7/3) :=
    (((by fun_prop : ContinuousOn (fun t : ℝ => Real.exp ((6/7:ℝ)*t)) (Set.uIcc (0:ℝ) (7/3)))).mul tf72f_contOn).intervalIntegrable
  have hT2 : IntervalIntegrable (fun t : ℝ => 2 * tf72f (6/7) t) volume (0:ℝ) (7/3) :=
    (continuousOn_const.mul tf72f_contOn).intervalIntegrable
  have hT3 : IntervalIntegrable (fun t : ℝ => Real.exp (l*t) * tf72f (6/7) t) volume (0:ℝ) (7/3) :=
    (((by fun_prop : ContinuousOn (fun t : ℝ => Real.exp (l*t)) (Set.uIcc (0:ℝ) (7/3)))).mul tf72f_contOn).intervalIntegrable
  have hT4 : IntervalIntegrable (fun t : ℝ => 2 * (Real.exp (-(((6/7:ℝ)-l)*t)) * tf72f (6/7) t)) volume (0:ℝ) (7/3) :=
    (continuousOn_const.mul (((by fun_prop : ContinuousOn (fun t : ℝ => Real.exp (-(((6/7:ℝ)-l)*t))) (Set.uIcc (0:ℝ) (7/3)))).mul tf72f_contOn)).intervalIntegrable
  have hpt : ∀ t : ℝ, (1 - Real.exp (-(((6/7:ℝ)-l)*t))) * ((Real.exp ((6/7:ℝ)*t) - 2) * tf72f (6/7) t)
      = (Real.exp ((6/7:ℝ)*t) * tf72f (6/7) t - 2 * tf72f (6/7) t)
        - (Real.exp (l*t) * tf72f (6/7) t - 2 * (Real.exp (-(((6/7:ℝ)-l)*t)) * tf72f (6/7) t)) := by
    intro t
    have hexp : Real.exp (-(((6/7:ℝ)-l)*t)) * Real.exp ((6/7:ℝ)*t) = Real.exp (l*t) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [show (1 - Real.exp (-(((6/7:ℝ)-l)*t))) * ((Real.exp ((6/7:ℝ)*t) - 2) * tf72f (6/7) t)
        = Real.exp ((6/7:ℝ)*t) * tf72f (6/7) t - 2 * tf72f (6/7) t
          - (Real.exp (-(((6/7:ℝ)-l)*t)) * Real.exp ((6/7:ℝ)*t)) * tf72f (6/7) t
          + 2 * (Real.exp (-(((6/7:ℝ)-l)*t)) * tf72f (6/7) t) from by ring]
    rw [hexp]
    ring
  unfold Kfun W72
  rw [intervalIntegral.integral_congr (fun t _ => hpt t)]
  rw [intervalIntegral.integral_sub (hT1.sub hT2) (hT3.sub hT4),
      intervalIntegral.integral_sub hT1 hT2, intervalIntegral.integral_sub hT3 hT4,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  ring

end Work.ZeroFreeTables.OffAxis

namespace Work.ZeroFreeTables.OffAxis
open Work.ZeroFreeTables

theorem tf72f_moment_step (ε s : ℝ) (hε : 0 < ε) (hs : 0 ≤ s) (hsε : s ≤ ε/10000) :
    ∀ l : ℝ, 0 ≤ l → l < 6/7 →
      (∫ t in (0:ℝ)..(7/3), Real.exp ((6/7:ℝ)*t) * Work.ZeroFreeTables.tf72f (6/7) t)
        - (∫ t in (0:ℝ)..(7/3), Real.exp (l*t) * Work.ZeroFreeTables.tf72f (6/7) t)
      ≤ 2 * ((∫ t in (0:ℝ)..(7/3), Work.ZeroFreeTables.tf72f (6/7) t)
        - (∫ t in (0:ℝ)..(7/3), Real.exp (-((6/7-l)*t)) * Work.ZeroFreeTables.tf72f (6/7) t))
        + s →
      l ≤ 792/1000 ∨ 6/7 - ε/2 ≤ l := by
  intro l hl0 hl7 hhyp
  by_cases h1 : l ≤ 792/1000
  · exact Or.inl h1
  · right
    push_neg at h1
    by_contra h2
    push_neg at h2
    have hKle' : 2 * (∫ t in (0:ℝ)..(7/3), Real.exp (-(((6/7:ℝ) - l) * t)) * tf72f (6/7) t)
        - (∫ t in (0:ℝ)..(7/3), Real.exp (l*t) * tf72f (6/7) t)
        + (∫ t in (0:ℝ)..(7/3), Real.exp ((6/7:ℝ)*t) * tf72f (6/7) t)
        - 2 * (∫ t in (0:ℝ)..(7/3), tf72f (6/7) t) ≤ s := by
      linarith [hhyp]
    have hKle : Kfun ((6/7:ℝ) - l) ≤ s := by
      rw [← K_identity l]; exact hKle'
    have hu_pos : 0 < (6/7:ℝ) - l := by linarith
    have hu_le : (6/7:ℝ) - l ≤ 57/875 := by linarith
    have hlb := Kfun_lower ((6/7:ℝ) - l) hu_pos.le hu_le
    have hu_eps : ε/2 < (6/7:ℝ) - l := by linarith
    linarith [hlb, hKle, hsε, hu_eps]

end Work.ZeroFreeTables.OffAxis
