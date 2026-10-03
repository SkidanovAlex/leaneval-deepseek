/-
  Companion paper ("Asymptotic sieve for primes"), §3: the *smoothed* form of (3.4).

  The paper applies the operator `I_h(Y,Z) = ∫_Y^{eY} ∫_Z^{eZ} h(y,z)(yz)^{-1} dy dz` to the
  pointwise identity (3.4).  Here we use the cheaper *y-only* smoothing, which suffices: the
  estimates that are intrinsically integrated (the `τ⁵`-weighted (R′) bounds for `S₂` and `S₃`)
  are integrated over `y` only, so it is enough to average the pointwise identity (3.4) over
  `y ∈ [Y, eY]` with weight `dy/y`, using `∫_Y^{eY} dy/y = 1`.

  Main results:
  * `S_eq_y_smoothed` — the `y`-smoothed (3.4);
  * `abs_S_bound_y_smoothed` — the companion's Theorem 1 in `y`-smoothed form: the pointwise
    estimates for `T`, `T(x;y,z)` and `S₁` together with the `y`-integrated estimates for `S₂`
    and `S₃` bound the truncated prime sum.
-/
import Mathlib
import Submission.ASP.Defs
import Submission.ASP.S3w
import Submission.ASP.S7c
import Submission.Commons.Analysis.Asymptotics.integral_one_div_Ioc_exp_mul

namespace Submission.ASP

open Finset MeasureTheory
open scoped Interval

noncomputable section

/-- `∫_Y^{eY} dy/y = 1`. -/
lemma integral_one_div_exp_mul (Y : ℝ) (hY : 0 < Y) :
    (∫ y in Y..Real.exp 1 * Y, 1 / y) = 1 :=
  Commons.Analysis.Asymptotics.integral_one_div_Ioc_exp_mul Y hY

/-- **The `y`-smoothed (3.4)**: for fixed truncation point `z > 0`, averaging the pointwise
identity `S_eq'` over `y ∈ [Y, eY]` against `dy/y` reproduces the pointwise left-hand side,
because `∫_Y^{eY} dy/y = 1`. -/
theorem S_eq_y_smoothed (a lam : ℕ → ℝ) (N : ℕ) (hN : 1 ≤ N) {Y s z : ℝ}
    (hY : 0 < Y) (hs : 1 ≤ s) (hz : 0 < z) :
    (∑ n ∈ Finset.Icc 1 N, a n * rhoOf lam n *
        (if z < (n : ℝ) then ArithmeticFunction.vonMangoldt n else 0))
      = ∫ y in Y..Real.exp 1 * Y,
          (Tsum a lam (N : ℝ) y - Tsum2 a lam (N : ℝ) y z
            + S2 a lam N y z (s * y) + S3 a lam N z (s * y) (s * z)
            + S1 a lam N (s * y) (s * z)) / y := by
  set L : ℝ := ∑ n ∈ Finset.Icc 1 N, a n * rhoOf lam n *
    (if z < (n : ℝ) then ArithmeticFunction.vonMangoldt n else 0) with hL
  have hconst : (∫ y in Y..Real.exp 1 * Y, L / y) = L := by
    rw [show (fun y : ℝ => L / y) = fun y => L * (1 / y) by funext y; ring]
    rw [intervalIntegral.integral_const_mul, integral_one_div_exp_mul Y hY, mul_one]
  rw [← hconst]
  refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (fun y hy => ?_))
  have hYpos : 0 < Real.exp 1 * Y := mul_pos (Real.exp_pos 1) hY
  have hy0 : 0 < y := by
    rcases Set.mem_uIoc.mp hy with h | h
    · linarith [h.1]
    · linarith [h.1]
  have hys : y ≤ s * y := by
    have := mul_le_mul_of_nonneg_right hs (le_of_lt hy0)
    simpa using this
  have hzs : z ≤ s * z := by
    have := mul_le_mul_of_nonneg_right hs (le_of_lt hz)
    simpa using this
  have hpt : L = Tsum a lam (N : ℝ) y - Tsum2 a lam (N : ℝ) y z
      + S2 a lam N y z (s * y) + S3 a lam N z (s * y) (s * z)
      + S1 a lam N (s * y) (s * z) := by
    rw [hL]
    rw [S_eq' a lam N hN hys hzs]
  rw [hpt]

/-! ### Measurability of step functions in `y` -/

lemma measurable_ite_le (c K : ℝ) : Measurable (fun y : ℝ => if c ≤ y then K else 0) := by
  have h : (fun y : ℝ => if c ≤ y then K else 0)
      = (Set.Ici c).indicator (fun _ => K) := by
    funext y
    rw [Set.indicator_apply]
    by_cases hy : c ≤ y <;> simp [hy]
  rw [h]; exact measurable_const.indicator measurableSet_Ici

lemma measurable_ite_lt (c K : ℝ) : Measurable (fun y : ℝ => if y < c then K else 0) := by
  have h : (fun y : ℝ => if y < c then K else 0)
      = (Set.Iio c).indicator (fun _ => K) := by
    funext y
    rw [Set.indicator_apply]
    by_cases hy : y < c <;> simp [hy]
  rw [h]; exact measurable_const.indicator measurableSet_Iio

lemma measurable_ite_mul_lt {s c K : ℝ} (hs : 0 < s) :
    Measurable (fun y : ℝ => if s * y < c then K else 0) := by
  have h : (fun y : ℝ => if s * y < c then K else 0)
      = (Set.Iio (c / s)).indicator (fun _ => K) := by
    funext y
    rw [Set.indicator_apply]
    by_cases hy : s * y < c
    · rw [if_pos hy, if_pos (Set.mem_Iio.mpr ?_)]
      rw [lt_div_iff₀ hs]; rwa [mul_comm]
    · rw [if_neg hy, if_neg (fun hc => hy ?_)]
      rw [Set.mem_Iio] at hc
      have h2 := (lt_div_iff₀ hs).mp hc
      rw [mul_comm] at h2
      exact h2
  rw [h]; exact measurable_const.indicator measurableSet_Iio

lemma measurable_ite_lt_and_le {s b K : ℝ} (hs : 0 < s) :
    Measurable (fun y : ℝ => if y < b ∧ b ≤ s * y then K else 0) := by
  have h : (fun y : ℝ => if y < b ∧ b ≤ s * y then K else 0)
      = (Set.Ico (b / s) b).indicator (fun _ => K) := by
    funext y
    rw [Set.indicator_apply]
    by_cases hy : y < b ∧ b ≤ s * y
    · rw [if_pos hy, if_pos (Set.mem_Ico.mpr ⟨?_, hy.1⟩)]
      rw [div_le_iff₀ hs]
      rw [mul_comm]
      exact hy.2
    · rw [if_neg hy, if_neg (fun hc => hy ⟨hc.2, ?_⟩)]
      rw [Set.mem_Ico] at hc
      have h2 := (div_le_iff₀ hs).mp hc.1
      rw [mul_comm] at h2
      exact h2
  rw [h]; exact measurable_const.indicator measurableSet_Ico

/-! ### Bounds on the five pieces -/

lemma abs_moebius_cast_le_one' (n : ℕ) : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
  have h := ArithmeticFunction.abs_moebius_le_one (n := n)
  exact_mod_cast h

lemma measurable_logWeight (n : ℕ) : Measurable (fun y : ℝ => logWeight n y) := by
  have h : (fun y : ℝ => logWeight n y) = fun y => ∑ b ∈ n.divisors,
      (if ((b : ℕ) : ℝ) ≤ y
        then (ArithmeticFunction.moebius b : ℝ) * (Real.log (n : ℝ) - Real.log (b : ℝ))
        else 0) := by
    funext y; rw [logWeight, Finset.sum_filter]
  rw [h]
  exact Finset.measurable_sum _ (fun b _ => measurable_ite_le _ _)

lemma abs_logWeight_le (n : ℕ) (y : ℝ) :
    |logWeight n y| ≤ ∑ b ∈ n.divisors, (|Real.log (n : ℝ)| + |Real.log (b : ℝ)|) := by
  rw [logWeight]
  calc |∑ b ∈ n.divisors.filter (fun b => ((b : ℕ) : ℝ) ≤ y),
        (ArithmeticFunction.moebius b : ℝ) * (Real.log (n : ℝ) - Real.log (b : ℝ))|
      ≤ ∑ b ∈ n.divisors.filter (fun b => ((b : ℕ) : ℝ) ≤ y),
          |(ArithmeticFunction.moebius b : ℝ) * (Real.log (n : ℝ) - Real.log (b : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b ∈ n.divisors.filter (fun b => ((b : ℕ) : ℝ) ≤ y),
          (|Real.log (n : ℝ)| + |Real.log (b : ℝ)|) := by
        refine Finset.sum_le_sum (fun b _ => ?_)
        rw [abs_mul]
        refine (mul_le_mul_of_nonneg_right (abs_moebius_cast_le_one' b) (abs_nonneg _)).trans ?_
        rw [one_mul]
        exact abs_sub_le_iff.mpr
          ⟨by linarith [le_abs_self (Real.log (n : ℝ)), neg_le_abs (Real.log (b : ℝ))],
           by linarith [le_abs_self (Real.log (b : ℝ)), neg_le_abs (Real.log (n : ℝ))]⟩
    _ ≤ ∑ b ∈ n.divisors, (|Real.log (n : ℝ)| + |Real.log (b : ℝ)|) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun b _ _ => by positivity)

/-- A sum over a subset is bounded by the sum of absolute values over the whole set. -/
lemma abs_sum_le_sum_of_subset {s t : Finset ℕ} (h : s ⊆ t) (f : ℕ → ℝ) :
    |∑ i ∈ s, f i| ≤ ∑ i ∈ t, |f i| :=
  (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum_of_subset_of_nonneg h (fun i _ _ => abs_nonneg (f i)))

lemma measurable_Tsum (a lam : ℕ → ℝ) (N : ℕ) :
    Measurable (fun y : ℝ => Tsum a lam (N : ℝ) y) := by
  have h : (fun y : ℝ => Tsum a lam (N : ℝ) y) = fun y =>
      ∑ n ∈ Finset.Icc 1 N, a n * rhoOf lam n * ∑ b ∈ n.divisors,
        (if ((b : ℕ) : ℝ) ≤ y
          then (ArithmeticFunction.moebius b : ℝ) * (Real.log (n : ℝ) - Real.log (b : ℝ))
          else 0) := by
    funext y; simp only [Tsum, Nat.floor_natCast, logWeight, Finset.sum_filter]
  rw [h]
  refine Finset.measurable_sum _ (fun n _ => ?_)
  exact (Finset.measurable_sum _ (fun b _ =>
    measurable_ite_le ((b : ℕ) : ℝ)
      ((ArithmeticFunction.moebius b : ℝ) * (Real.log (n : ℝ) - Real.log (b : ℝ))))).const_mul _

lemma abs_Tsum_le (a lam : ℕ → ℝ) (N : ℕ) (y : ℝ) :
    |Tsum a lam (N : ℝ) y| ≤ ∑ n ∈ Finset.Icc 1 N,
      |a n| * (∑ ν ∈ n.divisors, |lam ν|)
        * (∑ b ∈ n.divisors, (|Real.log (n : ℝ)| + |Real.log (b : ℝ)|)) := by
  rw [Tsum, Nat.floor_natCast]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun n _ => ?_))
  rw [abs_mul, abs_mul]
  refine mul_le_mul (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)) (abs_logWeight_le n y)
    (abs_nonneg _) (by positivity)
  rw [rhoOf]
  exact Finset.abs_sum_le_sum_abs _ _

/-- A global bound on `|Vb a lam d N|`. -/
lemma abs_Vb_le (a lam : ℕ → ℝ) (d N : ℕ) :
    |Vb a lam d (N : ℝ)| ≤ ∑ n ∈ Finset.Icc 1 N, |a n| * (∑ ν ∈ n.divisors, |lam ν|) := by
  rw [Vb, Nat.floor_natCast]
  refine (abs_sum_le_sum_of_subset (Finset.filter_subset _ _) _).trans ?_
  refine Finset.sum_le_sum (fun n _ => ?_)
  rw [abs_mul, rhoOf]
  exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)

/-- A global bound on `|Tsum2|`. -/
lemma abs_Tsum2_le (a lam : ℕ → ℝ) (N : ℕ) (y z : ℝ) :
    |Tsum2 a lam (N : ℝ) y z| ≤ ∑ b ∈ Finset.Icc 1 N,
      ∑ c ∈ Finset.Icc 1 N,
        |ArithmeticFunction.vonMangoldt c| *
          (∑ n ∈ Finset.Icc 1 N, |a n| * (∑ ν ∈ n.divisors, |lam ν|)) := by
  set K : ℝ := ∑ n ∈ Finset.Icc 1 N, |a n| * (∑ ν ∈ n.divisors, |lam ν|) with hK
  rw [Tsum2, Nat.floor_natCast]
  refine (abs_sum_le_sum_of_subset (Finset.filter_subset _ _) _).trans ?_
  refine Finset.sum_le_sum (fun b _ => ?_)
  have hinner : |∑ c ∈ (Finset.Icc 1 N).filter (fun c => ((c : ℕ) : ℝ) ≤ z),
        ArithmeticFunction.vonMangoldt c * Vb a lam (b * c) (N : ℝ)|
      ≤ ∑ c ∈ Finset.Icc 1 N, |ArithmeticFunction.vonMangoldt c| * K := by
    refine (abs_sum_le_sum_of_subset (Finset.filter_subset _ _)
      (fun c => ArithmeticFunction.vonMangoldt c * Vb a lam (b * c) (N : ℝ))).trans ?_
    refine Finset.sum_le_sum (fun c _ => ?_)
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [hK]
    exact abs_Vb_le a lam (b * c) N
  rw [abs_mul]
  refine (mul_le_mul (abs_moebius_cast_le_one' b) hinner (abs_nonneg _) (by norm_num)).trans ?_
  rw [one_mul]

/-- The common shape of the bounds for `S₁`, `S₂`, `S₃`. -/
lemma abs_S1_bd (a lam : ℕ → ℝ) (N : ℕ) (sy sz : ℝ) :
    |S1 a lam N sy sz| ≤ ∑ n ∈ Finset.Icc 1 N,
      |a n| * (∑ ν ∈ n.divisors, |lam ν|)
        * (∑ b ∈ n.divisors,
            (∑ c ∈ (n / b).divisors, |ArithmeticFunction.vonMangoldt c|)) := by
  have hrho : ∀ n : ℕ, |rhoOf lam n| ≤ ∑ ν ∈ n.divisors, |lam ν| := by
    intro n; rw [rhoOf]; exact Finset.abs_sum_le_sum_abs _ _
  have hLam : ∀ n : ℕ, |Lam1 n sy sz| ≤ ∑ b ∈ n.divisors,
      (∑ c ∈ (n / b).divisors, |ArithmeticFunction.vonMangoldt c|) := by
    intro n
    rw [Lam1]
    refine (abs_sum_le_sum_of_subset (Finset.filter_subset _ _) _).trans ?_
    refine Finset.sum_le_sum (fun b _ => ?_)
    rw [abs_mul]
    calc |(ArithmeticFunction.moebius b : ℝ)| *
          |∑ c ∈ (n / b).divisors.filter (fun c => sz < ((c : ℕ) : ℝ)),
              ArithmeticFunction.vonMangoldt c|
        ≤ 1 * (∑ c ∈ (n / b).divisors, |ArithmeticFunction.vonMangoldt c|) :=
          mul_le_mul (abs_moebius_cast_le_one' b)
            (abs_sum_le_sum_of_subset (Finset.filter_subset _ _) _) (abs_nonneg _) (by norm_num)
      _ = ∑ c ∈ (n / b).divisors, |ArithmeticFunction.vonMangoldt c| := by rw [one_mul]
  rw [S1]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun n _ => ?_))
  rw [abs_mul]
  refine mul_le_mul ?_ (hLam n) (abs_nonneg _) (by positivity)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hrho n) (abs_nonneg _)

lemma abs_S2_bd (a lam : ℕ → ℝ) (N : ℕ) (y z sy : ℝ) :
    |S2 a lam N y z sy| ≤ ∑ n ∈ Finset.Icc 1 N,
      |a n| * (∑ ν ∈ n.divisors, |lam ν|)
        * (∑ b ∈ n.divisors,
            (∑ c ∈ (n / b).divisors, |ArithmeticFunction.vonMangoldt c|)) := by
  have hrho : ∀ n : ℕ, |rhoOf lam n| ≤ ∑ ν ∈ n.divisors, |lam ν| := by
    intro n; rw [rhoOf]; exact Finset.abs_sum_le_sum_abs _ _
  have hLam : ∀ n : ℕ, |Lam2 n y z sy| ≤ ∑ b ∈ n.divisors,
      (∑ c ∈ (n / b).divisors, |ArithmeticFunction.vonMangoldt c|) := by
    intro n
    rw [Lam2]
    refine (abs_sum_le_sum_of_subset (Finset.filter_subset _ _) _).trans ?_
    refine Finset.sum_le_sum (fun b _ => ?_)
    rw [abs_mul]
    calc |(ArithmeticFunction.moebius b : ℝ)| *
          |∑ c ∈ (n / b).divisors.filter (fun c => z < ((c : ℕ) : ℝ)),
              ArithmeticFunction.vonMangoldt c|
        ≤ 1 * (∑ c ∈ (n / b).divisors, |ArithmeticFunction.vonMangoldt c|) :=
          mul_le_mul (abs_moebius_cast_le_one' b)
            (abs_sum_le_sum_of_subset (Finset.filter_subset _ _) _) (abs_nonneg _) (by norm_num)
      _ = ∑ c ∈ (n / b).divisors, |ArithmeticFunction.vonMangoldt c| := by rw [one_mul]
  rw [S2]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun n _ => ?_))
  rw [abs_mul]
  refine mul_le_mul ?_ (hLam n) (abs_nonneg _) (by positivity)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hrho n) (abs_nonneg _)

lemma abs_S3_bd (a lam : ℕ → ℝ) (N : ℕ) (z sy sz : ℝ) :
    |S3 a lam N z sy sz| ≤ ∑ n ∈ Finset.Icc 1 N,
      |a n| * (∑ ν ∈ n.divisors, |lam ν|)
        * (∑ b ∈ n.divisors,
            (∑ c ∈ (n / b).divisors, |ArithmeticFunction.vonMangoldt c|)) := by
  have hrho : ∀ n : ℕ, |rhoOf lam n| ≤ ∑ ν ∈ n.divisors, |lam ν| := by
    intro n; rw [rhoOf]; exact Finset.abs_sum_le_sum_abs _ _
  have hLam : ∀ n : ℕ, |Lam3 n z sy sz| ≤ ∑ b ∈ n.divisors,
      (∑ c ∈ (n / b).divisors, |ArithmeticFunction.vonMangoldt c|) := by
    intro n
    rw [Lam3]
    refine (abs_sum_le_sum_of_subset (Finset.filter_subset _ _) _).trans ?_
    refine Finset.sum_le_sum (fun b _ => ?_)
    rw [abs_mul]
    calc |(ArithmeticFunction.moebius b : ℝ)| *
          |∑ c ∈ (n / b).divisors.filter
              (fun c => z < ((c : ℕ) : ℝ) ∧ ((c : ℕ) : ℝ) ≤ sz),
              ArithmeticFunction.vonMangoldt c|
        ≤ 1 * (∑ c ∈ (n / b).divisors, |ArithmeticFunction.vonMangoldt c|) :=
          mul_le_mul (abs_moebius_cast_le_one' b)
            (abs_sum_le_sum_of_subset (Finset.filter_subset _ _) _) (abs_nonneg _) (by norm_num)
      _ = ∑ c ∈ (n / b).divisors, |ArithmeticFunction.vonMangoldt c| := by rw [one_mul]
  rw [S3]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun n _ => ?_))
  rw [abs_mul]
  refine mul_le_mul ?_ (hLam n) (abs_nonneg _) (by positivity)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hrho n) (abs_nonneg _)

/-! ### Measurability and integrability of the five pieces along `y` -/

/-- `Y ≤ e·Y` for `Y > 0`. -/
lemma le_exp_mul_self {Y : ℝ} (hY : 0 < Y) : Y ≤ Real.exp 1 * Y := by
  have h : (1 : ℝ) ≤ Real.exp 1 := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by norm_num)
  nlinarith

/-- Integrability of `f(y)/y` on `[Y, eY]` from measurability and a bound. -/
lemma intervalIntegrable_div_of_bound' {f : ℝ → ℝ} (hf : Measurable f) {Y : ℝ} (hY : 0 < Y)
    {C : ℝ} (hC : ∀ u ∈ Set.Icc Y (Real.exp 1 * Y), |f u| ≤ C) :
    IntervalIntegrable (fun y => f y / y) volume Y (Real.exp 1 * Y) :=
  intervalIntegrable_div_Ioc hf hY (le_exp_mul_self hY) C hC

lemma intervalIntegrable_Tsum_div (a lam : ℕ → ℝ) (N : ℕ) {Y : ℝ} (hY : 0 < Y) :
    IntervalIntegrable (fun y => Tsum a lam (N : ℝ) y / y) volume Y (Real.exp 1 * Y) :=
  intervalIntegrable_div_of_bound' (measurable_Tsum a lam N) hY
    (fun u _ => abs_Tsum_le a lam N u)

lemma measurable_Tsum2 (a lam : ℕ → ℝ) (N : ℕ) (z : ℝ) :
    Measurable (fun y : ℝ => Tsum2 a lam (N : ℝ) y z) := by
  have h : (fun y : ℝ => Tsum2 a lam (N : ℝ) y z) = fun y =>
      ∑ b ∈ Finset.Icc 1 N, (if ((b : ℕ) : ℝ) ≤ y
        then (ArithmeticFunction.moebius b : ℝ) *
          (∑ c ∈ (Finset.Icc 1 N).filter (fun c => ((c : ℕ) : ℝ) ≤ z),
            ArithmeticFunction.vonMangoldt c * Vb a lam (b * c) (N : ℝ)) else 0) := by
    funext y; simp only [Tsum2, Nat.floor_natCast, Finset.sum_filter]
  rw [h]
  exact Finset.measurable_sum _ (fun b _ => measurable_ite_le _ _)

lemma intervalIntegrable_Tsum2_div (a lam : ℕ → ℝ) (N : ℕ) (z : ℝ) {Y : ℝ} (hY : 0 < Y) :
    IntervalIntegrable (fun y => Tsum2 a lam (N : ℝ) y z / y) volume Y (Real.exp 1 * Y) :=
  intervalIntegrable_div_of_bound' (measurable_Tsum2 a lam N z) hY
    (fun u _ => abs_Tsum2_le a lam N u z)

lemma measurable_S1_y (a lam : ℕ → ℝ) (N : ℕ) {s z : ℝ} (hs : 0 < s) :
    Measurable (fun y : ℝ => S1 a lam N (s * y) (s * z)) := by
  have h : (fun y : ℝ => S1 a lam N (s * y) (s * z)) = fun y =>
      ∑ n ∈ Finset.Icc 1 N, a n * rhoOf lam n * ∑ b ∈ n.divisors,
        (if s * y < ((b : ℕ) : ℝ) then (ArithmeticFunction.moebius b : ℝ) *
          (∑ c ∈ (n / b).divisors.filter (fun c => s * z < ((c : ℕ) : ℝ)),
            ArithmeticFunction.vonMangoldt c) else 0) := by
    funext y; simp only [S1, Lam1, Finset.sum_filter]
  rw [h]
  refine Finset.measurable_sum _ (fun n _ => ?_)
  exact (Finset.measurable_sum _ (fun b _ => measurable_ite_mul_lt hs (c := ((b : ℕ) : ℝ))
    (K := (ArithmeticFunction.moebius b : ℝ) *
      (∑ c ∈ (n / b).divisors.filter (fun c => s * z < ((c : ℕ) : ℝ)),
        ArithmeticFunction.vonMangoldt c)))).const_mul _

lemma intervalIntegrable_S1_div (a lam : ℕ → ℝ) (N : ℕ) {s z Y : ℝ} (hs : 1 ≤ s) (hY : 0 < Y) :
    IntervalIntegrable (fun y => S1 a lam N (s * y) (s * z) / y) volume Y (Real.exp 1 * Y) :=
  intervalIntegrable_div_of_bound' (measurable_S1_y a lam N (lt_of_lt_of_le zero_lt_one hs)) hY
    (fun u _ => abs_S1_bd a lam N (s * u) (s * z))

lemma measurable_S2_y (a lam : ℕ → ℝ) (N : ℕ) {s z : ℝ} (hs : 0 < s) :
    Measurable (fun y : ℝ => S2 a lam N y z (s * y)) := by
  have h : (fun y : ℝ => S2 a lam N y z (s * y)) = fun y =>
      ∑ n ∈ Finset.Icc 1 N, a n * rhoOf lam n * ∑ b ∈ n.divisors,
        (if y < ((b : ℕ) : ℝ) ∧ ((b : ℕ) : ℝ) ≤ s * y
          then (ArithmeticFunction.moebius b : ℝ) *
            (∑ c ∈ (n / b).divisors.filter (fun c => z < ((c : ℕ) : ℝ)),
              ArithmeticFunction.vonMangoldt c) else 0) := by
    funext y; simp only [S2, Lam2, Finset.sum_filter]
  rw [h]
  refine Finset.measurable_sum _ (fun n _ => ?_)
  exact (Finset.measurable_sum _ (fun b _ => measurable_ite_lt_and_le hs
    (b := ((b : ℕ) : ℝ))
    (K := (ArithmeticFunction.moebius b : ℝ) *
      (∑ c ∈ (n / b).divisors.filter (fun c => z < ((c : ℕ) : ℝ)),
        ArithmeticFunction.vonMangoldt c)))).const_mul _

lemma intervalIntegrable_S2_div (a lam : ℕ → ℝ) (N : ℕ) {s z Y : ℝ} (hs : 1 ≤ s) (hY : 0 < Y) :
    IntervalIntegrable (fun y => S2 a lam N y z (s * y) / y) volume Y (Real.exp 1 * Y) :=
  intervalIntegrable_div_of_bound' (measurable_S2_y a lam N (lt_of_lt_of_le zero_lt_one hs)) hY
    (fun u _ => abs_S2_bd a lam N u z (s * u))

lemma measurable_S3_y (a lam : ℕ → ℝ) (N : ℕ) {s z : ℝ} (hs : 0 < s) :
    Measurable (fun y : ℝ => S3 a lam N z (s * y) (s * z)) := by
  have h : (fun y : ℝ => S3 a lam N z (s * y) (s * z)) = fun y =>
      ∑ n ∈ Finset.Icc 1 N, a n * rhoOf lam n * ∑ b ∈ n.divisors,
        (if s * y < ((b : ℕ) : ℝ) then (ArithmeticFunction.moebius b : ℝ) *
          (∑ c ∈ (n / b).divisors.filter
            (fun c => z < ((c : ℕ) : ℝ) ∧ ((c : ℕ) : ℝ) ≤ s * z),
            ArithmeticFunction.vonMangoldt c) else 0) := by
    funext y; simp only [S3, Lam3, Finset.sum_filter]
  rw [h]
  refine Finset.measurable_sum _ (fun n _ => ?_)
  exact (Finset.measurable_sum _ (fun b _ => measurable_ite_mul_lt hs (c := ((b : ℕ) : ℝ))
    (K := (ArithmeticFunction.moebius b : ℝ) *
      (∑ c ∈ (n / b).divisors.filter
        (fun c => z < ((c : ℕ) : ℝ) ∧ ((c : ℕ) : ℝ) ≤ s * z),
        ArithmeticFunction.vonMangoldt c)))).const_mul _

lemma intervalIntegrable_S3_div (a lam : ℕ → ℝ) (N : ℕ) {s z Y : ℝ} (hs : 1 ≤ s) (hY : 0 < Y) :
    IntervalIntegrable (fun y => S3 a lam N z (s * y) (s * z) / y) volume Y (Real.exp 1 * Y) :=
  intervalIntegrable_div_of_bound' (measurable_S3_y a lam N (lt_of_lt_of_le zero_lt_one hs)) hY
    (fun u _ => abs_S3_bd a lam N z (s * u) (s * z))

/-! ### The companion's Theorem 1 in `y`-smoothed form -/

/-- **The companion's Theorem 1, `y`-smoothed**: the pointwise estimates for `T`, `T(x;y,z)` and
`S₁` together with the `y`-integrated estimates for `S₂` and `S₃` bound the truncated prime sum
`∑_{n ≤ N} aₙρₙΛ(n>z)`. -/
theorem abs_S_bound_y_smoothed (a lam : ℕ → ℝ) (N : ℕ) (hN : 1 ≤ N)
    {Y s z H E1 E2 E3 E4 E5 : ℝ}
    (hY : 0 < Y) (hs : 1 ≤ s) (hz : 0 < z)
    (hT : ∀ y ∈ Set.Icc Y (Real.exp 1 * Y),
      |Tsum a lam (N : ℝ) y - H * Acount a (N : ℝ)| ≤ E1)
    (hT2 : ∀ y ∈ Set.Icc Y (Real.exp 1 * Y), |Tsum2 a lam (N : ℝ) y z| ≤ E2)
    (hS1 : ∀ y ∈ Set.Icc Y (Real.exp 1 * Y), |S1 a lam N (s * y) (s * z)| ≤ E3)
    (hS2 : (∫ y in Y..Real.exp 1 * Y, |S2 a lam N y z (s * y)| / y) ≤ E4)
    (hS3 : (∫ y in Y..Real.exp 1 * Y, |S3 a lam N z (s * y) (s * z)| / y) ≤ E5)
    (hE : 0 ≤ E1 + E2 + E3) (hE4 : 0 ≤ E4) (hE5 : 0 ≤ E5) :
    |(∑ n ∈ Finset.Icc 1 N, a n * rhoOf lam n *
        (if z < (n : ℝ) then ArithmeticFunction.vonMangoldt n else 0))
      - H * Acount a (N : ℝ)| ≤ E1 + E2 + E3 + E4 + E5 := by
  have hL : (∑ n ∈ Finset.Icc 1 N, a n * rhoOf lam n *
      (if z < (n : ℝ) then ArithmeticFunction.vonMangoldt n else 0))
      = ∫ y in Y..Real.exp 1 * Y,
          (Tsum a lam (N : ℝ) y - Tsum2 a lam (N : ℝ) y z
            + S2 a lam N y z (s * y) + S3 a lam N z (s * y) (s * z)
            + S1 a lam N (s * y) (s * z)) / y :=
    S_eq_y_smoothed a lam N hN hY hs hz
  have hHA : H * Acount a (N : ℝ)
      = ∫ y in Y..Real.exp 1 * Y, (H * Acount a (N : ℝ)) / y := by
    have hfun : (fun y : ℝ => H * Acount a (N : ℝ) / y)
        = fun y => (H * Acount a (N : ℝ)) * (1 / y) := by funext y; ring
    rw [hfun, intervalIntegral.integral_const_mul, integral_one_div_exp_mul Y hY, mul_one]
  have hYa : Y ≤ Real.exp 1 * Y := le_exp_mul_self hY
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hT' := intervalIntegrable_Tsum_div a lam N hY
  have hT2' := intervalIntegrable_Tsum2_div a lam N z hY
  have hS2' := intervalIntegrable_S2_div (z := z) a lam N hs hY
  have hS3' := intervalIntegrable_S3_div (z := z) a lam N hs hY
  have hS1' := intervalIntegrable_S1_div (z := z) a lam N hs hY
  have hint1 : IntervalIntegrable
      (fun y : ℝ => (Tsum a lam (N : ℝ) y - Tsum2 a lam (N : ℝ) y z
            + S2 a lam N y z (s * y) + S3 a lam N z (s * y) (s * z)
            + S1 a lam N (s * y) (s * z)) / y) volume Y (Real.exp 1 * Y) := by
    have h12 : IntervalIntegrable
        (fun y : ℝ => Tsum a lam (N : ℝ) y / y - Tsum2 a lam (N : ℝ) y z / y)
        volume Y (Real.exp 1 * Y) := IntervalIntegrable.sub hT' hT2'
    have h123 : IntervalIntegrable
        (fun y : ℝ => Tsum a lam (N : ℝ) y / y - Tsum2 a lam (N : ℝ) y z / y
          + S2 a lam N y z (s * y) / y) volume Y (Real.exp 1 * Y) :=
      IntervalIntegrable.add h12 hS2'
    have h1234 : IntervalIntegrable
        (fun y : ℝ => Tsum a lam (N : ℝ) y / y - Tsum2 a lam (N : ℝ) y z / y
          + S2 a lam N y z (s * y) / y + S3 a lam N z (s * y) (s * z) / y)
        volume Y (Real.exp 1 * Y) := IntervalIntegrable.add h123 hS3'
    have h12345 : IntervalIntegrable
        (fun y : ℝ => Tsum a lam (N : ℝ) y / y - Tsum2 a lam (N : ℝ) y z / y
          + S2 a lam N y z (s * y) / y + S3 a lam N z (s * y) (s * z) / y
          + S1 a lam N (s * y) (s * z) / y) volume Y (Real.exp 1 * Y) :=
      IntervalIntegrable.add h1234 hS1'
    refine h12345.congr ?_
    intro x _
    ring
  have hint2 : IntervalIntegrable (fun y : ℝ => (H * Acount a (N : ℝ)) / y)
      volume Y (Real.exp 1 * Y) :=
    intervalIntegrable_div_of_bound' (C := |H * Acount a (N : ℝ)|)
      (f := fun _ : ℝ => H * Acount a (N : ℝ)) measurable_const hY (fun u _ => le_rfl)
  have iA : IntervalIntegrable (fun y : ℝ => (E1 + E2 + E3) / y) volume Y (Real.exp 1 * Y) :=
    intervalIntegrable_div_of_bound' (C := |E1 + E2 + E3|)
      (f := fun _ : ℝ => E1 + E2 + E3) measurable_const hY (fun u _ => le_rfl)
  have iB : IntervalIntegrable (fun y : ℝ => |S2 a lam N y z (s * y)| / y)
      volume Y (Real.exp 1 * Y) :=
    intervalIntegrable_div_of_bound' ((measurable_S2_y a lam N hs0).abs) hY
      (fun u _ => by simpa using abs_S2_bd a lam N u z (s * u))
  have iC : IntervalIntegrable (fun y : ℝ => |S3 a lam N z (s * y) (s * z)| / y)
      volume Y (Real.exp 1 * Y) :=
    intervalIntegrable_div_of_bound' ((measurable_S3_y a lam N hs0).abs) hY
      (fun u _ => by simpa using abs_S3_bd a lam N z (s * u) (s * z))
  have hmaj : IntervalIntegrable
      (fun y : ℝ => (E1 + E2 + E3) / y + |S2 a lam N y z (s * y)| / y
        + |S3 a lam N z (s * y) (s * z)| / y) volume Y (Real.exp 1 * Y) := by
    exact IntervalIntegrable.add (IntervalIntegrable.add iA iB) iC
  rw [hL, hHA, ← intervalIntegral.integral_sub hint1 hint2]
  refine le_trans (intervalIntegral.abs_integral_le_integral_abs hYa) ?_
  refine le_trans (intervalIntegral.integral_mono_ae_restrict hYa
    (IntervalIntegrable.sub hint1 hint2).abs hmaj ?_) ?_
  · change ∀ᵐ x ∂(volume.restrict (Set.Icc Y (Real.exp 1 * Y))),
      |((Tsum a lam (N : ℝ) x - Tsum2 a lam (N : ℝ) x z
            + S2 a lam N x z (s * x) + S3 a lam N z (s * x) (s * z)
            + S1 a lam N (s * x) (s * z)) / x - (H * Acount a (N : ℝ)) / x)|
        ≤ (E1 + E2 + E3) / x + |S2 a lam N x z (s * x)| / x
          + |S3 a lam N z (s * x) (s * z)| / x
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    refine Filter.Eventually.of_forall (fun y hy => ?_)
    have hy0 : 0 < y := lt_of_lt_of_le hY hy.1
    have hT1 : |Tsum a lam (N : ℝ) y - H * Acount a (N : ℝ)| ≤ E1 := hT y hy
    have hT22 : |Tsum2 a lam (N : ℝ) y z| ≤ E2 := hT2 y hy
    have hS11 : |S1 a lam N (s * y) (s * z)| ≤ E3 := hS1 y hy
    rw [← sub_div, abs_div, abs_of_pos hy0, ← add_div, ← add_div]
    refine div_le_div_of_nonneg_right ?_ hy0.le
    have h1 : |(Tsum a lam (N : ℝ) y - H * Acount a (N : ℝ)) - Tsum2 a lam (N : ℝ) y z
          + S2 a lam N y z (s * y) + S3 a lam N z (s * y) (s * z)
          + S1 a lam N (s * y) (s * z)|
        ≤ |(Tsum a lam (N : ℝ) y - H * Acount a (N : ℝ)) - Tsum2 a lam (N : ℝ) y z
            + S2 a lam N y z (s * y) + S3 a lam N z (s * y) (s * z)|
          + |S1 a lam N (s * y) (s * z)| := abs_add_le _ _
    have h2 : |(Tsum a lam (N : ℝ) y - H * Acount a (N : ℝ)) - Tsum2 a lam (N : ℝ) y z
          + S2 a lam N y z (s * y) + S3 a lam N z (s * y) (s * z)|
        ≤ |(Tsum a lam (N : ℝ) y - H * Acount a (N : ℝ)) - Tsum2 a lam (N : ℝ) y z
            + S2 a lam N y z (s * y)|
          + |S3 a lam N z (s * y) (s * z)| := abs_add_le _ _
    have h3 : |(Tsum a lam (N : ℝ) y - H * Acount a (N : ℝ)) - Tsum2 a lam (N : ℝ) y z
          + S2 a lam N y z (s * y)|
        ≤ |(Tsum a lam (N : ℝ) y - H * Acount a (N : ℝ)) - Tsum2 a lam (N : ℝ) y z|
          + |S2 a lam N y z (s * y)| := abs_add_le _ _
    have h4 : |(Tsum a lam (N : ℝ) y - H * Acount a (N : ℝ)) - Tsum2 a lam (N : ℝ) y z|
        ≤ |Tsum a lam (N : ℝ) y - H * Acount a (N : ℝ)| + |Tsum2 a lam (N : ℝ) y z| := by
      have := abs_add_le (Tsum a lam (N : ℝ) y - H * Acount a (N : ℝ))
        (-(Tsum2 a lam (N : ℝ) y z))
      rwa [abs_neg, sub_eq_add_neg] at this
    have heq : (Tsum a lam (N : ℝ) y - Tsum2 a lam (N : ℝ) y z + S2 a lam N y z (s * y)
          + S3 a lam N z (s * y) (s * z) + S1 a lam N (s * y) (s * z)
          - H * Acount a (N : ℝ))
        = ((Tsum a lam (N : ℝ) y - H * Acount a (N : ℝ)) - Tsum2 a lam (N : ℝ) y z
          + S2 a lam N y z (s * y) + S3 a lam N z (s * y) (s * z)
          + S1 a lam N (s * y) (s * z)) := by ring
    rw [heq]
    linarith [h1, h2, h3, h4, hT1, hT22, hS11]
  · rw [intervalIntegral.integral_add (IntervalIntegrable.add iA iB) iC,
      intervalIntegral.integral_add iA iB]
    have hvalA : (∫ y in Y..Real.exp 1 * Y, (E1 + E2 + E3) / y) = E1 + E2 + E3 := by
      have hfun : (fun y : ℝ => (E1 + E2 + E3) / y)
          = fun y => (E1 + E2 + E3) * (1 / y) := by funext y; ring
      rw [hfun, intervalIntegral.integral_const_mul, integral_one_div_exp_mul Y hY, mul_one]
    rw [hvalA]
    linarith [hS2, hS3]

end

end Submission.ASP
