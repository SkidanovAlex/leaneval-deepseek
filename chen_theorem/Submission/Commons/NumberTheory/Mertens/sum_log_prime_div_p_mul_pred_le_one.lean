import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.PrimeCounting

namespace Commons.NumberTheory.Mertens

open scoped BigOperators
open Finset MeasureTheory intervalIntegral

private lemma log_div_pred_nonneg {p : ℕ} (hp : p.Prime) :
    0 ≤ Real.log (p:ℝ)/((p:ℝ)*((p:ℝ)-1)) := by
  have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.two_le
  apply div_nonneg
  · exact Real.log_nonneg (by linarith)
  · exact mul_nonneg (by linarith) (by linarith)

private lemma log_le_pred_div_sqrt {p : ℕ} (hp : p.Prime) :
    Real.log (p:ℝ) ≤ ((p:ℝ)-1)/Real.sqrt (p:ℝ) := by
  have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.two_le
  have hp0 : 0 < (p:ℝ) := by linarith
  have hspos : 0 < Real.sqrt (p:ℝ) := Real.sqrt_pos.mpr hp0
  have hsq : Real.sqrt (p:ℝ) * Real.sqrt (p:ℝ) = (p:ℝ) := Real.mul_self_sqrt hp0.le
  have hlog_p : Real.log (p:ℝ) = 2 * Real.log (Real.sqrt (p:ℝ)) := by
    have hpp : (p:ℝ) = (Real.sqrt (p:ℝ))^2 := (Real.sq_sqrt hp0.le).symm
    rw [hpp, Real.log_pow]
    norm_num
  have hge1 : (1:ℝ) ≤ Real.sqrt (p:ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by linarith)
  have hlog_nonneg : 0 ≤ Real.log (Real.sqrt (p:ℝ)) := Real.log_nonneg hge1
  have hsinh : Real.log (Real.sqrt (p:ℝ)) ≤ (Real.sqrt (p:ℝ) - (Real.sqrt (p:ℝ))⁻¹)/2 := by
    have := Real.self_le_sinh_iff.mpr hlog_nonneg
    rwa [Real.sinh_log hspos] at this
  have hval : Real.sqrt (p:ℝ) - (Real.sqrt (p:ℝ))⁻¹ = ((p:ℝ)-1)/Real.sqrt (p:ℝ) := by
    field_simp
    nlinarith [hsq]
  calc Real.log (p:ℝ) = 2 * Real.log (Real.sqrt (p:ℝ)) := hlog_p
    _ ≤ Real.sqrt (p:ℝ) - (Real.sqrt (p:ℝ))⁻¹ := by linarith
    _ = ((p:ℝ)-1)/Real.sqrt (p:ℝ) := hval

private lemma term_le_inv_mul_sqrt {p : ℕ} (hp : p.Prime) :
    Real.log (p:ℝ)/((p:ℝ)*((p:ℝ)-1)) ≤ 1/((p:ℝ)*Real.sqrt (p:ℝ)) := by
  have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.two_le
  have hp0 : 0 < (p:ℝ) := by linarith
  have hpm1 : 0 < (p:ℝ)-1 := by linarith
  have hspos : 0 < Real.sqrt (p:ℝ) := Real.sqrt_pos.mpr hp0
  have h := log_le_pred_div_sqrt hp
  rw [div_le_div_iff₀ (mul_pos hp0 hpm1) (mul_pos hp0 hspos)]
  calc Real.log (p:ℝ) * ((p:ℝ)*Real.sqrt (p:ℝ))
      ≤ (((p:ℝ)-1)/Real.sqrt (p:ℝ)) * ((p:ℝ)*Real.sqrt (p:ℝ)) :=
        mul_le_mul_of_nonneg_right h (by positivity)
    _ = 1 * ((p:ℝ)*((p:ℝ)-1)) := by
        field_simp

private noncomputable def sqrtLo : ℕ → ℝ
  | 2 => 1.4142
  | 3 => 1.732
  | 5 => 2.236
  | 7 => 2.6457
  | 11 => 3.3166
  | 13 => 3.6055
  | 17 => 4.1231
  | 19 => 4.3588
  | 23 => 4.7958
  | 29 => 5.3851
  | 31 => 5.5677
  | _ => 1

private lemma sqrtLo_pos (p : ℕ) : 0 < sqrtLo p := by
  unfold sqrtLo
  split <;> norm_num

private lemma le_sqrt_of_sq_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x^2 ≤ y) :
    x ≤ Real.sqrt y :=
  (Real.le_sqrt hx hy).mpr h

private lemma sqrtLo_le {p : ℕ} (hp : p.Prime) (hle : p ≤ 31) :
    sqrtLo p ≤ Real.sqrt (p:ℝ) := by
  have hp2 : 2 ≤ p := hp.two_le
  interval_cases p <;>
    first
      | exact absurd hp (by decide)
      | (simp only [sqrtLo]; exact le_sqrt_of_sq_le (by norm_num) (by norm_num) (by norm_num))

private lemma inv_sqrt_le_bound {p : ℕ} (hp : p.Prime) (hle : p ≤ 31) :
    1/((p:ℝ)*Real.sqrt (p:ℝ)) ≤ 1/((p:ℝ)*sqrtLo p) := by
  have h := sqrtLo_le hp hle
  have hp0 : 0 < (p:ℝ) := by exact_mod_cast hp.pos
  exact one_div_le_one_div_of_le (mul_pos hp0 (sqrtLo_pos p))
      (mul_le_mul_of_nonneg_left h hp0.le)

private lemma prefix_le :
    (∑ p ∈ (31:ℕ).primesLE, Real.log (p:ℝ)/((p:ℝ)*((p:ℝ)-1))) ≤ 4/5 := by
  calc (∑ p ∈ (31:ℕ).primesLE, Real.log (p:ℝ)/((p:ℝ)*((p:ℝ)-1)))
      ≤ ∑ p ∈ (31:ℕ).primesLE, 1/((p:ℝ)*Real.sqrt (p:ℝ)) :=
        Finset.sum_le_sum (fun p hp => term_le_inv_mul_sqrt (Nat.mem_primesLE.mp hp).2)
    _ ≤ ∑ p ∈ (31:ℕ).primesLE, 1/((p:ℝ)*sqrtLo p) :=
        Finset.sum_le_sum (fun p hp =>
          inv_sqrt_le_bound (Nat.mem_primesLE.mp hp).2 (Nat.mem_primesLE.mp hp).1)
    _ ≤ 4/5 := by
        rw [show (31:ℕ).primesLE = ({2,3,5,7,11,13,17,19,23,29,31}:Finset ℕ) by decide]
        norm_num [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, sqrtLo]

private lemma tail_term_le {p : ℕ} (hp : p.Prime) (hp32 : 32 ≤ p) :
    Real.log (p:ℝ)/((p:ℝ)*((p:ℝ)-1)) ≤ (32/31) * (Real.log (p:ℝ)/(p:ℝ)^2) := by
  have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.two_le
  have hp0 : 0 < (p:ℝ) := by linarith
  have hpm1 : 0 < (p:ℝ)-1 := by linarith
  have hp32' : (32:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp32
  have hlog : 0 ≤ Real.log (p:ℝ) := Real.log_nonneg (by linarith)
  have hratio : (p:ℝ)/((p:ℝ)-1) ≤ 32/31 := by
    rw [div_le_div_iff₀ hpm1 (by norm_num)]
    nlinarith
  have hrew : Real.log (p:ℝ)/((p:ℝ)*((p:ℝ)-1))
      = (Real.log (p:ℝ)/(p:ℝ)^2) * ((p:ℝ)/((p:ℝ)-1)) := by
    field_simp
  rw [hrew]
  calc (Real.log (p:ℝ)/(p:ℝ)^2) * ((p:ℝ)/((p:ℝ)-1))
      ≤ (Real.log (p:ℝ)/(p:ℝ)^2) * (32/31) :=
        mul_le_mul_of_nonneg_left hratio (div_nonneg hlog (sq_nonneg _))
    _ = (32/31) * (Real.log (p:ℝ)/(p:ℝ)^2) := by ring

private lemma sum_Ico_succ_eq_Ico (a b : ℕ) (f : ℕ → ℝ) :
    (∑ i ∈ Finset.Ico a b, f (i+1)) = ∑ m ∈ Finset.Ico (a+1) (b+1), f m := by
  have h := Finset.sum_Ico_add (f := f) a b 1
  simpa [Nat.add_comm] using h

private lemma log_div_sq_antitone (n : ℕ) :
    AntitoneOn (fun x : ℝ => Real.log x / x^2) (Set.Icc 31 n) := by
  have hbase : AntitoneOn (fun x : ℝ => Real.log x / x ^ (2:ℝ)) (Set.Ici (Real.exp (1/2))) := by
    simpa using Real.log_div_self_rpow_antitoneOn (a := 2) (by norm_num)
  have hexp : Real.exp (1/2) ≤ (31:ℝ) := by
    have h1 : Real.exp (1/2) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
    have h2 : Real.exp 1 < 31 := by linarith [Real.exp_one_lt_d9]
    linarith
  have hsub : Set.Icc (31:ℝ) (n:ℝ) ⊆ Set.Ici (Real.exp (1/2)) := by
    intro x hx; exact le_trans hexp hx.1
  have h := hbase.mono hsub
  simpa [Real.rpow_natCast] using h

private lemma hasDerivAt_neg_log_succ_div (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => -(Real.log y + 1)/y) (Real.log x / x^2) x := by
  have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx
  have hnum : HasDerivAt (fun y : ℝ => -(Real.log y + 1)) (-(x⁻¹)) x :=
    (hlog.add_const 1).neg
  have hden : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have h := hnum.div hden hx
  have hval : (-(x⁻¹) * x - (-(Real.log x + 1)) * 1) / x^2 = Real.log x / x^2 := by
    field_simp
    ring
  rw [hval] at h
  exact h

private lemma cont_log_div_sq (n : ℕ) :
    ContinuousOn (fun x : ℝ => Real.log x / x^2) (Set.Icc (31:ℝ) (n:ℝ)) := by
  apply ContinuousOn.div
  · refine Real.continuousOn_log.mono ?_
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith [hx.1]
  · fun_prop
  · intro x hx
    exact pow_ne_zero 2 (by linarith [hx.1] : x ≠ 0)

private lemma integral_log_div_sq {n : ℕ} (hn : 31 ≤ n) :
    (∫ x in (31:ℝ)..(n:ℝ), Real.log x / x^2)
      = (Real.log 31 + 1)/31 - (Real.log (n:ℝ) + 1)/(n:ℝ) := by
  have hnR : (31:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hderiv : ∀ x ∈ Set.uIcc (31:ℝ) (n:ℝ),
      HasDerivAt (fun y : ℝ => -(Real.log y + 1)/y) (Real.log x / x^2) x := by
    intro x hx
    rw [Set.uIcc_of_le hnR] at hx
    exact hasDerivAt_neg_log_succ_div x (by linarith [hx.1] : x ≠ 0)
  have hint : IntervalIntegrable (fun x : ℝ => Real.log x / x^2) volume (31:ℝ) (n:ℝ) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hnR]
    exact cont_log_div_sq n
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  ring

private lemma sum_log_div_sq_Ico_le (n : ℕ) :
    (∑ m ∈ Finset.Ico 32 (n+1), Real.log (m:ℝ)/(m:ℝ)^2) ≤ 3/20 := by
  rcases lt_or_ge n 32 with hn | hn
  · have hempty : Finset.Ico 32 (n+1) = ∅ := Finset.Ico_eq_empty (by omega)
    rw [hempty]; norm_num
  · have hn31 : 31 ≤ n := by omega
    rw [← sum_Ico_succ_eq_Ico 31 n (fun m => Real.log (m:ℝ)/(m:ℝ)^2)]
    have hsum := AntitoneOn.sum_le_integral_Ico (f := fun x : ℝ => Real.log x / x^2)
      (a := 31) (b := n) hn31 (log_div_sq_antitone n)
    have hint := integral_log_div_sq hn31
    have hbound : (∫ x in (31:ℝ)..(n:ℝ), Real.log x / x^2) ≤ 3/20 := by
      rw [hint]
      have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
      have hlog31 : Real.log 31 ≤ 5 * Real.log 2 := by
        have hmono : Real.log 31 ≤ Real.log 32 := Real.log_le_log (by norm_num) (by norm_num)
        have h32 : Real.log (32:ℝ) = 5 * Real.log 2 := by
          rw [show (32:ℝ) = 2^5 by norm_num, Real.log_pow]
          norm_num
        linarith
      have hlog31' : Real.log 31 ≤ 3.65 := by nlinarith
      have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
      have hsub : 0 ≤ (Real.log (n:ℝ)+1)/(n:ℝ) := by
        apply div_nonneg
        · have : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
          linarith
        · exact hnpos.le
      have hfirst : (Real.log 31 + 1)/31 ≤ 3/20 := by
        rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
        nlinarith
      linarith
    linarith [hsum, hbound]

/-- The prime–power correction sum is at most `1`: for every `n`,
`∑_{p prime, p ≤ n} (log p)/(p·(p-1)) ≤ 1`.

(The true value of the infinite sum `∑_p (log p)/(p(p-1))` is about `0.7554`, so
there is comfortable room.)

Proof.  Split `n.primesLE` at `31`.

* For every prime `p ≥ 2` we have `log p ≤ (p-1)/√p`, hence
  `(log p)/(p(p-1)) ≤ 1/(p·√p)`.  Indeed `2 log √p ≤ √p - 1/√p` follows from
  `Real.self_le_sinh_iff` together with `Real.sinh_log : sinh (log y) = (y - y⁻¹)/2`
  (applied to `y = √p ≥ 1`), and `log p = 2 log √p` (`Real.log_pow`, `Real.sq_sqrt`).
* Primes `p ≤ 31`: `∑_{p ∈ (31:ℕ).primesLE} 1/(p·√p) ≤ 4/5`.  Rational lower bounds
  for `√p` (`Real.le_sqrt`) give `1/(p√p) ≤ 1/(p·q)` for explicit rationals `q`
  (`√2 ≥ 1.4142`, `√3 ≥ 1.732`, `√5 ≥ 2.236`, `√7 ≥ 2.6457`, `√11 ≥ 3.3166`,
  `√13 ≥ 3.6055`, `√17 ≥ 4.1231`, `√19 ≥ 4.3588`, `√23 ≥ 4.7958`, `√29 ≥ 5.3851`,
  `√31 ≥ 5.5677`), and `∑ 1/(p·q) ≈ 0.7856 ≤ 4/5` (`norm_num`).
* Primes `p ≥ 32`: `(log p)/(p(p-1)) = (log p)/p²·(p/(p-1)) ≤ (32/31)·(log p)/p²`,
  and `∑_{32 ≤ p ≤ n} (log p)/p² ≤ ∑_{m ∈ Ico 32 (n+1)} (log m)/m² ≤ 3/20`.  The last
  step compares the antitone function `x ↦ log x/x²` with the integral
  `∫_31^n log x/x² dx = (log 31+1)/31 - (log n+1)/n ≤ 3/20`; here
  `log 31 ≤ 5 log 2 < 3.4658`.
* Total `≤ 4/5 + (32/31)·(3/20) = 4/5 + 24/155 ≤ 1`
  (split the sum at `31` with `Finset.sum_filter_add_sum_filter_not`). -/
theorem sum_log_prime_div_p_mul_pred_le_one (n : ℕ) :
    (∑ p ∈ n.primesLE, Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) ≤ 1 := by
  set f : ℕ → ℝ := fun p => Real.log (p:ℝ) / ((p:ℝ) * ((p:ℝ) - 1)) with hf
  have hsplit := Finset.sum_filter_add_sum_filter_not n.primesLE (fun p => p ≤ 31) f
  have hpre : (∑ p ∈ n.primesLE with p ≤ 31, f p) ≤ 4/5 := by
    have hsub : (n.primesLE.filter (fun p => p ≤ 31)) ⊆ (31:ℕ).primesLE := by
      intro p hp
      rw [Finset.mem_filter] at hp
      rw [Nat.mem_primesLE] at hp ⊢
      exact ⟨hp.2, hp.1.2⟩
    have h1 : (∑ p ∈ n.primesLE with p ≤ 31, f p) ≤ ∑ p ∈ (31:ℕ).primesLE, f p :=
      Finset.sum_le_sum_of_subset_of_nonneg (f := f) hsub
        (fun p hp _ => log_div_pred_nonneg (Nat.mem_primesLE.mp hp).2)
    calc (∑ p ∈ n.primesLE with p ≤ 31, f p) ≤ ∑ p ∈ (31:ℕ).primesLE, f p := h1
      _ ≤ 4/5 := by simpa only [hf] using prefix_le
  have htail : (∑ p ∈ n.primesLE with ¬ (p ≤ 31), f p) ≤ 24/155 := by
    have h1 : (∑ p ∈ n.primesLE with ¬(p≤31), f p)
        ≤ ∑ p ∈ n.primesLE with ¬(p≤31), (32/31) * (Real.log (p:ℝ)/(p:ℝ)^2) := by
      apply Finset.sum_le_sum
      intro p hp
      rw [Finset.mem_filter] at hp
      have hprime := (Nat.mem_primesLE.mp hp.1).2
      have hp32 : 32 ≤ p := by omega
      simpa only [hf] using tail_term_le hprime hp32
    have h2 : (∑ p ∈ n.primesLE with ¬(p≤31), (32/31)*(Real.log (p:ℝ)/(p:ℝ)^2))
        = (32/31) * ∑ p ∈ n.primesLE with ¬(p≤31), (Real.log (p:ℝ)/(p:ℝ)^2) := by
      rw [Finset.mul_sum]
    have hsub : (n.primesLE.filter (fun p => ¬(p≤31))) ⊆ Finset.Ico 32 (n+1) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      have hp' := Nat.mem_primesLE.mp hp.1
      rw [Finset.mem_Ico]
      omega
    have h3 : (∑ p ∈ n.primesLE with ¬(p≤31), (Real.log (p:ℝ)/(p:ℝ)^2))
        ≤ ∑ m ∈ Finset.Ico 32 (n+1), Real.log (m:ℝ)/(m:ℝ)^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m hm _ => by
        have hm32 : 32 ≤ m := (Finset.mem_Ico.mp hm).1
        apply div_nonneg
        · exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m))
        · positivity)
    have h4 := sum_log_div_sq_Ico_le n
    calc (∑ p ∈ n.primesLE with ¬(p≤31), f p)
        ≤ ∑ p ∈ n.primesLE with ¬(p≤31), (32/31)*(Real.log (p:ℝ)/(p:ℝ)^2) := h1
      _ = (32/31) * ∑ p ∈ n.primesLE with ¬(p≤31), (Real.log (p:ℝ)/(p:ℝ)^2) := h2
      _ ≤ (32/31) * ∑ m ∈ Finset.Ico 32 (n+1), Real.log (m:ℝ)/(m:ℝ)^2 := by
          apply mul_le_mul_of_nonneg_left h3; norm_num
      _ ≤ (32/31) * (3/20) := by
          apply mul_le_mul_of_nonneg_left h4; norm_num
      _ = 24/155 := by norm_num
  have htot : (∑ p ∈ n.primesLE, f p) ≤ 4/5 + 24/155 := by linarith [hsplit, hpre, htail]
  have : (4:ℝ)/5 + 24/155 ≤ 1 := by norm_num
  linarith

end Commons.NumberTheory.Mertens