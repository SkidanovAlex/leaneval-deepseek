import Mathlib
import Submission.Work.RHContract.Corpus
import Submission.Commons.NumberTheory.Chebyshev.sum_prime_inv_sq_abel
import Submission.Commons.Analysis.Real.main_term_abel_identity
import Submission.Commons.Analysis.Real.integral_inv_sq_log_lower
import Submission.Commons.NumberTheory.Chebyshev.psi_sub_theta_le_three_sqrt

namespace Work.RHContract.A.RegionIII

open MeasureTheory
open scoped BigOperators

noncomputable section

/-! ## Auxiliary calculus: derivative and antiderivative bound

The three remainder integrals of the Abel estimate have the common shape
`∫_n^m (c·a·log t + q)/(t^{a+1}(log t)^2) dt`, bounded by `c/(n^a log n)` whenever `q ≤ c`.
The bound is the fundamental theorem of calculus applied to `t ↦ c/(t^a log t)`. -/

/-- `deriv (t ↦ c/(t^a log t)) = -(c·a·log t + c)/(t^{a+1}(log t)^2)`. -/
lemma hasDerivAt_inv_rpow_mul_log {a c t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun s : ℝ => c / (s ^ a * Real.log s))
      (-(c * a * Real.log t + c) / (t ^ (a + 1) * (Real.log t) ^ 2)) t := by
  have htpos : 0 < t := by linarith
  have ht0 : t ≠ 0 := by linarith
  have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht)
  have hu : HasDerivAt (fun s : ℝ => s ^ a) (a * t ^ (a - 1)) t :=
    Real.hasDerivAt_rpow_const (Or.inl ht0)
  have hl : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log ht0
  have hmul : HasDerivAt (fun s : ℝ => s ^ a * Real.log s)
      (a * t ^ (a - 1) * Real.log t + t ^ a * t⁻¹) t := hu.mul hl
  have hne : t ^ a * Real.log t ≠ 0 :=
    mul_ne_zero (ne_of_gt (Real.rpow_pos_of_pos htpos a)) hlog
  have hinv : HasDerivAt (fun s : ℝ => (s ^ a * Real.log s)⁻¹)
      (-(a * t ^ (a - 1) * Real.log t + t ^ a * t⁻¹) / (t ^ a * Real.log t) ^ 2) t :=
    hmul.inv hne
  have hF := hinv.const_mul c
  refine hF.congr_deriv ?_
  have hpow : t ^ a * t⁻¹ = t ^ (a - 1) := by
    calc t ^ a * t⁻¹ = t ^ a / t ^ (1:ℝ) := by rw [Real.rpow_one, div_eq_mul_inv]
      _ = t ^ (a - 1) := (Real.rpow_sub htpos a 1).symm
  have hden : (t ^ a * Real.log t) ^ 2 = t ^ (a + 1) * t ^ (a - 1) * (Real.log t) ^ 2 := by
    rw [mul_pow]
    have hta2 : (t ^ a) ^ 2 = t ^ (2 * a) := by
      rw [show (2*a:ℝ) = a + a by ring, Real.rpow_add htpos a a]; ring
    rw [hta2, show t ^ (2*a) = t^(a+1) * t^(a-1) by
      rw [← Real.rpow_add htpos (a+1) (a-1), show a+1+(a-1) = 2*a by ring]]
  rw [hpow, hden]
  have hta1 : t ^ (a - 1) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos htpos (a - 1))
  have hta : t ^ (a + 1) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos htpos (a + 1))
  field_simp

/-- The general antiderivative bound `∫_n^m (c·a·log t + q)/(t^{a+1}(log t)^2) ≤ c/(n^a log n)`. -/
lemma integral_rpow_log_le {n m a c q : ℝ} (hn : 1 < n) (hnm : n ≤ m)
    (hc : 0 < c) (hq : q ≤ c) :
    ∫ t in n..m, (c * a * Real.log t + q) / (t ^ (a + 1) * (Real.log t) ^ 2)
      ≤ c / (n ^ a * Real.log n) := by
  have hcont : ContinuousOn (fun t : ℝ => (c * a * Real.log t + c) / (t ^ (a+1) * (Real.log t)^2))
      (Set.Icc n m) := by
    have hlog : ContinuousOn Real.log (Set.Icc n m) :=
      Real.continuousOn_log.mono (fun x hx => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        have h1 : 1 < x := lt_of_lt_of_le hn hx.1
        linarith)
    have hid : ContinuousOn (fun x : ℝ => x) (Set.Icc n m) := continuousOn_id
    have hnum : ContinuousOn (fun x : ℝ => c * a * Real.log x + c) (Set.Icc n m) :=
      ((continuousOn_const.mul continuousOn_const).mul hlog).add continuousOn_const
    have hpow : ContinuousOn (fun x : ℝ => x ^ (a+1)) (Set.Icc n m) :=
      hid.rpow_const (fun x hx => Or.inl (by have h1 : 1 < x := lt_of_lt_of_le hn hx.1; linarith))
    have hden : ContinuousOn (fun x : ℝ => x ^ (a+1) * (Real.log x)^2) (Set.Icc n m) :=
      hpow.mul (hlog.pow 2)
    refine hnum.div hden (fun x hx => ?_)
    have h1 : 1 < x := lt_of_lt_of_le hn hx.1
    have hl0 : Real.log x ≠ 0 := ne_of_gt (Real.log_pos h1)
    exact mul_ne_zero (ne_of_gt (Real.rpow_pos_of_pos (by linarith) (a+1))) (pow_ne_zero 2 hl0)
  have hcont_f : ContinuousOn (fun t : ℝ => (c * a * Real.log t + q) / (t ^ (a+1) * (Real.log t)^2))
      (Set.Icc n m) := by
    have hlog : ContinuousOn Real.log (Set.Icc n m) :=
      Real.continuousOn_log.mono (fun x hx => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        have h1 : 1 < x := lt_of_lt_of_le hn hx.1
        linarith)
    have hid : ContinuousOn (fun x : ℝ => x) (Set.Icc n m) := continuousOn_id
    have hnum : ContinuousOn (fun x : ℝ => c * a * Real.log x + q) (Set.Icc n m) :=
      ((continuousOn_const.mul continuousOn_const).mul hlog).add continuousOn_const
    have hpow : ContinuousOn (fun x : ℝ => x ^ (a+1)) (Set.Icc n m) :=
      hid.rpow_const (fun x hx => Or.inl (by have h1 : 1 < x := lt_of_lt_of_le hn hx.1; linarith))
    have hden : ContinuousOn (fun x : ℝ => x ^ (a+1) * (Real.log x)^2) (Set.Icc n m) :=
      hpow.mul (hlog.pow 2)
    refine hnum.div hden (fun x hx => ?_)
    have h1 : 1 < x := lt_of_lt_of_le hn hx.1
    have hl0 : Real.log x ≠ 0 := ne_of_gt (Real.log_pos h1)
    exact mul_ne_zero (ne_of_gt (Real.rpow_pos_of_pos (by linarith) (a+1))) (pow_ne_zero 2 hl0)
  have hint_g : IntervalIntegrable
      (fun t : ℝ => (c * a * Real.log t + c)/(t^(a+1)*(Real.log t)^2)) volume n m :=
    hcont.intervalIntegrable_of_Icc (μ := volume) hnm
  have hint_f : IntervalIntegrable
      (fun t : ℝ => (c * a * Real.log t + q)/(t^(a+1)*(Real.log t)^2)) volume n m :=
    hcont_f.intervalIntegrable_of_Icc (μ := volume) hnm
  have hmono : ∫ t in n..m, (c * a * Real.log t + q)/(t^(a+1)*(Real.log t)^2)
      ≤ ∫ t in n..m, (c * a * Real.log t + c)/(t^(a+1)*(Real.log t)^2) := by
    refine intervalIntegral.integral_mono_on hnm hint_f hint_g (fun x hx => ?_)
    have h1 : 1 < x := lt_of_lt_of_le hn hx.1
    have hnum : c * a * Real.log x + q ≤ c * a * Real.log x + c := by linarith
    have hden : 0 < x ^ (a+1) * (Real.log x)^2 :=
      mul_pos (Real.rpow_pos_of_pos (by linarith) (a+1)) (pow_pos (Real.log_pos h1) 2)
    exact div_le_div_of_nonneg_right hnum hden.le
  have hderiv : ∀ x ∈ Set.uIcc n m,
      HasDerivAt (fun s : ℝ => -(c / (s ^ a * Real.log s)))
        ((c * a * Real.log x + c) / (x ^ (a + 1) * (Real.log x) ^ 2)) x := by
    intro x hx
    rw [Set.uIcc_of_le hnm] at hx
    have hx1 : 1 < x := lt_of_lt_of_le hn hx.1
    have h := (hasDerivAt_inv_rpow_mul_log (a := a) (c := c) hx1).neg
    refine h.congr_deriv ?_
    ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint_g
  have hval : -(c / (m ^ a * Real.log m)) - (-(c / (n ^ a * Real.log n)))
      = c / (n ^ a * Real.log n) - c / (m ^ a * Real.log m) := by ring
  rw [hval] at hFTC
  have hle : c / (n ^ a * Real.log n) - c / (m ^ a * Real.log m) ≤ c / (n ^ a * Real.log n) := by
    have : 0 ≤ c / (m ^ a * Real.log m) :=
      div_nonneg hc.le (mul_pos (Real.rpow_pos_of_pos (by linarith) a) (Real.log_pos (by linarith))).le
    linarith
  linarith [hmono, hFTC.symm.le, hle]

/-! ## The three remainder bounds -/

/-- `∫_n^m (2 log t + 1)/(t^3 log²t) · (9/20) t^{3/4} ≤ 0.76/(n^{5/4} log n)`. -/
lemma integral_045_rpow_le {n m : ℝ} (hn : 1 < n) (hnm : n ≤ m) :
    ∫ t in n..m, ((2*Real.log t + 1)/(t^3 * (Real.log t)^2)) * (0.45 * t ^ (3/4:ℝ))
      ≤ 0.76 / (n ^ (5/4:ℝ) * Real.log n) := by
  have hbase := integral_rpow_log_le (n:=n) (m:=m) (a:=5/4) (c:=0.72) (q:=0.45)
    hn hnm (by norm_num) (by norm_num)
  have heq : ∫ t in n..m, ((2*Real.log t+1)/(t^3*(Real.log t)^2)) * (0.45*t^(3/4:ℝ))
      = ∫ t in n..m, (0.72 * (5/4:ℝ) * Real.log t + 0.45)/(t^(5/4+1:ℝ)*(Real.log t)^2) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hnm] at ht
    have ht1 : 1 < t := lt_of_lt_of_le hn ht.1
    have hL : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht1)
    have ht0 : (0:ℝ) < t := by linarith
    show ((2*Real.log t + 1)/(t^3 * (Real.log t)^2)) * (0.45 * t ^ (3/4:ℝ))
      = (0.72 * (5/4:ℝ) * Real.log t + 0.45)/(t^(5/4+1:ℝ)*(Real.log t)^2)
    have hsub : t ^ (9/4:ℝ) = t ^ (3:ℝ) / t ^ (3/4:ℝ) := by
      rw [← Real.rpow_sub ht0 (3:ℝ) (3/4:ℝ), show (3:ℝ) - 3/4 = 9/4 by norm_num]
    have h3 : (t^3:ℝ) = t^(3:ℝ) := (Real.rpow_natCast t 3).symm
    rw [show (5/4:ℝ)+1 = 9/4 by norm_num, h3, hsub]
    field_simp
    ring
  rw [heq]
  calc ∫ t in n..m, (0.72 * (5/4:ℝ) * Real.log t + 0.45)/(t^(5/4+1:ℝ)*(Real.log t)^2)
      ≤ 0.72 / (n ^ (5/4:ℝ) * Real.log n) := hbase
    _ ≤ 0.76 / (n ^ (5/4:ℝ) * Real.log n) := by
        apply div_le_div_of_nonneg_right (by norm_num)
        exact (mul_pos (Real.rpow_pos_of_pos (by linarith) (5/4:ℝ)) (Real.log_pos hn)).le

/-- `∫_n^m (2 log t + 1)/(t^3 log²t) · 2 ≤ 2/(n² log n)`. -/
lemma integral_two_h_le {n m : ℝ} (hn : 1 < n) (hnm : n ≤ m) :
    ∫ t in n..m, ((2*Real.log t + 1)/(t^3 * (Real.log t)^2)) * 2
      ≤ 2 / (n ^ 2 * Real.log n) := by
  have hbase := integral_rpow_log_le (n:=n) (m:=m) (a:=2) (c:=2) (q:=2)
    hn hnm (by norm_num) (by norm_num)
  have heq : ∫ t in n..m, ((2*Real.log t+1)/(t^3*(Real.log t)^2)) * 2
      = ∫ t in n..m, (2 * (2:ℝ) * Real.log t + 2)/(t^(2+1:ℝ)*(Real.log t)^2) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hnm] at ht
    have ht1 : 1 < t := lt_of_lt_of_le hn ht.1
    have hL : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht1)
    show ((2*Real.log t + 1)/(t^3 * (Real.log t)^2)) * 2
      = (2 * (2:ℝ) * Real.log t + 2)/(t^(2+1:ℝ)*(Real.log t)^2)
    have h3 : (t^3:ℝ) = t^(3:ℝ) := (Real.rpow_natCast t 3).symm
    rw [show (2:ℝ)+1 = 3 by norm_num]
    rw [← h3]
    ring
  rw [heq]
  rw [show n ^ (2:ℝ) = n ^ (2:ℕ) from Real.rpow_natCast n 2] at hbase
  exact hbase

/-- `∫_n^m (2 log t + 1)/(t^3 log²t) · 3√t ≤ 4.25/(n^{3/2} log n)`. -/
lemma integral_three_sqrt_h_le {n m : ℝ} (hn : 1 < n) (hnm : n ≤ m) :
    ∫ t in n..m, ((2*Real.log t + 1)/(t^3 * (Real.log t)^2)) * (3 * Real.sqrt t)
      ≤ 4.25 / (n ^ (3/2:ℝ) * Real.log n) := by
  have hbase := integral_rpow_log_le (n:=n) (m:=m) (a:=3/2) (c:=4) (q:=3)
    hn hnm (by norm_num) (by norm_num)
  have heq : ∫ t in n..m, ((2*Real.log t+1)/(t^3*(Real.log t)^2)) * (3*Real.sqrt t)
      = ∫ t in n..m, (4 * (3/2:ℝ) * Real.log t + 3)/(t^(3/2+1:ℝ)*(Real.log t)^2) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hnm] at ht
    have ht1 : 1 < t := lt_of_lt_of_le hn ht.1
    have hL : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht1)
    have ht0 : (0:ℝ) < t := by linarith
    show ((2*Real.log t + 1)/(t^3 * (Real.log t)^2)) * (3 * Real.sqrt t)
      = (4 * (3/2:ℝ) * Real.log t + 3)/(t^(3/2+1:ℝ)*(Real.log t)^2)
    have hsub : t ^ (5/2:ℝ) = t ^ (3:ℝ) / t ^ (1/2:ℝ) := by
      rw [← Real.rpow_sub ht0 (3:ℝ) (1/2:ℝ), show (3:ℝ) - 1/2 = 5/2 by norm_num]
    have h3 : (t^3:ℝ) = t^(3:ℝ) := (Real.rpow_natCast t 3).symm
    rw [show (3/2:ℝ)+1 = 5/2 by norm_num, Real.sqrt_eq_rpow, h3, hsub]
    field_simp
    ring
  rw [heq]
  calc ∫ t in n..m, (4 * (3/2:ℝ) * Real.log t + 3)/(t^(3/2+1:ℝ)*(Real.log t)^2)
      ≤ 4 / (n ^ (3/2:ℝ) * Real.log n) := hbase
    _ ≤ 4.25 / (n ^ (3/2:ℝ) * Real.log n) := by
        apply div_le_div_of_nonneg_right (by norm_num)
        exact (mul_pos (Real.rpow_pos_of_pos (by linarith) (3/2:ℝ)) (Real.log_pos hn)).le

/-! ## The main theorem -/

/-- **Abel/partial-summation lower bound for `∑ 1/p²` over the primes in `(n, m]`.**

`ψ` satisfies the Chebyshev-type envelope `|ψ t − t| ≤ 0.45 t^{3/4} + 2` on `[n, m]` (a
`RiemannHypothesis` consequence, `Work.RHContract.A.psi_sub_le_of_RH`), and `θ n ≤ Θ`.  Then,
with `g t = 1/(t² log t)`, `E t = 0.45 t^{3/4} + 2 + 3√t` and `h t = (2 log t + 1)/(t³ log² t)`
(so that `t − E t ≤ θ t ≤ t + (E t − 3√t)` on `[n,m]` and `h ≥ 0`),

`∑_{n < p ≤ m} 1/p²  ≥  ∫_n^m dt/(t² log t)  −  E m · g m  −  (Θ − n)·(1/(n² log n))  −  ∫_n^m E t · h t`

and the three explicit remainder bounds `∫ 0.45 t^{3/4} h ≤ 0.76/(n^{5/4} log n)`,
`∫ 2 h ≤ 2/(n² log n)`, `∫ 3√t h ≤ 4.25/(n^{3/2} log n)` (valid for `n ≥ 15000`), together with
`∫_n^m dt/(t² log t) ≥ (1/(n log n))(1 − n/min(m,n²) − 1/log n)`, give the stated closed form. -/
theorem sum_prime_inv_sq_lower_A2 {n m : ℕ} {Θ : ℝ} (hn : 15000 ≤ n) (hnm : n ≤ m)
    (hΘ : Chebyshev.theta (n : ℝ) ≤ Θ)
    (hA2 : ∀ t : ℝ, (n : ℝ) ≤ t → |Chebyshev.psi t - t| ≤ 0.45 * t ^ (3 / 4 : ℝ) + 2) :
    (∑ p ∈ Finset.Ioc n m, if p.Prime then (1 : ℝ) / ((p : ℝ) ^ 2) else 0)
      ≥ (1 / ((n : ℝ) * Real.log n))
          * (1 - (n : ℝ) / min (m : ℝ) ((n : ℝ) ^ 2) - 1 / Real.log (n : ℝ))
        - ((0.45 * (m : ℝ) ^ (3 / 4 : ℝ) + 2 + 3 * Real.sqrt (m : ℝ))
              / ((m : ℝ) ^ 2 * Real.log m)
           + (Θ - n) / ((n : ℝ) ^ 2 * Real.log n)
           + 0.76 / ((n : ℝ) ^ (5 / 4 : ℝ) * Real.log n)
           + 2 / ((n : ℝ) ^ 2 * Real.log n)
           + 4.25 / ((n : ℝ) ^ (3 / 2 : ℝ) * Real.log n)) := by
  have hn2 : 2 ≤ n := by omega
  have hn1 : (1:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hnm' : (n:ℝ) ≤ (m:ℝ) := by exact_mod_cast hnm
  have hm1 : (1:ℝ) < (m:ℝ) := lt_of_lt_of_le hn1 hnm'
  have hln : 0 < Real.log (n:ℝ) := Real.log_pos hn1
  have hlm : 0 < Real.log (m:ℝ) := Real.log_pos hm1
  -- The Chebyshev envelope for `θ`.
  have htheta : ∀ t : ℝ, (n:ℝ) ≤ t →
      t - (0.45 * t ^ (3/4:ℝ) + 2 + 3 * Real.sqrt t) ≤ Chebyshev.theta t := by
    intro t ht
    have ht1 : (1:ℝ) ≤ t := le_trans hn1.le ht
    have hψ := hA2 t ht
    have hψlow : t - (0.45 * t ^ (3/4:ℝ) + 2) ≤ Chebyshev.psi t := by
      have := (abs_le.mp hψ).1
      linarith
    have hdiff : Chebyshev.psi t - Chebyshev.theta t ≤ 3 * Real.sqrt t :=
      Commons.NumberTheory.Chebyshev.psi_sub_theta_le_three_sqrt t ht1
    linarith
  -- named quantities
  set Tm : ℝ := (1 / ((m : ℝ) ^ 2 * Real.log m)) * Chebyshev.theta (m : ℝ) with hTmdef
  set Tn : ℝ := (1 / ((n : ℝ) ^ 2 * Real.log n)) * Chebyshev.theta (n : ℝ) with hTndef
  set Iθ : ℝ := ∫ t in (n:ℝ)..(m:ℝ),
      ((2*Real.log t + 1)/(t^3 * (Real.log t)^2)) * Chebyshev.theta t with hIθdef
  set It : ℝ := ∫ t in (n:ℝ)..(m:ℝ),
      ((2*Real.log t + 1)/(t^3 * (Real.log t)^2)) * t with hItdef
  set IE : ℝ := ∫ t in (n:ℝ)..(m:ℝ),
      ((2*Real.log t + 1)/(t^3 * (Real.log t)^2)) * (0.45*t^(3/4:ℝ) + 2 + 3*Real.sqrt t) with hIEdef
  set J1 : ℝ := ∫ t in (n:ℝ)..(m:ℝ),
      ((2*Real.log t + 1)/(t^3 * (Real.log t)^2)) * (0.45 * t ^ (3/4:ℝ)) with hJ1def
  set J2 : ℝ := ∫ t in (n:ℝ)..(m:ℝ),
      ((2*Real.log t + 1)/(t^3 * (Real.log t)^2)) * 2 with hJ2def
  set J3 : ℝ := ∫ t in (n:ℝ)..(m:ℝ),
      ((2*Real.log t + 1)/(t^3 * (Real.log t)^2)) * (3 * Real.sqrt t) with hJ3def
  set A : ℝ := ∫ t in (n:ℝ)..(m:ℝ), 1/(t^2 * Real.log t) with hAdef
  set M : ℝ := (1 / ((n : ℝ) * Real.log n))
          * (1 - (n : ℝ) / min (m : ℝ) ((n : ℝ) ^ 2) - 1 / Real.log (n : ℝ)) with hMdef
  set Eterm : ℝ := (0.45 * (m : ℝ) ^ (3 / 4 : ℝ) + 2 + 3 * Real.sqrt (m : ℝ))
              / ((m : ℝ) ^ 2 * Real.log m) with hEtermdef
  set Q : ℝ := (Θ - n) / ((n : ℝ) ^ 2 * Real.log n) with hQdef
  set A1 : ℝ := 0.76 / ((n : ℝ) ^ (5 / 4 : ℝ) * Real.log n) with hA1def
  set A2 : ℝ := 2 / ((n : ℝ) ^ 2 * Real.log n) with hA2def
  set A3 : ℝ := 4.25 / ((n : ℝ) ^ (3 / 2 : ℝ) * Real.log n) with hA3def
  -- boundary terms
  have hdenm : 0 < (m:ℝ)^2 * Real.log m := by positivity
  have hdenn : 0 < (n:ℝ)^2 * Real.log n := by positivity
  have hTm : 1/((m:ℝ)*Real.log m) - Eterm ≤ Tm := by
    rw [hEtermdef, hTmdef]
    have hθm : (m:ℝ) - (0.45*(m:ℝ)^(3/4:ℝ) + 2 + 3*Real.sqrt (m:ℝ)) ≤ Chebyshev.theta (m:ℝ) :=
      htheta (m:ℝ) hnm'
    have h1 := mul_le_mul_of_nonneg_left hθm (le_of_lt (div_pos one_pos hdenm))
    have heq : (1/((m:ℝ)^2*Real.log m)) * ((m:ℝ) - (0.45*(m:ℝ)^(3/4:ℝ)+2+3*Real.sqrt (m:ℝ)))
        = 1/((m:ℝ)*Real.log m) - (0.45*(m:ℝ)^(3/4:ℝ)+2+3*Real.sqrt (m:ℝ))/((m:ℝ)^2*Real.log m) := by
      field_simp
    rw [heq] at h1
    exact h1
  have hTn : Tn ≤ Θ/((n:ℝ)^2*Real.log n) := by
    rw [hTndef]
    have h1 := mul_le_mul_of_nonneg_left hΘ (le_of_lt (div_pos one_pos hdenn))
    have heq : (1/((n:ℝ)^2*Real.log n)) * Θ = Θ/((n:ℝ)^2*Real.log n) := by ring
    rw [heq] at h1
    exact h1
  -- the integral of `h·θ` dominates the integral of `h·(t - E)`
  have h3 : It - IE ≤ Iθ := by
    rw [hItdef, hIEdef, hIθdef]
    have hcontH : ContinuousOn (fun t : ℝ => (2*Real.log t + 1)/(t^3*(Real.log t)^2))
        (Set.Icc (n:ℝ) (m:ℝ)) := by
      have hlog : ContinuousOn Real.log (Set.Icc (n:ℝ) (m:ℝ)) :=
        Real.continuousOn_log.mono (fun x hx => by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          have h1 : 1 < x := lt_of_lt_of_le hn1 hx.1
          linarith)
      have hid : ContinuousOn (fun x : ℝ => x) (Set.Icc (n:ℝ) (m:ℝ)) := continuousOn_id
      have hnum : ContinuousOn (fun x : ℝ => 2*Real.log x + 1) (Set.Icc (n:ℝ) (m:ℝ)) :=
        (continuousOn_const.mul hlog).add continuousOn_const
      exact hnum.div ((hid.pow 3).mul (hlog.pow 2)) (fun x hx => by
        have h1 : 1 < x := lt_of_lt_of_le hn1 hx.1
        exact mul_ne_zero (pow_ne_zero 3 (by linarith)) (pow_ne_zero 2 (ne_of_gt (Real.log_pos h1))))
    have hcontT : ContinuousOn (fun x : ℝ => x) (Set.Icc (n:ℝ) (m:ℝ)) := continuousOn_id
    have hcontEf : ContinuousOn (fun x : ℝ => 0.45*x^(3/4:ℝ) + 2 + 3*Real.sqrt x)
        (Set.Icc (n:ℝ) (m:ℝ)) := by
      have hid : ContinuousOn (fun x : ℝ => x) (Set.Icc (n:ℝ) (m:ℝ)) := continuousOn_id
      have hp : ContinuousOn (fun x : ℝ => x^(3/4:ℝ)) (Set.Icc (n:ℝ) (m:ℝ)) :=
        hid.rpow_const (fun x hx => Or.inl (by have h1 : 1 < x := lt_of_lt_of_le hn1 hx.1; linarith))
      exact ((continuousOn_const.mul hp).add continuousOn_const).add
        (continuousOn_const.mul Real.continuous_sqrt.continuousOn)
    have i1 : IntervalIntegrable
        (fun t : ℝ => ((2*Real.log t + 1)/(t^3*(Real.log t)^2)) * t) volume (n:ℝ) (m:ℝ) :=
      (hcontH.mul hcontT).intervalIntegrable_of_Icc (μ := volume) hnm'
    have i2 : IntervalIntegrable
        (fun t : ℝ => ((2*Real.log t + 1)/(t^3*(Real.log t)^2))
          * (0.45*t^(3/4:ℝ)+2+3*Real.sqrt t)) volume (n:ℝ) (m:ℝ) :=
      (hcontH.mul hcontEf).intervalIntegrable_of_Icc (μ := volume) hnm'
    have hcontH_u : ContinuousOn (fun t : ℝ => (2*Real.log t + 1)/(t^3*(Real.log t)^2))
        (Set.uIcc (n:ℝ) (m:ℝ)) := by rw [Set.uIcc_of_le hnm']; exact hcontH
    have i3 : IntervalIntegrable
        (fun t : ℝ => ((2*Real.log t + 1)/(t^3*(Real.log t)^2)) * Chebyshev.theta t)
        volume (n:ℝ) (m:ℝ) :=
      Chebyshev.theta_mono.intervalIntegrable.continuousOn_mul hcontH_u
    rw [← intervalIntegral.integral_sub i1 i2]
    refine intervalIntegral.integral_mono_on hnm' (i1.sub i2) i3 (fun x hx => ?_)
    have hx1 : 1 < x := lt_of_lt_of_le hn1 hx.1
    have hlogpos : 0 < Real.log x := Real.log_pos hx1
    have hHnn : 0 ≤ (2*Real.log x + 1)/(x^3*(Real.log x)^2) :=
      div_nonneg (by linarith) (mul_pos (pow_pos (by linarith) 3) (pow_pos hlogpos 2)).le
    have hpt : x - (0.45*x^(3/4:ℝ) + 2 + 3*Real.sqrt x) ≤ Chebyshev.theta x :=
      htheta x hx.1
    have hkey := mul_le_mul_of_nonneg_left hpt hHnn
    show ((2*Real.log x + 1)/(x^3*(Real.log x)^2)) * x
        - ((2*Real.log x + 1)/(x^3*(Real.log x)^2)) * (0.45*x^(3/4:ℝ)+2+3*Real.sqrt x)
      ≤ ((2*Real.log x + 1)/(x^3*(Real.log x)^2)) * Chebyshev.theta x
    rw [← mul_sub]
    exact hkey
  -- Abel identity for the `t`-weighted integral
  have hIt : It = A - (1/((m:ℝ)*Real.log m) - 1/((n:ℝ)*Real.log n)) := by
    rw [hItdef, hAdef]
    have hmain := Commons.Analysis.Real.main_term_abel_identity (n := (n:ℝ)) (m := (m:ℝ)) hn1 hnm'
    rw [← intervalIntegral.integral_of_le hnm'] at hmain
    have e1 : (1/((m:ℝ)^2*Real.log m)) * (m:ℝ) = 1/((m:ℝ)*Real.log m) := by
      field_simp
    have e2 : (1/((n:ℝ)^2*Real.log n)) * (n:ℝ) = 1/((n:ℝ)*Real.log n) := by
      field_simp
    rw [e1, e2] at hmain
    linarith [hmain]
  -- decomposition of the `E`-weighted integral
  have hIE : IE = J1 + J2 + J3 := by
    rw [hIEdef, hJ1def, hJ2def, hJ3def]
    have hcontH : ContinuousOn (fun t : ℝ => (2*Real.log t + 1)/(t^3*(Real.log t)^2))
        (Set.Icc (n:ℝ) (m:ℝ)) := by
      have hlog : ContinuousOn Real.log (Set.Icc (n:ℝ) (m:ℝ)) :=
        Real.continuousOn_log.mono (fun x hx => by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          have h1 : 1 < x := lt_of_lt_of_le hn1 hx.1
          linarith)
      have hid : ContinuousOn (fun x : ℝ => x) (Set.Icc (n:ℝ) (m:ℝ)) := continuousOn_id
      have hnum : ContinuousOn (fun x : ℝ => 2*Real.log x + 1) (Set.Icc (n:ℝ) (m:ℝ)) :=
        (continuousOn_const.mul hlog).add continuousOn_const
      exact hnum.div ((hid.pow 3).mul (hlog.pow 2)) (fun x hx => by
        have h1 : 1 < x := lt_of_lt_of_le hn1 hx.1
        exact mul_ne_zero (pow_ne_zero 3 (by linarith)) (pow_ne_zero 2 (ne_of_gt (Real.log_pos h1))))
    have hrp : ContinuousOn (fun x : ℝ => x^(3/4:ℝ)) (Set.Icc (n:ℝ) (m:ℝ)) :=
      continuousOn_id.rpow_const
        (fun x hx => Or.inr (by norm_num))
    have i1 : IntervalIntegrable
        (fun t : ℝ => ((2*Real.log t+1)/(t^3*(Real.log t)^2)) * (0.45*t^(3/4:ℝ))) volume (n:ℝ) (m:ℝ) :=
      (hcontH.mul (continuousOn_const.mul hrp)).intervalIntegrable_of_Icc (μ := volume) hnm'
    have i2 : IntervalIntegrable
        (fun t : ℝ => ((2*Real.log t+1)/(t^3*(Real.log t)^2)) * 2) volume (n:ℝ) (m:ℝ) :=
      (hcontH.mul continuousOn_const).intervalIntegrable_of_Icc (μ := volume) hnm'
    have i3 : IntervalIntegrable
        (fun t : ℝ => ((2*Real.log t+1)/(t^3*(Real.log t)^2)) * (3*Real.sqrt t)) volume (n:ℝ) (m:ℝ) :=
      (hcontH.mul (continuousOn_const.mul Real.continuous_sqrt.continuousOn)).intervalIntegrable_of_Icc (μ := volume) hnm'
    rw [← intervalIntegral.integral_add i1 i2, ← intervalIntegral.integral_add (i1.add i2) i3]
    apply intervalIntegral.integral_congr
    intro t ht
    show ((2*Real.log t + 1)/(t^3*(Real.log t)^2)) * (0.45*t^(3/4:ℝ)+2+3*Real.sqrt t)
      = ((2*Real.log t + 1)/(t^3*(Real.log t)^2)) * (0.45*t^(3/4:ℝ))
        + ((2*Real.log t + 1)/(t^3*(Real.log t)^2)) * 2
        + ((2*Real.log t + 1)/(t^3*(Real.log t)^2)) * (3*Real.sqrt t)
    ring
  -- the three explicit remainder bounds
  have hJ1 : J1 ≤ A1 := by rw [hJ1def, hA1def]; exact integral_045_rpow_le hn1 hnm'
  have hJ2 : J2 ≤ A2 := by rw [hJ2def, hA2def]; exact integral_two_h_le hn1 hnm'
  have hJ3 : J3 ≤ A3 := by rw [hJ3def, hA3def]; exact integral_three_sqrt_h_le hn1 hnm'
  -- the main term
  have hA : M ≤ A := by
    rw [hMdef, hAdef]
    exact Commons.Analysis.Real.integral_inv_sq_log_lower hn1 hnm'
  have hQ : 1/((n:ℝ)*Real.log n) - Θ/((n:ℝ)^2*Real.log n) = -Q := by
    rw [hQdef]
    field_simp
    ring
  have hchain : M - (Eterm + Q + A1 + A2 + A3) ≤ Tm - Tn + Iθ := by
    linarith [hA, hTm, hTn, h3, hIt, hIE, hJ1, hJ2, hJ3, hQ]
  rw [Commons.NumberTheory.Chebyshev.sum_prime_inv_sq_abel hn2 hnm]
  rw [← intervalIntegral.integral_of_le hnm']
  rw [← hIθdef, ← hTmdef, ← hTndef]
  exact hchain

end

end Work.RHContract.A.RegionIII
