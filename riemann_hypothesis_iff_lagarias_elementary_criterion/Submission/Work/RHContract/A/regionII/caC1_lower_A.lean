import Mathlib
import Submission.Work.RHContract.A.regionII.abdefs
import Submission.Work.RHContract.A.regionII.abel_ht_lower
import Submission.Work.RHContract.A.regionII.abel_h_upper
import Submission.Work.RHContract.A.regionII.abel_hsqrt_upper
import Submission.Work.RHContract.A.regionII.theta_deficit_cert_173_501
import Submission.Work.RHContract.A.regionII.Defs
import Submission.Work.RHContract.A.caXi2_le_sqrt

/-!
# `Margin.caC1 ε ≥ (498/1000) · abS n ξ` in region A of Region II

For `ξ = caXi ε ∈ [3·10^4, 10^5)` and `n = max (ξ₂(ε), 173)` this file proves

`(498/1000) · abS n ξ ≤ Margin.caC1 ε`,

where `Margin.caC1 ε = Σ_{ξ₂ < p ≤ ξ} (1/(2p²) − 1/(3p³))`.

The two ingredients are

* the Abel lower bound `abS n ξ ≤ Σ_{n<p≤ξ} 1/p²` (module-local theorem
  `caC1_lower_A_abS_le`, an `abS`-analogue of the classical Abel summation bound for
  `Σ 1/p²`), and
* the per-prime comparison `(498/1000)/p² ≤ 1/(2p²) − 1/(3p³)` for `p ≥ 173`
  (since `1/(3p) ≤ 1/519 < 1/500`),

together with `ξ₂(ε) ≤ n`: `caC1 ε` sums over the strictly larger range `(ξ₂, ξ]`, so

`(498/1000)·abS n ξ ≤ (498/1000)·Σ_{n<p≤ξ} 1/p² ≤ Σ_{n<p≤ξ} (1/(2p²) − 1/(3p³)) ≤ caC1 ε`.

The hypotheses fed to `caC1_lower_A_abS_le` are `n ≤ 501` (from `ξ₂ ≤ √(2.5ξ) + 1 < 501`
via `caXi2_le_sqrt`), the certified `θ`-bracket on `[173,501]`
(`theta_deficit_cert_173_501`), the Chebyshev table bound `θ ξ ≥ (96/100) ξ`
(`theta_bracket_finite_range`, valid for `1531 ≤ ξ ≤ 10^5`) and the hypothesis `hθ`.

The Abel bound splits the range at `501`, using `θ t ≥ t − 1 − (189/100)√t` on `(n,501]`
(where `t` is rounded down to the integer bound of `theta_deficit_cert_173_501`) and
`θ t ≥ t − (23/10)√t` on `[501, ξ]`, and the three Abel-kernel integrals
`abel_ht_lower`, `abel_h_upper`, `abel_hsqrt_upper`.
-/

namespace Work.RHContract.A.regionII

open MeasureTheory Finset
open scoped BigOperators

/-! ## Elementary helpers -/

/-- `θ` depends only on `⌊t⌋₊`. -/
lemma caC1_lower_A_theta_eq_theta_floor (t : ℝ) :
    Chebyshev.theta t = Chebyshev.theta ((⌊t⌋₊ : ℝ)) := by
  rw [Chebyshev.theta_eq_sum_primesLE, Chebyshev.theta_eq_sum_primesLE, Nat.floor_natCast]

/-- The Abel kernel `t ↦ (2 log t + 1)/(t ^ 3 (log t) ^ 2)` is nonnegative for `t ≥ 1`. -/
lemma caC1_lower_A_kernel_nonneg {t : ℝ} (ht : 1 ≤ t) :
    0 ≤ (2*Real.log t + 1)/(t^3*(Real.log t)^2) := by
  have hnum : 0 ≤ 2*Real.log t + 1 := by
    have := Real.log_nonneg ht; linarith
  exact div_nonneg hnum (by positivity)

/-- Continuity of `t ↦ (2 log t + 1)/(t ^ 2 (log t) ^ 2)` on `[a,b]`, `1 < a`. -/
lemma caC1_lower_A_continuousOn_h2 {a b : ℝ} (ha : 1 < a) :
    ContinuousOn (fun t : ℝ => (2*Real.log t + 1)/(t^2*(Real.log t)^2)) (Set.Icc a b) := by
  have hlog : ContinuousOn Real.log (Set.Icc a b) :=
    Real.continuousOn_log.mono (fun x hx => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      have : 1 < x := lt_of_lt_of_le ha hx.1
      linarith)
  have hid : ContinuousOn (fun x : ℝ => x) (Set.Icc a b) := continuousOn_id
  have hnum : ContinuousOn (fun x : ℝ => 2*Real.log x + 1) (Set.Icc a b) :=
    (hlog.const_mul 2).add continuousOn_const
  have hden : ContinuousOn (fun x : ℝ => x^2*(Real.log x)^2) (Set.Icc a b) :=
    (hid.pow 2).mul (hlog.pow 2)
  exact hnum.div hden (fun x hx => by
    have h1 : 1 < x := lt_of_lt_of_le ha hx.1
    exact mul_ne_zero (pow_ne_zero 2 (by linarith)) (pow_ne_zero 2 (ne_of_gt (Real.log_pos h1))))

/-- Continuity of `t ↦ (2 log t + 1)/(t ^ 3 (log t) ^ 2)` on `[a,b]`, `1 < a`. -/
lemma caC1_lower_A_continuousOn_h3 {a b : ℝ} (ha : 1 < a) :
    ContinuousOn (fun t : ℝ => (2*Real.log t + 1)/(t^3*(Real.log t)^2)) (Set.Icc a b) := by
  have hlog : ContinuousOn Real.log (Set.Icc a b) :=
    Real.continuousOn_log.mono (fun x hx => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      have : 1 < x := lt_of_lt_of_le ha hx.1
      linarith)
  have hid : ContinuousOn (fun x : ℝ => x) (Set.Icc a b) := continuousOn_id
  have hnum : ContinuousOn (fun x : ℝ => 2*Real.log x + 1) (Set.Icc a b) :=
    (hlog.const_mul 2).add continuousOn_const
  have hden : ContinuousOn (fun x : ℝ => x^3*(Real.log x)^2) (Set.Icc a b) :=
    (hid.pow 3).mul (hlog.pow 2)
  exact hnum.div hden (fun x hx => by
    have h1 : 1 < x := lt_of_lt_of_le ha hx.1
    exact mul_ne_zero (pow_ne_zero 3 (by linarith)) (pow_ne_zero 2 (ne_of_gt (Real.log_pos h1))))

/-! ## The Abel lower bound `abS n z ≤ Σ_{n<p≤z} 1/p²` -/

theorem caC1_lower_A_abS_le (n z : ℕ) (hn : 173 ≤ n) (hn501 : n ≤ 501) (hnz : n ≤ z)
    (hz : z ≤ 100000) (h501 : 501 ≤ z)
    (hθn : Chebyshev.theta (n:ℝ) ≤ (n:ℝ) - (64/100) * Real.sqrt n)
    (hθint : ∀ m : ℕ, n ≤ m → m ≤ 501 → (m:ℝ) - Chebyshev.theta (m:ℝ) ≤ (189/100) * Real.sqrt m)
    (hθz : (96/100) * (z:ℝ) ≤ Chebyshev.theta (z:ℝ))
    (hθh : ∀ t : ℝ, 501 ≤ t → t ≤ (z:ℝ) → t - Chebyshev.theta t ≤ 2.3 * Real.sqrt t) :
    Work.RHContract.A.RegionII.abS n z ≤
      ∑ p ∈ Finset.Ioc n z, if p.Prime then (1:ℝ)/((p:ℝ)^2) else 0 := by
  have hn2 : 2 ≤ n := by omega
  have hnR1 : (1:ℝ) < (n:ℝ) := by
    have : (173:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    linarith
  have hnR : (0:ℝ) < (n:ℝ) := by linarith
  have hnzR : (n:ℝ) ≤ (z:ℝ) := by exact_mod_cast hnz
  have hn501R : (n:ℝ) ≤ 501 := by
    have : (n:ℝ) ≤ (501:ℝ) := by exact_mod_cast hn501
    norm_num at this ⊢
    exact this
  have h501zR : (501:ℝ) ≤ (z:ℝ) := by exact_mod_cast h501
  have hzpos : (0:ℝ) < (z:ℝ) := by linarith
  have hln : (0:ℝ) < Real.log (n:ℝ) := Real.log_pos hnR1
  have hlz : (0:ℝ) < Real.log (z:ℝ) := Real.log_pos (by linarith)
  -- define the kernel
  set K : ℝ → ℝ := fun t => ((2*Real.log t + 1)/(t^3*(Real.log t)^2)) * Chebyshev.theta t with hK
  -- Abel identity
  have habel := Commons.NumberTheory.Chebyshev.sum_prime_inv_sq_abel (n := n) (m := z) hn2 hnz
  -- integrability of `K` on the two pieces
  have hKcont_r : ContinuousOn (fun t : ℝ => (2*Real.log t + 1)/(t^3*(Real.log t)^2))
      (Set.uIcc (n:ℝ) 501) := by
    rw [Set.uIcc_of_le hn501R]
    exact caC1_lower_A_continuousOn_h3 hnR1
  have hKint_low : IntervalIntegrable K volume (n:ℝ) 501 :=
    Chebyshev.theta_mono.intervalIntegrable.continuousOn_mul hKcont_r
  have hKcont_r2 : ContinuousOn (fun t : ℝ => (2*Real.log t + 1)/(t^3*(Real.log t)^2))
      (Set.uIcc (501:ℝ) (z:ℝ)) := by
    rw [Set.uIcc_of_le h501zR]
    exact caC1_lower_A_continuousOn_h3 (by linarith : (1:ℝ) < 501)
  have hKint_high : IntervalIntegrable K volume (501:ℝ) (z:ℝ) :=
    Chebyshev.theta_mono.intervalIntegrable.continuousOn_mul hKcont_r2
  -- split the Abel integral
  have hsplit : (∫ t in Set.Ioc (n:ℝ) (z:ℝ), K t)
      = (∫ t in Set.Ioc (n:ℝ) 501, K t) + (∫ t in Set.Ioc (501:ℝ) (z:ℝ), K t) := by
    rw [← intervalIntegral.integral_of_le hn501R, ← intervalIntegral.integral_of_le h501zR,
        ← intervalIntegral.integral_of_le hnzR]
    exact (intervalIntegral.integral_add_adjacent_intervals hKint_low hKint_high).symm
  -- the boundary term at `z`
  have hbz : (96/100)/((z:ℝ)*Real.log (z:ℝ))
      ≤ (1/((z:ℝ)^2*Real.log (z:ℝ))) * Chebyshev.theta (z:ℝ) := by
    have hcoef : 0 ≤ 1/((z:ℝ)^2*Real.log (z:ℝ)) := by positivity
    have h := mul_le_mul_of_nonneg_left hθz hcoef
    have heq : (1/((z:ℝ)^2*Real.log (z:ℝ))) * ((96/100) * (z:ℝ))
        = (96/100)/((z:ℝ)*Real.log (z:ℝ)) := by
      field_simp
    rw [heq] at h
    exact h
  -- the boundary term at `n`
  have hbn : -(1 - (64/100)/Real.sqrt (n:ℝ))/((n:ℝ)*Real.log (n:ℝ))
      ≤ -((1/((n:ℝ)^2*Real.log (n:ℝ))) * Chebyshev.theta (n:ℝ)) := by
    have hcoef : 0 ≤ 1/((n:ℝ)^2*Real.log (n:ℝ)) := by positivity
    have h := mul_le_mul_of_nonneg_left hθn hcoef
    have hsq : Real.sqrt (n:ℝ) * Real.sqrt (n:ℝ) = (n:ℝ) := Real.mul_self_sqrt (le_of_lt hnR)
    have heq : (1/((n:ℝ)^2*Real.log (n:ℝ))) * ((n:ℝ) - (64/100) * Real.sqrt (n:ℝ))
        = (1 - (64/100)/Real.sqrt (n:ℝ))/((n:ℝ)*Real.log (n:ℝ)) := by
      field_simp
      nlinarith [hsq]
    rw [heq] at h
    simpa only [neg_div] using neg_le_neg h
  -- ## the lower piece: `∫_{n..501} K`
  have hlow : 2 * (1/((n:ℝ)*Real.log (n:ℝ)) - 1/(501*Real.log 501))
        - (1/((n:ℝ)*Real.log (n:ℝ)) - 1/(501*Real.log 501)) / (Real.log (n:ℝ) + 1)
        - ((2 + 1/Real.log (n:ℝ))/Real.log (n:ℝ))/2 * (1/(n:ℝ)^2 - 1/501^2)
        - (189/100) * (((2 + 1/Real.log (n:ℝ))/Real.log (n:ℝ)) * (2/3)
            * (1/((n:ℝ)*Real.sqrt (n:ℝ)) - 1/(501*Real.sqrt 501)))
      ≤ ∫ t in Set.Ioc (n:ℝ) 501, K t := by
    rw [← intervalIntegral.integral_of_le hn501R]
    have hθlow : ∀ t ∈ Set.Icc (n:ℝ) 501, t - Chebyshev.theta t ≤ 1 + (189/100) * Real.sqrt t := by
      intro t ht
      have hm1 : n ≤ ⌊t⌋₊ := Nat.le_floor ht.1
      have hm2 : ⌊t⌋₊ ≤ 501 := by
        have h := Nat.floor_mono (show t ≤ ((501:ℕ):ℝ) from ht.2)
        rwa [Nat.floor_natCast] at h
      have hbase := hθint ⌊t⌋₊ hm1 hm2
      have hfl := caC1_lower_A_theta_eq_theta_floor t
      have hfrac : t - (⌊t⌋₊:ℝ) ≤ 1 := by
        have := Nat.lt_floor_add_one t; linarith
      have hsq : (189/100) * Real.sqrt ((⌊t⌋₊:ℝ)) ≤ (189/100) * Real.sqrt t :=
        mul_le_mul_of_nonneg_left
          (Real.sqrt_le_sqrt (Nat.floor_le (le_trans (le_of_lt hnR) ht.1))) (by norm_num)
      have hsum : (t - (⌊t⌋₊:ℝ)) + ((⌊t⌋₊:ℝ) - Chebyshev.theta ((⌊t⌋₊:ℝ)))
          ≤ 1 + (189/100) * Real.sqrt ((⌊t⌋₊:ℝ)) := add_le_add hfrac hbase
      rw [hfl]
      linarith [hsum, hsq]
    have hpt : ∀ t ∈ Set.Icc (n:ℝ) 501,
        ((2*Real.log t + 1)/(t^3*(Real.log t)^2)) * (t - 1 - (189/100)*Real.sqrt t) ≤ K t := by
      intro t ht
      have ht1 : (1:ℝ) ≤ t := by linarith [ht.1, hnR1]
      have hk := caC1_lower_A_kernel_nonneg ht1
      have hθt : t - Chebyshev.theta t ≤ 1 + (189/100)*Real.sqrt t := hθlow t ht
      have : t - 1 - (189/100)*Real.sqrt t ≤ Chebyshev.theta t := by linarith
      exact mul_le_mul_of_nonneg_left this hk
    have hf_int : IntervalIntegrable
        (fun t : ℝ => ((2*Real.log t + 1)/(t^3*(Real.log t)^2)) * (t - 1 - (189/100)*Real.sqrt t))
        volume (n:ℝ) 501 := by
      apply (ContinuousOn.intervalIntegrable_of_Icc hn501R)
      have h1 := caC1_lower_A_continuousOn_h3 (b := 501) hnR1
      have h2 : ContinuousOn (fun t : ℝ => t - 1 - (189/100)*Real.sqrt t) (Set.Icc (n:ℝ) 501) :=
        ((continuousOn_id.sub continuousOn_const).sub
          (continuousOn_const.mul Real.continuous_sqrt.continuousOn)).mono (by intro x hx; exact hx)
      exact h1.mul h2
    have hmono := intervalIntegral.integral_mono_on hn501R hf_int hKint_low hpt
    have hcongr : (∫ t in (n:ℝ)..501,
          ((2*Real.log t + 1)/(t^3*(Real.log t)^2)) * (t - 1 - (189/100)*Real.sqrt t))
        = ∫ t in (n:ℝ)..501,
            ((2*Real.log t + 1)/(t^2*(Real.log t)^2)
              - (2*Real.log t + 1)/(t^3*(Real.log t)^2)
              - (189/100) * ((2*Real.log t + 1)/(t^3*(Real.log t)^2) * Real.sqrt t)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      field_simp
    rw [hcongr] at hmono
    have hI1 : IntervalIntegrable (fun t : ℝ => (2*Real.log t + 1)/(t^2*(Real.log t)^2))
        volume (n:ℝ) 501 := (caC1_lower_A_continuousOn_h2 hnR1).intervalIntegrable_of_Icc hn501R
    have hI2 : IntervalIntegrable (fun t : ℝ => (2*Real.log t + 1)/(t^3*(Real.log t)^2))
        volume (n:ℝ) 501 := (caC1_lower_A_continuousOn_h3 hnR1).intervalIntegrable_of_Icc hn501R
    have hI3 : IntervalIntegrable
        (fun t : ℝ => (2*Real.log t + 1)/(t^3*(Real.log t)^2) * Real.sqrt t)
        volume (n:ℝ) 501 := by
      apply ContinuousOn.intervalIntegrable_of_Icc hn501R
      exact (caC1_lower_A_continuousOn_h3 hnR1).mul Real.continuous_sqrt.continuousOn
    have hsub1 : IntervalIntegrable
        (fun t : ℝ => (2*Real.log t + 1)/(t^2*(Real.log t)^2)
          - (2*Real.log t + 1)/(t^3*(Real.log t)^2)) volume (n:ℝ) 501 := hI1.sub hI2
    rw [intervalIntegral.integral_sub hsub1 (hI3.const_mul (189/100)),
        intervalIntegral.integral_sub hI1 hI2, intervalIntegral.integral_const_mul] at hmono
    have hA := abel_ht_lower (a := (n:ℝ)) (b := 501) hnR1 hn501R
    have hB := abel_h_upper (a := (n:ℝ)) (b := 501) hnR1 hn501R
    have hC := abel_hsqrt_upper (a := (n:ℝ)) (b := 501) hnR1 hn501R
    linarith [hmono, hA, hB, hC]

  -- ## the upper piece: `∫_{501..z} K`
  have hhigh : 2 * (1/(501*Real.log 501) - 1/((z:ℝ)*Real.log (z:ℝ)))
        - (1/(501*Real.log 501) - 1/((z:ℝ)*Real.log (z:ℝ))) / (Real.log 501 + 1)
        - (23/10) * (((2 + 1/Real.log 501)/Real.log 501) * (2/3)
            * (1/(501*Real.sqrt 501) - 1/((z:ℝ)*Real.sqrt (z:ℝ))))
      ≤ ∫ t in Set.Ioc (501:ℝ) (z:ℝ), K t := by
    rw [← intervalIntegral.integral_of_le h501zR]
    have hpt : ∀ t ∈ Set.Icc (501:ℝ) (z:ℝ),
        ((2*Real.log t + 1)/(t^3*(Real.log t)^2)) * (t - (23/10)*Real.sqrt t) ≤ K t := by
      intro t ht
      have ht1 : (1:ℝ) ≤ t := by linarith [ht.1]
      have hk := caC1_lower_A_kernel_nonneg ht1
      have hθt : t - Chebyshev.theta t ≤ 2.3 * Real.sqrt t := hθh t ht.1 ht.2
      have : t - (23/10)*Real.sqrt t ≤ Chebyshev.theta t := by linarith
      exact mul_le_mul_of_nonneg_left this hk
    have hf_int : IntervalIntegrable
        (fun t : ℝ => ((2*Real.log t + 1)/(t^3*(Real.log t)^2)) * (t - (23/10)*Real.sqrt t))
        volume (501:ℝ) (z:ℝ) := by
      apply ContinuousOn.intervalIntegrable_of_Icc h501zR
      have h1 := caC1_lower_A_continuousOn_h3 (a := (501:ℝ)) (b := (z:ℝ)) (by norm_num)
      have h2 : ContinuousOn (fun t : ℝ => t - (23/10)*Real.sqrt t) (Set.Icc (501:ℝ) (z:ℝ)) :=
        (continuousOn_id.sub (continuousOn_const.mul Real.continuous_sqrt.continuousOn))
      exact h1.mul h2
    have hmono := intervalIntegral.integral_mono_on h501zR hf_int hKint_high hpt
    have hcongr : (∫ t in (501:ℝ)..(z:ℝ),
          ((2*Real.log t + 1)/(t^3*(Real.log t)^2)) * (t - (23/10)*Real.sqrt t))
        = ∫ t in (501:ℝ)..(z:ℝ),
            ((2*Real.log t + 1)/(t^2*(Real.log t)^2)
              - (23/10) * ((2*Real.log t + 1)/(t^3*(Real.log t)^2) * Real.sqrt t)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      field_simp
    rw [hcongr] at hmono
    have hI1 : IntervalIntegrable (fun t : ℝ => (2*Real.log t + 1)/(t^2*(Real.log t)^2))
        volume (501:ℝ) (z:ℝ) :=
      (caC1_lower_A_continuousOn_h2 (a := (501:ℝ)) (b := (z:ℝ)) (by norm_num)).intervalIntegrable_of_Icc h501zR
    have hI3 : IntervalIntegrable
        (fun t : ℝ => (2*Real.log t + 1)/(t^3*(Real.log t)^2) * Real.sqrt t)
        volume (501:ℝ) (z:ℝ) := by
      apply ContinuousOn.intervalIntegrable_of_Icc h501zR
      exact (caC1_lower_A_continuousOn_h3 (a := (501:ℝ)) (b := (z:ℝ)) (by norm_num)).mul
        Real.continuous_sqrt.continuousOn
    rw [intervalIntegral.integral_sub hI1 (hI3.const_mul (23/10)),
        intervalIntegral.integral_const_mul] at hmono
    have hA := abel_ht_lower (a := (501:ℝ)) (b := (z:ℝ)) (by norm_num) h501zR
    have hC := abel_hsqrt_upper (a := (501:ℝ)) (b := (z:ℝ)) (by norm_num) h501zR
    linarith [hmono, hA, hC]

  -- ## assembly
  have hdJ : Work.RHContract.A.RegionII.abJ z
      = (96/100)/((z:ℝ)*Real.log (z:ℝ))
        + (2 * (1/(501*Real.log 501) - 1/((z:ℝ)*Real.log (z:ℝ)))
           - (1/(501*Real.log 501) - 1/((z:ℝ)*Real.log (z:ℝ))) / (Real.log 501 + 1)
           - (23/10) * (((2 + 1/Real.log 501)/Real.log 501) * (2/3)
               * (1/(501*Real.sqrt 501) - 1/((z:ℝ)*Real.sqrt (z:ℝ))))) := by
    unfold Work.RHContract.A.RegionII.abJ Work.RHContract.A.RegionII.uAb
      Work.RHContract.A.RegionII.chAb
    ring
  have hdA : Work.RHContract.A.RegionII.abA n
      = -(-(1 - (64/100)/Real.sqrt (n:ℝ))/((n:ℝ)*Real.log (n:ℝ))
        + (2 * (1/((n:ℝ)*Real.log (n:ℝ)) - 1/(501*Real.log 501))
           - (1/((n:ℝ)*Real.log (n:ℝ)) - 1/(501*Real.log 501)) / (Real.log (n:ℝ) + 1)
           - ((2 + 1/Real.log (n:ℝ))/Real.log (n:ℝ))/2 * (1/(n:ℝ)^2 - 1/501^2)
           - (189/100) * (((2 + 1/Real.log (n:ℝ))/Real.log (n:ℝ)) * (2/3)
               * (1/((n:ℝ)*Real.sqrt (n:ℝ)) - 1/(501*Real.sqrt 501))))) := by
    unfold Work.RHContract.A.RegionII.abA Work.RHContract.A.RegionII.uAb
      Work.RHContract.A.RegionII.chAb
    ring
  have hdef : Work.RHContract.A.RegionII.abS n z
      = Work.RHContract.A.RegionII.abJ z - Work.RHContract.A.RegionII.abA n := rfl
  rw [hdef, habel, hdJ, hdA, hsplit]
  linarith [hbz, hbn, hlow, hhigh]

/-! ## The target lemma -/

/-- Per-prime comparison: for `p ≥ 173`, `(498/1000)/p² ≤ 1/(2p²) − 1/(3p³)`. -/
lemma caC1_lower_A_c1ge (p : ℕ) (hp : 173 ≤ p) :
    (498/1000 : ℝ) * (1/(p:ℝ)^2) ≤ 1/(2*(p:ℝ)^2) - 1/(3*(p:ℝ)^3) := by
  have hpR : (173:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
  have hx : (0:ℝ) < (p:ℝ) := by linarith
  rw [show (1:ℝ)/(2*(p:ℝ)^2) - 1/(3*(p:ℝ)^3) = (3*(p:ℝ)-2)/(6*(p:ℝ)^3) by
    field_simp; ring]
  rw [le_div_iff₀ (by positivity)]
  field_simp
  nlinarith [hpR]

/-- `1/(2p²) − 1/(3p³) ≥ 0` for every `p ≥ 2`. -/
lemma caC1_lower_A_c1nonneg (p : ℕ) (hp : 2 ≤ p) :
    (0:ℝ) ≤ 1/(2*(p:ℝ)^2) - 1/(3*(p:ℝ)^3) := by
  have hpR : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
  have hx : (0:ℝ) < (p:ℝ) := by linarith
  rw [show (1:ℝ)/(2*(p:ℝ)^2) - 1/(3*(p:ℝ)^3) = (3*(p:ℝ)-2)/(6*(p:ℝ)^3) by
    field_simp; ring]
  exact div_nonneg (by linarith) (by positivity)

theorem caC1_lower_A (ε : ℝ) (hε : 0 < ε)
    (hlo : 30000 ≤ (Work.RHPlan.caXi ε : ℝ)) (hhi : (Work.RHPlan.caXi ε : ℝ) < 100000)
    (hθ : ∀ t : ℝ, 173 ≤ t → t ≤ 100000 → t - Chebyshev.theta t ≤ 2.3 * Real.sqrt t) :
    (498/1000) * Work.RHContract.A.RegionII.abS
        (max (Work.RHContract.Margin.caXi2 ε) 173) (Work.RHPlan.caXi ε)
      ≤ Work.RHContract.Margin.caC1 ε := by
  set ξ : ℕ := Work.RHPlan.caXi ε with hξdef
  set n : ℕ := max (Work.RHContract.Margin.caXi2 ε) 173 with hndef
  have hξge : (30000:ℝ) ≤ (ξ:ℝ) := by rw [hξdef]; exact hlo
  have hξlt : (ξ:ℝ) < 100000 := by rw [hξdef]; exact hhi
  have hξ30000 : 30000 ≤ ξ := by exact_mod_cast hξge
  have hξ100000 : ξ ≤ 100000 := by
    have : ξ < 100000 := by exact_mod_cast hξlt
    omega
  have hξ1530 : 1530 ≤ (Work.RHPlan.caXi ε : ℝ) := by rw [← hξdef]; linarith
  have hcaXi2le : Work.RHContract.Margin.caXi2 ε ≤ n := by
    rw [hndef]; exact le_max_left _ _
  have hn173 : 173 ≤ n := by rw [hndef]; exact le_max_right _ _
  have h501 : 501 ≤ ξ := by omega
  -- `ξ₂(ε) ≤ 500`, hence `n ≤ 501`
  have hcaXi2_500 : Work.RHContract.Margin.caXi2 ε ≤ 500 := by
    have hbase := Work.RHContract.A.caXi2_le_sqrt ε hε hξ1530
    have hs : Real.sqrt (2.5 * (ξ:ℝ)) < 500 := by
      rw [Real.sqrt_lt' (by norm_num : (0:ℝ) < 500)]
      nlinarith [hξlt]
    have hlt : (Work.RHContract.Margin.caXi2 ε : ℝ) < 501 := by linarith
    have hlt' : Work.RHContract.Margin.caXi2 ε < 501 := by exact_mod_cast hlt
    omega
  have hn501 : n ≤ 501 := by rw [hndef]; omega
  have hnz : n ≤ ξ := by omega
  -- the `θ`-bracket inputs of the Abel bound
  have hd := theta_deficit_cert_173_501
  have hθn : Chebyshev.theta (n:ℝ) ≤ (n:ℝ) - (64/100) * Real.sqrt n := by
    have := hd.1 n hn173 hn501
    linarith
  have hθint : ∀ m : ℕ, n ≤ m → m ≤ 501 →
      (m:ℝ) - Chebyshev.theta (m:ℝ) ≤ (189/100) * Real.sqrt m := by
    intro m h1 h2
    exact hd.2 m (by omega) (by omega)
  have hθz : (96/100) * (ξ:ℝ) ≤ Chebyshev.theta (ξ:ℝ) := by
    have h := (Commons.NumberTheory.Chebyshev.theta_bracket_finite_range ξ
      (by omega) hξ100000).1
    rw [if_neg (by omega : ¬ ξ ≤ 100), if_neg (by omega : ¬ ξ ≤ 150),
        if_neg (by omega : ¬ ξ ≤ 250), if_neg (by omega : ¬ ξ ≤ 400),
        if_neg (by omega : ¬ ξ ≤ 700), if_neg (by omega : ¬ ξ ≤ 1100),
        if_neg (by omega : ¬ ξ ≤ 1530)] at h
    exact h
  have hθh : ∀ t : ℝ, 501 ≤ t → t ≤ (ξ:ℝ) → t - Chebyshev.theta t ≤ 2.3 * Real.sqrt t := by
    intro t h1 h2
    refine hθ t (by linarith) ?_
    have hle : (ξ:ℝ) ≤ 100000 := by exact_mod_cast hξ100000
    linarith
  -- Abel lower bound
  have hAB := caC1_lower_A_abS_le n ξ hn173 hn501 hnz hξ100000 h501 hθn hθint hθz hθh
  -- identify the prime-indicator sum with a sum over a filtered `primesLE`
  have hfinset : (Finset.Ioc n ξ).filter Nat.Prime
      = (Nat.primesLE ξ).filter (fun q => n < q) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h2, h3⟩, h1⟩
    · rintro ⟨⟨h2, h3⟩, h1⟩; exact ⟨⟨h1, h2⟩, h3⟩
  have heq : (∑ p ∈ Finset.Ioc n ξ, (if p.Prime then (1:ℝ)/((p:ℝ)^2) else 0))
      = ∑ p ∈ (Nat.primesLE ξ).filter (fun q => n < q), (1:ℝ)/((p:ℝ)^2) := by
    rw [← Finset.sum_filter, hfinset]
  -- the per-prime comparison, summed
  have hstep2 : (498/1000) * (∑ p ∈ (Nat.primesLE ξ).filter (fun q => n < q),
        (1:ℝ)/((p:ℝ)^2))
      ≤ ∑ p ∈ (Nat.primesLE ξ).filter (fun q => n < q),
          (1/(2*(p:ℝ)^2) - 1/(3*(p:ℝ)^3)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun p hp => ?_)
    have hp173 : 173 ≤ p := by
      rw [Finset.mem_filter] at hp
      omega
    exact caC1_lower_A_c1ge p hp173
  -- enlarge the range
  have hsub : (Nat.primesLE ξ).filter (fun q => n < q)
      ⊆ (Nat.primesLE ξ).filter (fun q => Work.RHContract.Margin.caXi2 ε < q) := by
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, lt_of_le_of_lt hcaXi2le hp.2⟩
  have hstep3 : (∑ p ∈ (Nat.primesLE ξ).filter (fun q => n < q),
        (1/(2*(p:ℝ)^2) - 1/(3*(p:ℝ)^3)))
      ≤ ∑ p ∈ (Nat.primesLE ξ).filter (fun q => Work.RHContract.Margin.caXi2 ε < q),
          (1/(2*(p:ℝ)^2) - 1/(3*(p:ℝ)^3)) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => ?_)
    have hp' : p ∈ Nat.primesLE ξ := (Finset.mem_filter.mp hp).1
    exact caC1_lower_A_c1nonneg p (Nat.mem_primesLE.mp hp').2.two_le
  have hC1eq : Work.RHContract.Margin.caC1 ε
      = ∑ p ∈ (Nat.primesLE ξ).filter (fun q => Work.RHContract.Margin.caXi2 ε < q),
          (1/(2*(p:ℝ)^2) - 1/(3*(p:ℝ)^3)) := by
    unfold Work.RHContract.Margin.caC1
    rw [← hξdef, Nat.floor_natCast]
  calc (498/1000) * Work.RHContract.A.RegionII.abS n ξ
      ≤ (498/1000) * (∑ p ∈ Finset.Ioc n ξ,
          (if p.Prime then (1:ℝ)/((p:ℝ)^2) else 0)) :=
        mul_le_mul_of_nonneg_left hAB (by norm_num)
    _ = (498/1000) * (∑ p ∈ (Nat.primesLE ξ).filter (fun q => n < q),
          (1:ℝ)/((p:ℝ)^2)) := by rw [heq]
    _ ≤ ∑ p ∈ (Nat.primesLE ξ).filter (fun q => n < q),
          (1/(2*(p:ℝ)^2) - 1/(3*(p:ℝ)^3)) := hstep2
    _ ≤ ∑ p ∈ (Nat.primesLE ξ).filter (fun q => Work.RHContract.Margin.caXi2 ε < q),
          (1/(2*(p:ℝ)^2) - 1/(3*(p:ℝ)^3)) := hstep3
    _ = Work.RHContract.Margin.caC1 ε := hC1eq.symm

end Work.RHContract.A.regionII
