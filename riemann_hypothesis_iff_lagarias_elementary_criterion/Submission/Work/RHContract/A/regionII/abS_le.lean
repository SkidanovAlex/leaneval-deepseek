import Mathlib
import Submission.Work.RHContract.A.regionII.abdefs
import Submission.Work.RHContract.Corpus
import Submission.Work.RHContract.A.regionII.ab_piece
import Submission.Work.RHContract.A.regionII.ab_theta_lower

open MeasureTheory
open scoped BigOperators

namespace Work.RHContract.A.regionII

/-- Continuity of the Abel kernel `h t = (2 log t + 1)/(t³ log²t)` on `[a,b]` for `1 < a`. -/
private lemma hcont_h {a b : ℝ} (ha : 1 < a) :
    ContinuousOn (fun t : ℝ => (2 * Real.log t + 1) / (t ^ 3 * (Real.log t) ^ 2)) (Set.Icc a b) := by
  have hlog : ContinuousOn Real.log (Set.Icc a b) :=
    Real.continuousOn_log.mono (fun x hx => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      have h1 : 1 < x := lt_of_lt_of_le ha hx.1
      linarith)
  have hid : ContinuousOn (fun x : ℝ => x) (Set.Icc a b) := continuousOn_id
  have hnum : ContinuousOn (fun x : ℝ => 2 * Real.log x + 1) (Set.Icc a b) :=
    (hlog.const_mul 2).add continuousOn_const
  exact hnum.div ((hid.pow 3).mul (hlog.pow 2)) (fun x hx => by
    have h1 : 1 < x := lt_of_lt_of_le ha hx.1
    exact mul_ne_zero (pow_ne_zero 3 (by linarith)) (pow_ne_zero 2 (ne_of_gt (Real.log_pos h1))))

/-- The `θ`-weighted Abel integrand is interval integrable. -/
private lemma intervalIntegrable_F {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => ((2 * Real.log t + 1) / (t ^ 3 * (Real.log t) ^ 2)) * Chebyshev.theta t)
      volume a b := by
  refine Chebyshev.theta_mono.intervalIntegrable.continuousOn_mul ?_
  rw [Set.uIcc_of_le hab]
  exact hcont_h ha

/-- **Region II Abel lower bound.** For integers `173 ≤ n ≤ 501 ≤ z ≤ 10^5` the explicit
bound `abS n z` below-approximates `∑_{n < p ≤ z, p prime} 1/p²`.

The Abel identity `∑ 1/p² = θ z/(z² log z) − θ n/(n² log n) + ∫_n^z h·θ` with
`h t = (2 log t + 1)/(t³ log²t)` is combined with the four certified `θ`-bounds
(`θ z ≥ (96/100) z`, `θ n ≤ n − (64/100)√n`, `θ m ≥ m − (189/100)√m` at integers
`m ∈ [n,501]`, and `θ t ≥ t − 2.3√t` on `[501,z]`), the floor reduction
`θ t ≥ (t−1) − (189/100)√t` on `[n,501]`, and the kernel estimates packaged in
`ab_piece`. -/
theorem abS_le (n z : ℕ) (hn : 173 ≤ n) (hn501 : n ≤ 501) (hnz : n ≤ z) (hz : z ≤ 100000) (h501 : 501 ≤ z)
    (hθn : Chebyshev.theta (n:ℝ) ≤ (n:ℝ) - (64/100) * Real.sqrt n)
    (hθint : ∀ m : ℕ, n ≤ m → m ≤ 501 → (m:ℝ) - Chebyshev.theta (m:ℝ) ≤ (189/100) * Real.sqrt m)
    (hθz : (96/100) * (z:ℝ) ≤ Chebyshev.theta (z:ℝ))
    (hθh : ∀ t : ℝ, 501 ≤ t → t ≤ z → t - Chebyshev.theta t ≤ 2.3 * Real.sqrt t) :
    Work.RHContract.A.RegionII.abS n z ≤
      ∑ p ∈ Finset.Ioc n z, if p.Prime then (1:ℝ)/((p:ℝ)^2) else 0 := by
  have hn2 : 2 ≤ n := by omega
  have hn1R : (1:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hz1R : (1:ℝ) < (z:ℝ) := by exact_mod_cast (by omega : 1 < z)
  have hnzR : (n:ℝ) ≤ (z:ℝ) := by exact_mod_cast hnz
  have h501R : (501:ℝ) ≤ (z:ℝ) := by exact_mod_cast h501
  have hn501R : (n:ℝ) ≤ 501 := by exact_mod_cast hn501
  have hn2R : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn2
  have hln : 0 < Real.log (n:ℝ) := Real.log_pos hn1R
  have hlz : 0 < Real.log (z:ℝ) := Real.log_pos hz1R
  -- Abel summation
  rw [Commons.NumberTheory.Chebyshev.sum_prime_inv_sq_abel hn2 hnz]
  rw [← intervalIntegral.integral_of_le hnzR]
  have hF1 : IntervalIntegrable (fun t : ℝ => ((2 * Real.log t + 1) / (t ^ 3 * (Real.log t) ^ 2)) * Chebyshev.theta t)
      volume (n:ℝ) 501 := intervalIntegrable_F hn1R hn501R
  have hF2 : IntervalIntegrable (fun t : ℝ => ((2 * Real.log t + 1) / (t ^ 3 * (Real.log t) ^ 2)) * Chebyshev.theta t)
      volume 501 (z:ℝ) := intervalIntegrable_F (by norm_num) h501R
  rw [← intervalIntegral.integral_add_adjacent_intervals hF1 hF2]
  -- the two `θ`-lower bounds
  have hθlow1 : ∀ t ∈ Set.Icc (n:ℝ) 501, 1 * t - 1 - (189/100) * Real.sqrt t ≤ Chebyshev.theta t := by
    intro t ht
    have h := ab_theta_lower n hθint t ht.1 ht.2
    linarith
  have hθlow2 : ∀ t ∈ Set.Icc (501:ℝ) (z:ℝ), 1 * t - 0 - (23/10) * Real.sqrt t ≤ Chebyshev.theta t := by
    intro t ht
    have h := hθh t ht.1 ht.2
    have h23 : ((23:ℝ)/10) = 2.3 := by norm_num
    rw [h23]
    linarith
  have hI1 := ab_piece (a := (n:ℝ)) (b := 501) (c := 1) (d := 1) (e := 189/100)
    hn2R hn501R (by norm_num) (by norm_num) (by norm_num) hθlow1
  have hI2 := ab_piece (a := 501) (b := (z:ℝ)) (c := 1) (d := 0) (e := 23/10)
    (by norm_num) h501R (by norm_num) (by norm_num) (by norm_num) hθlow2
  -- the two boundary terms
  have hz_bound : (96/100)/((z:ℝ) * Real.log z) ≤ (1/((z:ℝ)^2 * Real.log z)) * Chebyshev.theta (z:ℝ) := by
    have hden : 0 < (z:ℝ)^2 * Real.log z := by positivity
    have h1 := mul_le_mul_of_nonneg_left hθz (le_of_lt (div_pos one_pos hden))
    have heq : (1/((z:ℝ)^2 * Real.log z)) * ((96/100) * (z:ℝ)) = (96/100)/((z:ℝ) * Real.log z) := by
      field_simp
    rw [heq] at h1
    exact h1
  have hn_bound : -((1 - (64/100)/Real.sqrt n)/((n:ℝ) * Real.log n)) ≤
      -((1/((n:ℝ)^2 * Real.log n)) * Chebyshev.theta (n:ℝ)) := by
    have hden : 0 < (n:ℝ)^2 * Real.log n := by positivity
    have h1 := mul_le_mul_of_nonneg_left hθn (le_of_lt (div_pos one_pos hden))
    have heq : (1/((n:ℝ)^2 * Real.log n)) * ((n:ℝ) - (64/100) * Real.sqrt n)
        = (1 - (64/100)/Real.sqrt n)/((n:ℝ) * Real.log n) := by
      field_simp
      nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ (n:ℝ) by positivity)]
    rw [heq] at h1
    linarith
  -- assemble
  unfold Work.RHContract.A.RegionII.abS Work.RHContract.A.RegionII.abJ Work.RHContract.A.RegionII.abA
  linarith [hz_bound, hn_bound, hI1, hI2]

end Work.RHContract.A.regionII
