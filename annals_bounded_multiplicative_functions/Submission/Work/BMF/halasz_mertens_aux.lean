import Mathlib
import Submission.Work.BMF.halasz_defs
import Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound
import Submission.Work.BMF.mertens.exp_neg_div_bounds
import Submission.Work.BMF.mertens.primeRpow_filter_sub
import Submission.Work.BMF.mertens.primeRpow_small_shift
import Submission.Work.BMF.mertens.loglog_rpow_telescope
import Submission.Work.BMF.mertens.primeRpow_abel

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators
open Finset Real MeasureTheory



namespace Work.BMF

/-- The prime indicator sequence `p ↦ 1/p`. -/
noncomputable def primC : ℕ → ℝ := Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => (1 : ℝ) / (n : ℝ))

lemma Zrcp_eq_indicator_sum (x : ℝ) :
    (∑ k ∈ Icc 0 ⌊x⌋₊, Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => (1 : ℝ) / (n : ℝ)) k) =
      Zrcp x := by
  unfold Zrcp
  rw [Nat.primesLE_eq_filter_Icc_zero]
  rw [sum_filter]
  congr 1
  ext k
  by_cases h : k.Prime
  · simp [h]
  · simp [h]

lemma Zrcp_eq_sum_primC (x : ℝ) : Zrcp x = ∑ k ∈ Icc 0 ⌊x⌋₊, primC k := by
  rw [← Zrcp_eq_indicator_sum x]
  rfl

lemma Zrcp_nonneg (t : ℝ) : 0 ≤ Zrcp t := by
  unfold Zrcp
  exact Finset.sum_nonneg (fun p _ => div_nonneg zero_le_one (Nat.cast_nonneg p))

lemma integrableOn_rpow_mul_Zrcp {a b ε : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t ^ (-(1 + ε)) * Zrcp t) (Set.Icc a b) := by
  have hfun : (fun t : ℝ => t ^ (-(1 + ε)) * Zrcp t)
      = fun t : ℝ => t ^ (-(1 + ε)) * (∑ k ∈ Icc 0 ⌊t⌋₊, primC k) := by
    funext t
    rw [Zrcp_eq_sum_primC]
  rw [hfun]
  refine integrableOn_mul_sum_Icc (c := primC) (m := 0) ha.le ?_
  refine ContinuousOn.integrableOn_Icc ?_
  intro z hz
  have hz0 : z ≠ 0 := by linarith [hz.1]
  exact (Real.continuousAt_rpow_const z (-(1 + ε)) (Or.inl hz0)).continuousWithinAt

lemma intervalIntegrable_rpow_mul_Zrcp {a b ε : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => t ^ (-(1 + ε)) * Zrcp t) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  exact integrableOn_rpow_mul_Zrcp ha

/-- `ε ∫_y^x t^{-1-ε} dt = y^{-ε} - x^{-ε}`. -/
lemma eps_mul_integral_rpow (y x ε : ℝ) (hy : 0 < y) (hyx : y ≤ x) (hε : 0 < ε) :
    ε * ∫ t in y..x, t ^ (-(1 + ε)) = y ^ (-ε) - x ^ (-ε) := by
  have hx : 0 < x := lt_of_lt_of_le hy hyx
  have hr : (-(1 + ε)) ≠ (-1 : ℝ) := by
    intro h
    have : ε = 0 := by linarith
    exact absurd this (ne_of_gt hε)
  rw [integral_rpow (Or.inr ⟨hr, by
    rw [Set.uIcc_of_le hyx]
    exact fun h => absurd h.1 (not_le.mpr hy)⟩)]
  have h1 : -(1 + ε) + 1 = -ε := by ring
  rw [h1]
  have hyne : y ^ (-ε) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hy _)
  have hxne : x ^ (-ε) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hx _)
  field_simp
  ring

end Work.BMF


namespace Work.BMF

/-- Integral bound for `ε ∫ t^{-1-ε} Z(t)`: the core estimate for primes in `(y,x]`. -/
theorem sum_rpow_le_integral (C₀ y x ε : ℝ) (hC₀ : 0 ≤ C₀) (hy : 11 ≤ y) (hyx : y ≤ x)
    (hε : 0 < ε) (hZ : ∀ t : ℝ, 11 ≤ t → |Zrcp t - Real.log (Real.log t)| ≤ C₀) :
    (∑ p ∈ ((⌊x⌋₊).primesLE.filter (fun p : ℕ => y < (p : ℝ))), (1 : ℝ) / (p : ℝ) ^ (1 + ε)) ≤
      (∫ v in (ε * Real.log y)..(ε * Real.log x), Real.exp (-v) / v) + 2 * C₀ := by
  have hy2 : 2 ≤ y := by linarith
  have hx2 : 2 ≤ x := by linarith
  have hypos : 0 < y := by linarith
  have hxpos : 0 < x := by linarith
  have e1 : (∑ p ∈ (⌊x⌋₊).primesLE, (1 : ℝ) / (p : ℝ) ^ (1 + ε))
      = x ^ (-ε) * Zrcp x + ε * (∫ t in (2:ℝ)..x, t ^ (-(1 + ε)) * Zrcp t) := by
    simpa only [Zrcp] using Work.BMF.mertens.primeRpow_abel (x := x) (ε := ε) hx2 hε
  have e2 : (∑ p ∈ (⌊y⌋₊).primesLE, (1 : ℝ) / (p : ℝ) ^ (1 + ε))
      = y ^ (-ε) * Zrcp y + ε * (∫ t in (2:ℝ)..y, t ^ (-(1 + ε)) * Zrcp t) := by
    simpa only [Zrcp] using Work.BMF.mertens.primeRpow_abel (x := y) (ε := ε) hy2 hε
  have h4 := Work.BMF.mertens.primeRpow_filter_sub (x := x) (y := y) (ε := ε) hyx
  have hI2y : IntervalIntegrable (fun t : ℝ => t ^ (-(1 + ε)) * Zrcp t) volume (2:ℝ) y :=
    intervalIntegrable_rpow_mul_Zrcp (by norm_num) hy2
  have hIyx : IntervalIntegrable (fun t : ℝ => t ^ (-(1 + ε)) * Zrcp t) volume y x :=
    intervalIntegrable_rpow_mul_Zrcp hypos hyx
  have hsplit : (∫ t in (2:ℝ)..y, t ^ (-(1 + ε)) * Zrcp t)
      + (∫ t in y..x, t ^ (-(1 + ε)) * Zrcp t)
      = ∫ t in (2:ℝ)..x, t ^ (-(1 + ε)) * Zrcp t :=
    intervalIntegral.integral_add_adjacent_intervals hI2y hIyx
  have hD : (∑ p ∈ ((⌊x⌋₊).primesLE.filter (fun p : ℕ => y < (p : ℝ))),
        (1 : ℝ) / (p : ℝ) ^ (1 + ε))
      = x ^ (-ε) * Zrcp x - y ^ (-ε) * Zrcp y
        + ε * (∫ t in y..x, t ^ (-(1 + ε)) * Zrcp t) := by
    rw [h4, e1, e2, ← hsplit]
    ring
  -- integrability of the comparison integrands
  have hIcont : IntervalIntegrable
      (fun t : ℝ => t ^ (-(1 + ε)) * (Real.log (Real.log t) + C₀)) volume y x := by
    refine ContinuousOn.intervalIntegrable_of_Icc hyx ?_
    intro t ht
    have htpos : 0 < t := by linarith [ht.1]
    have htne : t ≠ 0 := ne_of_gt htpos
    have hlogne : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith [ht.1]))
    exact (((Real.continuousAt_rpow_const t (-(1 + ε)) (Or.inl htne)).mul
      (((Real.continuousAt_log htne).log hlogne).add_const C₀))).continuousWithinAt
  have hMono : ε * (∫ t in y..x, t ^ (-(1 + ε)) * Zrcp t)
      ≤ ε * (∫ t in y..x, t ^ (-(1 + ε)) * (Real.log (Real.log t) + C₀)) := by
    have hmono := intervalIntegral.integral_mono_on hyx hIyx hIcont (fun t ht => ?_)
    · nlinarith [hmono, hε]
    · have ht11 : 11 ≤ t := le_trans hy ht.1
      have htpos : 0 < t := by linarith
      have hpow : 0 ≤ t ^ (-(1 + ε)) := Real.rpow_nonneg htpos.le _
      have hb : Zrcp t - Real.log (Real.log t) ≤ C₀ := (abs_le.mp (hZ t ht11)).2
      exact mul_le_mul_of_nonneg_left (by linarith) hpow
  have hIloglog : IntervalIntegrable
      (fun t : ℝ => t ^ (-(1 + ε)) * Real.log (Real.log t)) volume y x := by
    refine ContinuousOn.intervalIntegrable_of_Icc hyx ?_
    intro t ht
    have htpos : 0 < t := by linarith [ht.1]
    have htne : t ≠ 0 := ne_of_gt htpos
    have hlogne : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith [ht.1]))
    exact (((Real.continuousAt_rpow_const t (-(1 + ε)) (Or.inl htne)).mul
      ((Real.continuousAt_log htne).log hlogne))).continuousWithinAt
  have hIpow : IntervalIntegrable (fun t : ℝ => t ^ (-(1 + ε))) volume y x := by
    refine ContinuousOn.intervalIntegrable_of_Icc hyx ?_
    intro t ht
    have htpos : 0 < t := by linarith [ht.1]
    have htne : t ≠ 0 := ne_of_gt htpos
    exact (Real.continuousAt_rpow_const t (-(1 + ε)) (Or.inl htne)).continuousWithinAt
  have hLin : ε * (∫ t in y..x, t ^ (-(1 + ε)) * (Real.log (Real.log t) + C₀))
      = ε * (∫ t in y..x, t ^ (-(1 + ε)) * Real.log (Real.log t))
        + C₀ * (ε * (∫ t in y..x, t ^ (-(1 + ε)))) := by
    rw [show (fun t : ℝ => t ^ (-(1 + ε)) * (Real.log (Real.log t) + C₀))
        = (fun t : ℝ => t ^ (-(1 + ε)) * Real.log (Real.log t) + C₀ * t ^ (-(1 + ε))) by
      funext t; ring]
    rw [intervalIntegral.integral_add hIloglog (hIpow.const_mul C₀)]
    rw [intervalIntegral.integral_const_mul]
    ring
  have hTel := Work.BMF.mertens.loglog_rpow_telescope y x ε (by linarith) hyx hε
  have hTel2 : ε * (∫ t in y..x, t ^ (-(1 + ε)) * Real.log (Real.log t))
      = Real.log (Real.log y) / y ^ ε - Real.log (Real.log x) / x ^ ε
        + (∫ v in (ε * Real.log y)..(ε * Real.log x), Real.exp (-v) / v) := by
    rw [← hTel]
    congr 1
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    have htpos : 0 < t := by
      rw [Set.uIcc_of_le hyx] at ht
      linarith [ht.1]
    rw [Real.rpow_neg htpos.le]
    ring
  have hPow := eps_mul_integral_rpow y x ε hypos hyx hε
  have hZx : Zrcp x ≤ Real.log (Real.log x) + C₀ := by
    have h := (abs_le.mp (hZ x (le_trans hy hyx))).2; linarith
  have hZy : Real.log (Real.log y) - C₀ ≤ Zrcp y := by
    have h := (abs_le.mp (hZ y hy)).1; linarith
  have h1 : x ^ (-ε) * Zrcp x ≤ x ^ (-ε) * (Real.log (Real.log x) + C₀) :=
    mul_le_mul_of_nonneg_left hZx (Real.rpow_nonneg hxpos.le _)
  have h2 : -y ^ (-ε) * Zrcp y ≤ -y ^ (-ε) * (Real.log (Real.log y) - C₀) := by
    have hh : y ^ (-ε) * (Real.log (Real.log y) - C₀) ≤ y ^ (-ε) * Zrcp y :=
      mul_le_mul_of_nonneg_left hZy (Real.rpow_nonneg hypos.le _)
    linarith
  have hye : y ^ (-ε) ≤ 1 := by
    simpa using (Real.rpow_le_rpow_of_nonpos (x := (1:ℝ)) (y := y) (z := -ε)
      zero_lt_one (by linarith) (by linarith))
  have hxpr : x ^ (-ε) * Real.log (Real.log x) = Real.log (Real.log x) / x ^ ε := by
    rw [Real.rpow_neg hxpos.le]; ring
  have hypr : y ^ (-ε) * Real.log (Real.log y) = Real.log (Real.log y) / y ^ ε := by
    rw [Real.rpow_neg hypos.le]; ring
  have hA : x ^ (-ε) * Zrcp x - y ^ (-ε) * Zrcp y
        + (ε * (∫ t in y..x, t ^ (-(1 + ε)) * Real.log (Real.log t))
            + C₀ * (ε * (∫ t in y..x, t ^ (-(1 + ε)))))
      ≤ x ^ (-ε) * (Real.log (Real.log x) + C₀) - y ^ (-ε) * (Real.log (Real.log y) - C₀)
        + (Real.log (Real.log y) / y ^ ε - Real.log (Real.log x) / x ^ ε
            + (∫ v in (ε * Real.log y)..(ε * Real.log x), Real.exp (-v) / v))
        + C₀ * (y ^ (-ε) - x ^ (-ε)) := by
    rw [hTel2, hPow]
    linarith [h1, h2]
  have hB : x ^ (-ε) * (Real.log (Real.log x) + C₀) - y ^ (-ε) * (Real.log (Real.log y) - C₀)
        + (Real.log (Real.log y) / y ^ ε - Real.log (Real.log x) / x ^ ε
            + (∫ v in (ε * Real.log y)..(ε * Real.log x), Real.exp (-v) / v))
        + C₀ * (y ^ (-ε) - x ^ (-ε))
      ≤ (∫ v in (ε * Real.log y)..(ε * Real.log x), Real.exp (-v) / v) + 2 * C₀ := by
    have hxx : x ^ (-ε) * (Real.log (Real.log x) + C₀)
        = Real.log (Real.log x) / x ^ ε + C₀ * x ^ (-ε) := by rw [mul_add, hxpr]; ring
    have hyy : y ^ (-ε) * (Real.log (Real.log y) - C₀)
        = Real.log (Real.log y) / y ^ ε - C₀ * y ^ (-ε) := by rw [mul_sub, hypr]; ring
    rw [hxx, hyy]
    nlinarith [hye, hC₀]
  calc (∑ p ∈ ((⌊x⌋₊).primesLE.filter (fun p : ℕ => y < (p : ℝ))),
          (1 : ℝ) / (p : ℝ) ^ (1 + ε))
      = x ^ (-ε) * Zrcp x - y ^ (-ε) * Zrcp y
        + ε * (∫ t in y..x, t ^ (-(1 + ε)) * Zrcp t) := hD
    _ ≤ x ^ (-ε) * Zrcp x - y ^ (-ε) * Zrcp y
        + ε * (∫ t in y..x, t ^ (-(1 + ε)) * (Real.log (Real.log t) + C₀)) := by
          linarith [hMono]
    _ = x ^ (-ε) * Zrcp x - y ^ (-ε) * Zrcp y
        + (ε * (∫ t in y..x, t ^ (-(1 + ε)) * Real.log (Real.log t))
            + C₀ * (ε * (∫ t in y..x, t ^ (-(1 + ε))))) := by rw [hLin]
    _ ≤ _ := hA
    _ ≤ _ := hB

end Work.BMF

namespace Work.BMF

/-- Reduction of the Halász crossover sum `Σ_{p ≤ x} (1 - p^{-ε})/p` to the integral
`∫_{ε log 11}^{ε log x} e^{-v}/v`. -/
theorem halasz_sum_bound (C₀ x ε : ℝ) (hC₀ : 0 ≤ C₀) (hx : 11 ≤ x) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hZ : ∀ t : ℝ, 11 ≤ t → |Zrcp t - Real.log (Real.log t)| ≤ C₀) :
    (∑ p ∈ (⌊x⌋₊).primesLE, (1 - (p : ℝ) ^ (-ε)) / p) ≤
      Real.log (Real.log x)
        - (∫ v in (ε * Real.log 11)..(ε * Real.log x), Real.exp (-v) / v) + 2 * C₀ := by
  have hxpos : 0 < x := by linarith
  have hx2 : 2 ≤ x := by linarith
  -- termwise identity
  have hterm : ∀ p ∈ (⌊x⌋₊).primesLE,
      (1 - (p : ℝ) ^ (-ε)) / p = (1 : ℝ) / p - 1 / (p : ℝ) ^ (1 + ε) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Nat.Prime.two_le (Nat.mem_primesLE.mp hp).2)
    have hp0 : (0 : ℝ) < p := by linarith
    have hq : (p : ℝ) ^ (-ε) = ((p : ℝ) ^ ε)⁻¹ := Real.rpow_neg hp0.le ε
    have hq' : (p : ℝ) ^ (1 + ε) = (p : ℝ) * (p : ℝ) ^ ε := by
      rw [Real.rpow_add hp0, Real.rpow_one]
    have hpne : (p : ℝ) ≠ 0 := ne_of_gt hp0
    have hpe : (p : ℝ) ^ ε ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hp0 ε)
    rw [hq, hq']
    field_simp
  have hA' : (∑ p ∈ (⌊x⌋₊).primesLE, (1 - (p : ℝ) ^ (-ε)) / p)
      = Zrcp x - (∑ p ∈ (⌊x⌋₊).primesLE, (1 : ℝ) / (p : ℝ) ^ (1 + ε)) := by
    have h1 : (∑ p ∈ (⌊x⌋₊).primesLE, (1 - (p : ℝ) ^ (-ε)) / p)
        = ∑ p ∈ (⌊x⌋₊).primesLE, ((1 : ℝ) / p - 1 / (p : ℝ) ^ (1 + ε)) :=
      Finset.sum_congr rfl hterm
    rw [h1, Finset.sum_sub_distrib]
    simp only [Zrcp]
  -- Abel identity
  have e1 : (∑ p ∈ (⌊x⌋₊).primesLE, (1 : ℝ) / (p : ℝ) ^ (1 + ε))
      = x ^ (-ε) * Zrcp x + ε * (∫ t in (2:ℝ)..x, t ^ (-(1 + ε)) * Zrcp t) := by
    simpa only [Zrcp] using Work.BMF.mertens.primeRpow_abel (x := x) (ε := ε) hx2 hε
  have hI211 : IntervalIntegrable (fun t : ℝ => t ^ (-(1 + ε)) * Zrcp t) volume (2:ℝ) 11 :=
    intervalIntegrable_rpow_mul_Zrcp (by norm_num) (by norm_num)
  have hI11x : IntervalIntegrable (fun t : ℝ => t ^ (-(1 + ε)) * Zrcp t) volume 11 x :=
    intervalIntegrable_rpow_mul_Zrcp (by norm_num) (by linarith)
  have hsplit : (∫ t in (2:ℝ)..11, t ^ (-(1 + ε)) * Zrcp t)
      + (∫ t in 11..x, t ^ (-(1 + ε)) * Zrcp t)
      = ∫ t in (2:ℝ)..x, t ^ (-(1 + ε)) * Zrcp t :=
    intervalIntegral.integral_add_adjacent_intervals hI211 hI11x
  have hAeq : (∑ p ∈ (⌊x⌋₊).primesLE, (1 - (p : ℝ) ^ (-ε)) / p)
      = Zrcp x - x ^ (-ε) * Zrcp x
        - ε * (∫ t in (2:ℝ)..11, t ^ (-(1 + ε)) * Zrcp t)
        - ε * (∫ t in 11..x, t ^ (-(1 + ε)) * Zrcp t) := by
    rw [hA', e1, ← hsplit]
    ring
  -- the [2,11] part is nonnegative
  have hnn : 0 ≤ ε * (∫ t in (2:ℝ)..11, t ^ (-(1 + ε)) * Zrcp t) := by
    have h0 : 0 ≤ ∫ t in (2:ℝ)..11, t ^ (-(1 + ε)) * Zrcp t := by
      refine intervalIntegral.integral_nonneg (by norm_num) (fun u hu => ?_)
      exact mul_nonneg (Real.rpow_nonneg (by linarith [hu.1]) _) (Zrcp_nonneg u)
    nlinarith [h0, hε]
  -- lower bound for the [11,x] part
  have hIcont : IntervalIntegrable
      (fun t : ℝ => t ^ (-(1 + ε)) * (Real.log (Real.log t) - C₀)) volume 11 x := by
    refine ContinuousOn.intervalIntegrable_of_Icc (by linarith) ?_
    intro t ht
    have htpos : 0 < t := by linarith [ht.1]
    have htne : t ≠ 0 := ne_of_gt htpos
    have hlogne : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith [ht.1]))
    exact (((Real.continuousAt_rpow_const t (-(1 + ε)) (Or.inl htne)).mul
      (((Real.continuousAt_log htne).log hlogne).sub_const C₀))).continuousWithinAt
  have hlow : ε * (∫ t in 11..x, t ^ (-(1 + ε)) * (Real.log (Real.log t) - C₀))
      ≤ ε * (∫ t in 11..x, t ^ (-(1 + ε)) * Zrcp t) := by
    have hmono := intervalIntegral.integral_mono_on (by linarith : (11:ℝ) ≤ x) hIcont hI11x
      (fun t ht => ?_)
    · nlinarith [hmono, hε]
    · have ht11 : 11 ≤ t := ht.1
      have htpos : 0 < t := by linarith
      have hpow : 0 ≤ t ^ (-(1 + ε)) := Real.rpow_nonneg htpos.le _
      have hb : Real.log (Real.log t) - C₀ ≤ Zrcp t := by
        have h := (abs_le.mp (hZ t ht11)).1; linarith
      exact mul_le_mul_of_nonneg_left hb hpow
  have hIloglog : IntervalIntegrable
      (fun t : ℝ => t ^ (-(1 + ε)) * Real.log (Real.log t)) volume 11 x := by
    refine ContinuousOn.intervalIntegrable_of_Icc (by linarith) ?_
    intro t ht
    have htpos : 0 < t := by linarith [ht.1]
    have htne : t ≠ 0 := ne_of_gt htpos
    have hlogne : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith [ht.1]))
    exact (((Real.continuousAt_rpow_const t (-(1 + ε)) (Or.inl htne)).mul
      ((Real.continuousAt_log htne).log hlogne))).continuousWithinAt
  have hIpow : IntervalIntegrable (fun t : ℝ => t ^ (-(1 + ε))) volume 11 x := by
    refine ContinuousOn.intervalIntegrable_of_Icc (by linarith) ?_
    intro t ht
    have htpos : 0 < t := by linarith [ht.1]
    have htne : t ≠ 0 := ne_of_gt htpos
    exact (Real.continuousAt_rpow_const t (-(1 + ε)) (Or.inl htne)).continuousWithinAt
  have hLin : ε * (∫ t in 11..x, t ^ (-(1 + ε)) * (Real.log (Real.log t) - C₀))
      = ε * (∫ t in 11..x, t ^ (-(1 + ε)) * Real.log (Real.log t))
        - C₀ * (ε * (∫ t in 11..x, t ^ (-(1 + ε)))) := by
    rw [show (fun t : ℝ => t ^ (-(1 + ε)) * (Real.log (Real.log t) - C₀))
        = (fun t : ℝ => t ^ (-(1 + ε)) * Real.log (Real.log t) - C₀ * t ^ (-(1 + ε))) by
      funext t; ring]
    rw [intervalIntegral.integral_sub hIloglog (hIpow.const_mul C₀)]
    rw [intervalIntegral.integral_const_mul]
    ring
  have hTel := Work.BMF.mertens.loglog_rpow_telescope 11 x ε (by norm_num) (by linarith) hε
  have hTel2 : ε * (∫ t in 11..x, t ^ (-(1 + ε)) * Real.log (Real.log t))
      = Real.log (Real.log 11) / 11 ^ ε - Real.log (Real.log x) / x ^ ε
        + (∫ v in (ε * Real.log 11)..(ε * Real.log x), Real.exp (-v) / v) := by
    rw [← hTel]
    congr 1
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    have htpos : 0 < t := by
      rw [Set.uIcc_of_le (by linarith : (11:ℝ) ≤ x)] at ht
      linarith [ht.1]
    rw [Real.rpow_neg htpos.le]
    ring
  have hPow := eps_mul_integral_rpow 11 x ε (by norm_num) (by linarith) hε
  have hZx : Zrcp x ≤ Real.log (Real.log x) + C₀ := by
    have h := (abs_le.mp (hZ x hx)).2; linarith
  have hZx2 : Real.log (Real.log x) - C₀ ≤ Zrcp x := by
    have h := (abs_le.mp (hZ x hx)).1; linarith
  have hxexp : x ^ (-ε) ≤ 1 := by
    simpa using (Real.rpow_le_rpow_of_nonpos (x := (1:ℝ)) (y := x) (z := -ε)
      zero_lt_one (by linarith) (by linarith))
  have h11exp : (11:ℝ) ^ (-ε) ≤ 1 := by
    simpa using (Real.rpow_le_rpow_of_nonpos (x := (1:ℝ)) (y := 11) (z := -ε)
      zero_lt_one (by norm_num) (by linarith))
  have hll11 : 0 ≤ Real.log (Real.log 11) := by
    have hexp : Real.exp 1 ≤ 11 := by
      have := Real.exp_one_lt_three; linarith
    have hlog11 : (1:ℝ) ≤ Real.log 11 := by
      have h := Real.log_le_log (Real.exp_pos 1) hexp
      rwa [Real.log_exp] at h
    exact Real.log_nonneg hlog11
  have hxpr : x ^ (-ε) * Real.log (Real.log x) = Real.log (Real.log x) / x ^ ε := by
    rw [Real.rpow_neg hxpos.le]; ring
  have hstep2 : Zrcp x - x ^ (-ε) * Zrcp x
        - ε * (∫ t in (2:ℝ)..11, t ^ (-(1 + ε)) * Zrcp t)
        - ε * (∫ t in 11..x, t ^ (-(1 + ε)) * Zrcp t)
      ≤ (Real.log (Real.log x) + C₀) - x ^ (-ε) * (Real.log (Real.log x) - C₀) - 0
        - ε * (∫ t in 11..x, t ^ (-(1 + ε)) * (Real.log (Real.log t) - C₀)) := by
    have hx2' : -x ^ (-ε) * Zrcp x ≤ -x ^ (-ε) * (Real.log (Real.log x) - C₀) := by
      have hh : x ^ (-ε) * (Real.log (Real.log x) - C₀) ≤ x ^ (-ε) * Zrcp x :=
        mul_le_mul_of_nonneg_left hZx2 (Real.rpow_nonneg hxpos.le _)
      linarith
    linarith [hZx, hx2', hnn, hlow]
  have hE : (Real.log (Real.log x) + C₀) - x ^ (-ε) * (Real.log (Real.log x) - C₀) - 0
        - ε * (∫ t in 11..x, t ^ (-(1 + ε)) * (Real.log (Real.log t) - C₀))
      = Real.log (Real.log x)
        - (∫ v in (ε * Real.log 11)..(ε * Real.log x), Real.exp (-v) / v)
        + (C₀ + C₀ * 11 ^ (-ε) - Real.log (Real.log 11) / 11 ^ ε) := by
    have hxx : x ^ (-ε) * (Real.log (Real.log x) - C₀)
        = Real.log (Real.log x) / x ^ ε - C₀ * x ^ (-ε) := by
      rw [mul_sub, hxpr]; ring
    rw [hLin, hTel2, hPow, hxx]
    ring
  have hfin : Real.log (Real.log x)
        - (∫ v in (ε * Real.log 11)..(ε * Real.log x), Real.exp (-v) / v)
        + (C₀ + C₀ * 11 ^ (-ε) - Real.log (Real.log 11) / 11 ^ ε)
      ≤ Real.log (Real.log x)
        - (∫ v in (ε * Real.log 11)..(ε * Real.log x), Real.exp (-v) / v) + 2 * C₀ := by
    have h3 : 0 ≤ Real.log (Real.log 11) / 11 ^ ε :=
      div_nonneg hll11 (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
    nlinarith [h11exp, hC₀, h3]
  calc (∑ p ∈ (⌊x⌋₊).primesLE, (1 - (p : ℝ) ^ (-ε)) / p)
      = Zrcp x - x ^ (-ε) * Zrcp x
        - ε * (∫ t in (2:ℝ)..11, t ^ (-(1 + ε)) * Zrcp t)
        - ε * (∫ t in 11..x, t ^ (-(1 + ε)) * Zrcp t) := hAeq
    _ ≤ (Real.log (Real.log x) + C₀) - x ^ (-ε) * (Real.log (Real.log x) - C₀) - 0
        - ε * (∫ t in 11..x, t ^ (-(1 + ε)) * (Real.log (Real.log t) - C₀)) := hstep2
    _ = Real.log (Real.log x)
        - (∫ v in (ε * Real.log 11)..(ε * Real.log x), Real.exp (-v) / v)
        + (C₀ + C₀ * 11 ^ (-ε) - Real.log (Real.log 11) / 11 ^ ε) := hE
    _ ≤ Real.log (Real.log x)
        - (∫ v in (ε * Real.log 11)..(ε * Real.log x), Real.exp (-v) / v) + 2 * C₀ := hfin

end Work.BMF

namespace Work.BMF

theorem halasz_mertens_aux :
    (∃ C : ℝ, 0 < C ∧ ∀ x y : ℝ, 11 ≤ y → y ≤ x →
        Work.BMF.Zrcp x - Work.BMF.Zrcp y ≤ Real.log (Real.log x / Real.log y) + C) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ ε x : ℝ, 0 < ε → ε ≤ 1 → 11 ≤ x → 1 / Real.log x ≤ ε →
        (∑ p ∈ (⌊x⌋₊).primesLE, (1 - (p : ℝ) ^ (-ε)) / p) ≤ Real.log (ε * Real.log x) + C) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ ε y x : ℝ, 0 < ε → ε ≤ 1 → 2 < y → 11 ≤ x → 1 ≤ ε * Real.log y →
        (∑ p ∈ ((⌊x⌋₊).primesLE.filter (fun p : ℕ => y < (p : ℝ))), (1 : ℝ) / (p : ℝ) ^ (1 + ε)) ≤ C) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound
  have hZ : ∀ t : ℝ, 11 ≤ t → |Zrcp t - Real.log (Real.log t)| ≤ C₀ := by
    intro t ht
    simpa only [Zrcp] using hC₀ t ht
  have hlog11pos : 0 < Real.log 11 := Real.log_pos (by norm_num)
  have hll11le : Real.log (Real.log 11) ≤ 2 := by
    have hexp3 : Real.exp 3 = Real.exp 1 ^ 3 := by
      have := Real.exp_nat_mul 1 3
      simpa using this
    have he1 : (2.7 : ℝ) < Real.exp 1 := by
      have := Real.exp_one_gt_d9
      linarith
    have h11 : (11 : ℝ) < Real.exp 3 := by
      rw [hexp3]
      have h1 : (2.7 : ℝ) ^ 3 < Real.exp 1 ^ 3 := pow_lt_pow_left₀ he1 (by norm_num) (by norm_num)
      have h2 : (11 : ℝ) < (2.7 : ℝ) ^ 3 := by norm_num
      linarith
    have hlog11le3 : Real.log 11 ≤ 3 := by
      have h := Real.log_le_log (by norm_num : (0:ℝ) < 11) (le_of_lt h11)
      rwa [Real.log_exp] at h
    have hlog3 : Real.log 3 ≤ 2 := by
      have hexp2 : (3 : ℝ) ≤ Real.exp 2 := by
        have he : Real.exp 2 = Real.exp 1 ^ 2 := by
          have := Real.exp_nat_mul 1 2
          simpa using this
        rw [he]
        have h1 : (2.7 : ℝ) ^ 2 < Real.exp 1 ^ 2 := pow_lt_pow_left₀ he1 (by norm_num) (by norm_num)
        have h2 : (3 : ℝ) < (2.7 : ℝ) ^ 2 := by norm_num
        linarith
      have h := Real.log_le_log (by norm_num : (0:ℝ) < 3) hexp2
      rwa [Real.log_exp] at h
    have h := Real.log_le_log hlog11pos hlog11le3
    linarith
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨2 * C₀ + 1, by linarith, ?_⟩
    intro x y hy hyx
    have hx11 : 11 ≤ x := le_trans hy hyx
    have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
    have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
    have h1 : Zrcp x - Real.log (Real.log x) ≤ C₀ := (abs_le.mp (hZ x hx11)).2
    have h2 : Real.log (Real.log y) - Zrcp y ≤ C₀ := by
      have h := (abs_le.mp (hZ y hy)).1
      linarith
    have h3 : Real.log (Real.log x) - Real.log (Real.log y)
        = Real.log (Real.log x / Real.log y) := by
      rw [Real.log_div (ne_of_gt hlogx) (ne_of_gt hlogy)]
    linarith
  · refine ⟨2 * C₀ + 4, by linarith, ?_⟩
    intro ε x hε hε1 hx hεx
    have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
    have hεx' : 1 ≤ ε * Real.log x := (div_le_iff₀ hlogx).mp hεx
    have hδU : ε * Real.log 11 ≤ ε * Real.log x :=
      mul_le_mul_of_nonneg_left (Real.log_le_log (by norm_num) hx) (le_of_lt hε)
    have hmain := halasz_sum_bound C₀ x ε (le_of_lt hC₀pos) hx hε hε1 hZ
    have hlogid : Real.log (ε * Real.log x) = Real.log (Real.log x) - Real.log (1 / ε) := by
      rw [Real.log_mul (ne_of_gt hε) (ne_of_gt hlogx), one_div, Real.log_inv]
      ring
    have hδpos : 0 < ε * Real.log 11 := by positivity
    rcases le_or_gt (ε * Real.log 11) 1 with hδ | hδ
    · have hint := Work.BMF.mertens.exp_neg_div_bounds.2.1 (ε * Real.log 11) (ε * Real.log x) hδpos hδ hεx'
      have hlogd : Real.log (1 / (ε * Real.log 11))
          = Real.log (1 / ε) - Real.log (Real.log 11) := by
        have hEq : 1 / (ε * Real.log 11) = (1 / ε) / Real.log 11 := by
          field_simp
        rw [hEq, Real.log_div (by positivity) (ne_of_gt hlog11pos)]
      rw [hlogd] at hint
      rw [hlogid]
      linarith
    · have hδone : 1 ≤ ε * Real.log 11 := le_of_lt hδ
      have hint : 0 ≤ (∫ v in (ε * Real.log 11)..(ε * Real.log x), Real.exp (-v) / v) :=
        Work.BMF.mertens.exp_neg_div_bounds.2.2 (ε * Real.log 11) (ε * Real.log x) hδone hδU
      have hlogle : Real.log (1 / ε) ≤ 4 := by
        have h1e : 1 / ε ≤ Real.log 11 := by
          rw [div_le_iff₀ hε]
          linarith [hδone]
        have h2 : Real.log (1 / ε) ≤ Real.log (Real.log 11) :=
          Real.log_le_log (by positivity) h1e
        linarith
      rw [hlogid]
      linarith
  · refine ⟨2 * C₀ + 3, by linarith, ?_⟩
    intro ε y x hε hε1 hy2 hx hεy
    by_cases hyx : y ≤ x
    · by_cases hy11 : 11 ≤ y
      · have hδU : ε * Real.log y ≤ ε * Real.log x :=
          mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) hyx) (le_of_lt hε)
        have hδpos : 0 < ε * Real.log y := by
          have h := Real.log_pos (by linarith : (1:ℝ) < y)
          positivity
        have hb := sum_rpow_le_integral C₀ y x ε (le_of_lt hC₀pos) hy11 hyx hε hZ
        have hint := Work.BMF.mertens.exp_neg_div_bounds.1 (ε * Real.log y) (ε * Real.log x) hδpos hδU
        have hle : Real.exp (-(ε * Real.log y)) / (ε * Real.log y) ≤ 1 := by
          rw [div_le_one hδpos]
          have h1 : Real.exp (-(ε * Real.log y)) ≤ 1 := by
            have h := Real.exp_le_exp.mpr (show -(ε * Real.log y) ≤ 0 by linarith)
            simpa using h
          linarith [hεy]
        linarith
      · push_neg at hy11
        have hε11 : 1 ≤ ε * Real.log 11 := by
          have hlogy11 : Real.log y ≤ Real.log 11 := Real.log_le_log (by linarith) (le_of_lt hy11)
          have := mul_le_mul_of_nonneg_left hlogy11 (le_of_lt hε)
          linarith
        have hδU : ε * Real.log 11 ≤ ε * Real.log x :=
          mul_le_mul_of_nonneg_left (Real.log_le_log (by norm_num) hx) (le_of_lt hε)
        have hδpos : 0 < ε * Real.log 11 := by positivity
        have hb5 := Work.BMF.mertens.primeRpow_small_shift (y := y) (x := x) (ε := ε)
          hy2 hy11 hx hε
        have hb6 := sum_rpow_le_integral C₀ 11 x ε (le_of_lt hC₀pos) le_rfl hx hε hZ
        have hint := Work.BMF.mertens.exp_neg_div_bounds.1 (ε * Real.log 11) (ε * Real.log x) hδpos hδU
        have hle : Real.exp (-(ε * Real.log 11)) / (ε * Real.log 11) ≤ 1 := by
          rw [div_le_one hδpos]
          have h1 : Real.exp (-(ε * Real.log 11)) ≤ 1 := by
            have h := Real.exp_le_exp.mpr (show -(ε * Real.log 11) ≤ 0 by linarith)
            simpa using h
          linarith [hε11]
        linarith
    · push_neg at hyx
      have hempty : ((⌊x⌋₊).primesLE.filter (fun p : ℕ => y < (p : ℝ))) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro p hp
        rw [Nat.mem_primesLE] at hp
        have hpx : (p : ℝ) ≤ x := by
          have h1 : (p : ℝ) ≤ ((⌊x⌋₊ : ℕ) : ℝ) := Nat.cast_le.mpr hp.1
          have h2 : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le (by linarith)
          exact le_trans h1 h2
        exact not_lt.mpr (le_trans hpx (le_of_lt hyx))
      rw [hempty, Finset.sum_empty]
      linarith [hC₀pos]

end Work.BMF
