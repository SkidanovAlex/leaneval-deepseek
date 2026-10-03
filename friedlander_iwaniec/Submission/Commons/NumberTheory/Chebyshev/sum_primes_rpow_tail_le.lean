import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.Chebyshev

namespace Commons.NumberTheory.Chebyshev

open Finset

/-! ## Helper lemmas for `sum_primes_rpow_tail_le`

We prove the Chebyshev-type tail bound
`∑_{Δ ≤ p ≤ Y} p^{-(1+ε)} ≤ 32 / (ε log Δ)`
by summation by parts against the prime counting function together with the
explicit Chebyshev bound `π(n) ≤ 5 n / log n`. -/

private lemma Ioc_sub_one_eq_Icc {a b : ℕ} (ha : 1 ≤ a) :
    Finset.Ioc (a - 1) b = Finset.Icc a b := by
  ext x; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega

/-- Explicit Chebyshev upper bound for the prime counting function. -/
private lemma primesLE_card_le_five (n : ℕ) (hn : 2 ≤ n) :
    ((Nat.primesLE n).card : ℝ) ≤ 5 * (n : ℝ) / Real.log (n : ℝ) := by
  have hn' : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hx1 : (1:ℝ) < (n:ℝ) := by linarith
  have hlogx : Real.log (n:ℝ) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by positivity) (by linarith)
  have hpi := Chebyshev.pi_le_log4_mul_div (x := (n:ℝ)) hx1
  have hlog4 : Real.log 4 ≤ (3:ℝ)/2 := by
    have h4 : Real.log (4:ℝ) = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
    rw [h4]; nlinarith [Real.log_two_lt_d9]
  have hsqrt : Real.sqrt (n:ℝ) ≤ 2 * (n:ℝ) / Real.log (n:ℝ) := by
    rw [le_div_iff₀ (Real.log_pos hx1)]
    have hlog_le : Real.log (n:ℝ) ≤ 2 * Real.sqrt (n:ℝ) := by
      have h := Real.log_le_rpow_div (by positivity : (0:ℝ) ≤ (n:ℝ)) (by norm_num : (0:ℝ) < 1/2)
      calc Real.log (n:ℝ) ≤ (n:ℝ) ^ (1/2:ℝ) / (1/2:ℝ) := h
        _ = 2 * Real.sqrt (n:ℝ) := by rw [← Real.sqrt_eq_rpow]; ring
    calc Real.sqrt (n:ℝ) * Real.log (n:ℝ)
        ≤ Real.sqrt (n:ℝ) * (2 * Real.sqrt (n:ℝ)) :=
          mul_le_mul_of_nonneg_left hlog_le (Real.sqrt_nonneg _)
      _ = 2 * (Real.sqrt (n:ℝ) * Real.sqrt (n:ℝ)) := by ring
      _ = 2 * (n:ℝ) := by rw [Real.mul_self_sqrt (by positivity : (0:ℝ) ≤ (n:ℝ))]
  calc ((Nat.primesLE n).card : ℝ) = (Nat.primeCounting n : ℝ) := by
        rw [Nat.primesLE_card_eq_primeCounting]
    _ = (Nat.primeCounting ⌊(n:ℝ)⌋₊ : ℝ) := by rw [Nat.floor_natCast]
    _ ≤ Real.log 4 * (n:ℝ) / Real.log (Real.sqrt (n:ℝ)) + Real.sqrt (n:ℝ) := hpi
    _ = (2 * Real.log 4) * (n:ℝ) / Real.log (n:ℝ) + Real.sqrt (n:ℝ) := by
        rw [Real.log_sqrt (by positivity : (0:ℝ) ≤ (n:ℝ))]; field_simp
    _ ≤ (2 * Real.log 4) * (n:ℝ) / Real.log (n:ℝ) + 2 * (n:ℝ)/Real.log (n:ℝ) := by
        linarith
    _ = ((2 * Real.log 4 + 2) * (n:ℝ)) / Real.log (n:ℝ) := by
        rw [← add_div]; ring_nf
    _ ≤ 5 * (n:ℝ) / Real.log (n:ℝ) := by
        apply div_le_div_of_nonneg_right _ (Real.log_pos hx1).le
        nlinarith [hlog4, show (0:ℝ) ≤ (n:ℝ) by positivity]

/-- `∑_{i < m+1} [i prime]` is the number of primes `≤ m`. -/
private lemma sum_range_prime_indicator (m : ℕ) :
    (∑ i ∈ Finset.range (m+1), (if i.Prime then (1:ℝ) else 0))
      = ((Nat.primesLE m).card : ℝ) := by
  rw [← Finset.sum_filter, ← Nat.primesLE_eq_filter_range]
  simp

/-- Bernoulli-type bound: `(1+u)^{-α} ≥ 1 - α u` (tangent line at `1`). -/
private lemma one_sub_rpow_neg_one_add_le {u α : ℝ} (hα : 1 ≤ α) (hu0 : 0 ≤ u) :
    1 - (1 + u) ^ (-α) ≤ α * u := by
  have h1u : 0 < 1 + u := by linarith
  have hs : (-1 : ℝ) ≤ -(u / (1 + u)) := by
    have h : u / (1 + u) ≤ 1 := by rw [div_le_one h1u]; linarith
    linarith
  have hb := one_add_mul_self_le_rpow_one_add (s := -(u / (1 + u))) hs (p := α) hα
  have hsimp : 1 + -(u / (1 + u)) = 1 / (1 + u) := by field_simp; ring
  rw [hsimp] at hb
  have hrec : (1 / (1 + u)) ^ α = (1 + u) ^ (-α) := by
    rw [one_div, Real.inv_rpow h1u.le, Real.rpow_neg h1u.le]
  rw [hrec] at hb
  have hu_div : u / (1 + u) ≤ u := by
    rw [div_le_iff₀ h1u]; nlinarith
  nlinarith [hb, hu_div, hα]

/-- Tangent-line inequality for `t ↦ t^{-α}`: `t^{-α} - (t+1)^{-α} ≤ α t^{-(α+1)}`. -/
private lemma rpow_neg_sub_succ_le {α : ℝ} (hα : 1 ≤ α) {t : ℝ} (ht : 1 ≤ t) :
    t ^ (-α) - (t + 1) ^ (-α) ≤ α * t ^ (-(α + 1)) := by
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  have h1t0 : 0 < 1 + 1 / t := by positivity
  have hkey := one_sub_rpow_neg_one_add_le (u := 1 / t) (α := α) hα (div_nonneg zero_le_one ht0.le)
  have hfac : t * (1 + 1 / t) = t + 1 := by field_simp
  rw [← hfac, Real.mul_rpow ht0.le h1t0.le]
  have hpowa : (0:ℝ) ≤ t ^ (-α) := Real.rpow_nonneg ht0.le _
  have step : t ^ (-α) - t ^ (-α) * (1 + 1 / t) ^ (-α)
      = t ^ (-α) * (1 - (1 + 1 / t) ^ (-α)) := by ring
  rw [step]
  calc t ^ (-α) * (1 - (1 + 1 / t) ^ (-α))
      ≤ t ^ (-α) * (α * (1 / t)) := mul_le_mul_of_nonneg_left hkey hpowa
    _ = α * t ^ (-(α + 1)) := by
        have hdiv : t ^ (-α) * t⁻¹ = t ^ (-(α + 1)) := by
          rw [← Real.rpow_neg_one, ← Real.rpow_add ht0]
          congr 1
          ring
        have h1 : t ^ (-α) * (α * (1/t)) = α * (t ^ (-α) * t⁻¹) := by
          rw [one_div]; ring
        rw [h1, hdiv]

/-- The step-1 inequality in the `ε`, `n` form. -/
private lemma rpow_neg_diff_le {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 1 ≤ n) :
    (n:ℝ)^(-(1+ε)) - ((n+1:ℕ):ℝ)^(-(1+ε)) ≤ (1+ε) * (n:ℝ)^(-(2+ε)) := by
  have ht : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have h := rpow_neg_sub_succ_le (α := 1+ε) (by linarith) (t := (n:ℝ)) ht
  have hcast : ((n+1:ℕ):ℝ) = (n:ℝ) + 1 := by push_cast; ring
  have hexp : -((1 + ε) + 1) = -(2 + ε) := by ring
  rw [hcast, ← hexp]
  exact h

/-- The tangent-line bound for the "step-2" inequality:
`(1-u)^{-ε} ≥ 1 + ε u` for `0 < ε ≤ 1`, `0 ≤ u < 1`. -/
private lemma one_add_mul_le_rpow_neg {ε u : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hu0 : 0 ≤ u) (hu1 : u < 1) :
    1 + ε * u ≤ (1 - u) ^ (-ε) := by
  have h1u : 0 < 1 - u := by linarith
  have hb := rpow_one_add_le_one_add_mul_self (s := -u) (by linarith : (-1:ℝ) ≤ -u)
    (p := ε) hε0.le hε1
  have hb' : (1 - u) ^ ε ≤ 1 - ε * u := by
    rw [show (1:ℝ) + -u = 1 - u by ring] at hb
    nlinarith [hb]
  have hpos : 0 < (1 - u) ^ ε := Real.rpow_pos_of_pos h1u ε
  have h1 : (1 + ε * u) * (1 - u) ^ ε ≤ 1 := by
    have h2 : (1 + ε * u) * (1 - u) ^ ε ≤ (1 + ε*u) * (1 - ε*u) :=
      mul_le_mul_of_nonneg_left hb' (by nlinarith [hε0, hu0] : (0:ℝ) ≤ 1 + ε*u)
    nlinarith [h2, sq_nonneg (ε*u)]
  have h3 : (1 + ε * u) ≤ 1 / (1 - u) ^ ε := (le_div_iff₀ hpos).mpr h1
  have h4 : 1 / (1 - u) ^ ε = (1 - u) ^ (-ε) := by
    rw [one_div, Real.rpow_neg h1u.le]
  rwa [h4] at h3

/-- The telescoping step-2 inequality: `n^{-(1+ε)} ≤ ε⁻¹((n-1)^{-ε} - n^{-ε})`. -/
private lemma rpow_neg_le_telescope_le {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {n : ℕ}
    (hn : 2 ≤ n) :
    (n:ℝ)^(-(1+ε)) ≤ (1/ε) * (((n-1:ℕ):ℝ)^(-ε) - (n:ℝ)^(-ε)) := by
  have hn1 : (1:ℕ) ≤ n := le_trans (by norm_num) hn
  have hnR : (0:ℝ) < (n:ℝ) := by positivity
  have hnR1 : (1:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hcast : (((n-1:ℕ)):ℝ) = (n:ℝ) - 1 := by
    rw [Nat.cast_sub hn1]; norm_num
  have hu0 : 0 ≤ 1/(n:ℝ) := by positivity
  have hu1 : 1/(n:ℝ) < 1 := by rw [div_lt_one hnR]; exact_mod_cast (by omega : 1 < n)
  have hkey := one_add_mul_le_rpow_neg (ε := ε) (u := 1/(n:ℝ)) hε0 hε1 hu0 hu1
  have hfac : (n:ℝ) * (1 - 1/(n:ℝ)) = (n:ℝ) - 1 := by field_simp
  have h1mn : 0 ≤ 1 - 1/(n:ℝ) := by
    rw [sub_nonneg, div_le_one hnR]; exact_mod_cast le_of_lt (by omega : 1 < n)
  have hrewrite : (((n-1:ℕ)):ℝ)^(-ε) = (n:ℝ)^(-ε) * (1 - 1/(n:ℝ))^(-ε) := by
    rw [hcast, ← hfac, Real.mul_rpow (by positivity : (0:ℝ) ≤ (n:ℝ)) h1mn]
  have hdiff : (((n-1:ℕ)):ℝ)^(-ε) - (n:ℝ)^(-ε)
      = (n:ℝ)^(-ε) * ((1 - 1/(n:ℝ))^(-ε) - 1) := by rw [hrewrite]; ring
  have hstep1 : (n:ℝ)^(-ε) * (1/(n:ℝ)) = (n:ℝ)^(-(1+ε)) := by
    rw [one_div, ← Real.rpow_neg_one, ← Real.rpow_add hnR]
    congr 1; ring
  have heq : ε * (n:ℝ)^(-(1+ε)) = (n:ℝ)^(-ε) * (ε * (1/(n:ℝ))) := by
    rw [show (n:ℝ)^(-ε) * (ε * (1/(n:ℝ))) = ε * ((n:ℝ)^(-ε) * (1/(n:ℝ))) by ring, hstep1]
  have hge : ε * (n:ℝ)^(-(1+ε)) ≤ (((n-1:ℕ)):ℝ)^(-ε) - (n:ℝ)^(-ε) := by
    rw [hdiff, heq]
    exact mul_le_mul_of_nonneg_left (by linarith [hkey]) (Real.rpow_nonneg hnR.le _)
  calc (n:ℝ)^(-(1+ε)) = (1/ε) * (ε * (n:ℝ)^(-(1+ε))) := by field_simp
    _ ≤ (1/ε) * ((((n-1:ℕ)):ℝ)^(-ε) - (n:ℝ)^(-ε)) :=
        mul_le_mul_of_nonneg_left hge (by positivity)

/-- Telescoping identity `∑_{n=a}^{b} (g n - g (n+1)) = g a - g (b+1)`. -/
private lemma sum_Icc_telescope_sub (g : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ n ∈ Finset.Icc a b, (g n - g (n+1)) = g a - g (b+1) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih => rw [Finset.sum_Icc_succ_top (le_trans hab (Nat.le_succ b)), ih]; ring

/-- Summation-by-parts bound `∑_{Δ ≤ n ≤ N} n^{-(1+ε)} ≤ ε⁻¹ (Δ-1)^{-ε}`. -/
private lemma sum_Icc_rpow_neg_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {Δ N : ℕ}
    (hΔ : 2 ≤ Δ) :
    (∑ n ∈ Finset.Icc Δ N, (n : ℝ) ^ (-(1 + ε))) ≤ (1 / ε) * (((Δ - 1 : ℕ) : ℝ) ^ (-ε)) := by
  rcases lt_or_ge N Δ with hN | hN
  · rw [Finset.Icc_eq_empty (not_le.mpr hN), Finset.sum_empty]
    positivity
  · have hstep : ∀ n ∈ Finset.Icc Δ N,
        (n:ℝ)^(-(1+ε)) ≤ (1/ε) * (((n-1:ℕ):ℝ)^(-ε) - (n:ℝ)^(-ε)) := by
      intro n hn
      rw [Finset.mem_Icc] at hn
      exact rpow_neg_le_telescope_le hε hε1 (le_trans hΔ hn.1)
    have htele : ∑ n ∈ Finset.Icc Δ N, (((n-1:ℕ):ℝ)^(-ε) - ((n:ℕ):ℝ)^(-ε))
        = (((Δ-1:ℕ)):ℝ)^(-ε) - ((N:ℕ):ℝ)^(-ε) := by
      have h := sum_Icc_telescope_sub (fun n => (((n-1:ℕ)):ℝ)^(-ε)) hN
      simpa [Nat.add_sub_cancel] using h
    calc (∑ n ∈ Finset.Icc Δ N, (n:ℝ)^(-(1+ε)))
        ≤ ∑ n ∈ Finset.Icc Δ N, (1/ε) * (((n-1:ℕ):ℝ)^(-ε) - (n:ℝ)^(-ε)) :=
          Finset.sum_le_sum hstep
      _ = (1/ε) * ∑ n ∈ Finset.Icc Δ N, (((n-1:ℕ):ℝ)^(-ε) - (n:ℝ)^(-ε)) := by
          rw [Finset.mul_sum]
      _ = (1/ε) * ((((Δ-1:ℕ)):ℝ)^(-ε) - ((N:ℕ):ℝ)^(-ε)) := by rw [htele]
      _ ≤ (1/ε) * (((Δ-1:ℕ):ℝ)^(-ε)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hNnn : (0:ℝ) ≤ ((N:ℕ):ℝ)^(-ε) := Real.rpow_nonneg (by positivity) _
          linarith

theorem sum_primes_rpow_tail_le (ε : ℝ) (Δ Y : ℕ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hΔ : 2 ≤ Δ) :
    (∑ p ∈ (Finset.Icc Δ Y).filter Nat.Prime, (p : ℝ) ^ (-(1 + ε))) ≤
      32 / (ε * Real.log (Δ : ℝ)) := by
  have hΔpos : (0:ℝ) < (Δ:ℝ) := by exact_mod_cast (by omega : 0 < Δ)
  have hlogΔ : 0 < Real.log (Δ : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < Δ))
  have hden : 0 < ε * Real.log (Δ : ℝ) := mul_pos hε0 hlogΔ
  by_cases hYlt : Y < Δ
  · rw [Finset.Icc_eq_empty (not_le.mpr hYlt), Finset.filter_empty, Finset.sum_empty]
    exact le_of_lt (div_pos (by norm_num) hden)
  · replace hYlt : Δ ≤ Y := le_of_not_gt hYlt
    have hΔ1 : 1 ≤ Δ := by omega
    set w : ℕ → ℝ := fun i => (i:ℝ)^(-(1+ε)) with hw
    set a : ℕ → ℝ := fun i => if i.Prime then 1 else 0 with ha
    -- Relate the target sum to a sum over `Ioc (Δ-1) Y`.
    have hS : (∑ p ∈ (Finset.Icc Δ Y).filter Nat.Prime, (p:ℝ)^(-(1+ε)))
        = ∑ i ∈ Finset.Ioc (Δ-1) Y, w i * a i := by
      rw [hw]
      rw [Finset.sum_filter, ← Ioc_sub_one_eq_Icc hΔ1]
      apply Finset.sum_congr rfl
      intro i hi
      rw [ha]
      by_cases hp : i.Prime <;> simp [hp]
    -- Summation by parts.
    have hparts := Finset.sum_Ioc_by_parts (f := w) (g := a) (m := Δ-1) (n := Y)
      (by omega : Δ-1 < Y)
    simp only [smul_eq_mul, Nat.sub_add_cancel hΔ1] at hparts
    have hGnn : (0:ℝ) ≤ ∑ k ∈ Finset.range Δ, a k :=
      Finset.sum_nonneg (fun k _ => by by_cases hk : Nat.Prime k <;> simp [ha, hk])
    have hwΔnn : (0:ℝ) ≤ w Δ := Real.rpow_nonneg hΔpos.le _
    have hneg : ∑ i ∈ Finset.Ioc (Δ-1) (Y-1), (w (i+1) - w i) * (∑ k ∈ Finset.range (i+1), a k)
        = - ∑ i ∈ Finset.Ioc (Δ-1) (Y-1), (w i - w (i+1)) * (∑ k ∈ Finset.range (i+1), a k) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi; ring
    have hS_bound : (∑ p ∈ (Finset.Icc Δ Y).filter Nat.Prime, (p:ℝ)^(-(1+ε)))
        ≤ w Y * (∑ i ∈ Finset.range (Y+1), a i)
          + ∑ i ∈ Finset.Ioc (Δ-1) (Y-1), (w i - w (i+1)) * (∑ k ∈ Finset.range (i+1), a k) := by
      rw [hS, hparts, hneg]
      nlinarith [mul_nonneg hwΔnn hGnn]
    -- Term 1.
    have hT1 : w Y * (∑ i ∈ Finset.range (Y+1), a i) ≤ 5 / (ε * Real.log (Δ:ℝ)) := by
      have hY2 : 2 ≤ Y := le_trans hΔ hYlt
      have hY1 : (1:ℝ) < (Y:ℝ) := by exact_mod_cast (by omega : 1 < Y)
      have hlogY : 0 < Real.log (Y:ℝ) := Real.log_pos hY1
      have hYpos : (0:ℝ) < (Y:ℝ) := by positivity
      have hGY : (∑ i ∈ Finset.range (Y+1), a i) = ((Nat.primesLE Y).card : ℝ) := by
        rw [ha]; exact sum_range_prime_indicator Y
      rw [hGY]
      have hpi := primesLE_card_le_five Y hY2
      have hwY : w Y = (Y:ℝ)^(-(1+ε)) := by rw [hw]
      have hwYnn : (0:ℝ) ≤ w Y := by rw [hwY]; exact Real.rpow_nonneg hYpos.le _
      have hstep2 : w Y * (5 * (Y:ℝ) / Real.log (Y:ℝ)) = 5 * (Y:ℝ)^(-ε) / Real.log (Y:ℝ) := by
        rw [hwY]
        have hp : (Y:ℝ)^(-(1+ε)) * (Y:ℝ) = (Y:ℝ)^(-ε) := by
          rw [show (-ε:ℝ) = -(1+ε) + 1 by ring, Real.rpow_add hYpos, Real.rpow_one]
        rw [show (Y:ℝ)^(-(1+ε)) * (5 * (Y:ℝ) / Real.log (Y:ℝ))
              = 5 * ((Y:ℝ)^(-(1+ε)) * (Y:ℝ)) / Real.log (Y:ℝ) by ring, hp]
      have hlogle : Real.log (Δ:ℝ) ≤ Real.log (Y:ℝ) :=
        Real.log_le_log hΔpos (by exact_mod_cast hYlt)
      have hYme : (Y:ℝ)^(-ε) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (by omega : 1 ≤ Y))
          (by linarith : -ε ≤ 0)
      calc w Y * ((Nat.primesLE Y).card : ℝ)
          ≤ w Y * (5 * (Y:ℝ) / Real.log (Y:ℝ)) := mul_le_mul_of_nonneg_left hpi hwYnn
        _ = 5 * (Y:ℝ)^(-ε) / Real.log (Y:ℝ) := hstep2
        _ ≤ 5 * 1 / Real.log (Y:ℝ) := by
            apply div_le_div_of_nonneg_right _ hlogY.le; linarith
        _ = 5 / Real.log (Y:ℝ) := by ring
        _ ≤ 5 / Real.log (Δ:ℝ) := by
            apply div_le_div_of_nonneg_left (by norm_num) hlogΔ hlogle
        _ ≤ 5 / (ε * Real.log (Δ:ℝ)) := by
            apply div_le_div_of_nonneg_left (by norm_num) hden
            nlinarith [hε0, hε1, hlogΔ]
    -- Term 2.
    have hT2 : ∑ i ∈ Finset.Ioc (Δ-1) (Y-1), (w i - w (i+1)) * (∑ k ∈ Finset.range (i+1), a k)
        ≤ 10 / (ε * Real.log (Δ:ℝ)) := by
      have hstep : ∀ i ∈ Finset.Ioc (Δ-1) (Y-1),
          (w i - w (i+1)) * (∑ k ∈ Finset.range (i+1), a k)
            ≤ (10 / Real.log (Δ:ℝ)) * (i:ℝ)^(-(1+ε)) := by
        intro i hi
        rw [Finset.mem_Ioc] at hi
        have hiΔ : Δ ≤ i := by omega
        have hi2 : 2 ≤ i := le_trans hΔ hiΔ
        have hiR : (0:ℝ) < (i:ℝ) := by positivity
        have hi1 : (1:ℝ) ≤ (i:ℝ) := by exact_mod_cast (by omega : 1 ≤ i)
        have hi1' : (1:ℝ) < (i:ℝ) := by exact_mod_cast (by omega : 1 < i)
        have hlogi : 0 < Real.log (i:ℝ) := Real.log_pos hi1'
        have hlogi_le : Real.log (Δ:ℝ) ≤ Real.log (i:ℝ) :=
          Real.log_le_log hΔpos (by exact_mod_cast hiΔ)
        have hGi : (∑ k ∈ Finset.range (i+1), a k) = ((Nat.primesLE i).card : ℝ) := by
          rw [ha]; exact sum_range_prime_indicator i
        have hGinn : (0:ℝ) ≤ ((Nat.primesLE i).card : ℝ) := by positivity
        have hpi := primesLE_card_le_five i hi2
        have hdiff : w i - w (i+1) ≤ (1+ε) * (i:ℝ)^(-(2+ε)) := by
          rw [hw]; exact rpow_neg_diff_le hε0 (n := i) (by omega : 1 ≤ i)
        have hpow1 : (i:ℝ)^(-(2+ε)) * (i:ℝ) = (i:ℝ)^(-(1+ε)) := by
          rw [show (-(1+ε):ℝ) = -(2+ε) + 1 by ring, Real.rpow_add hiR, Real.rpow_one]
        have hA : 5 * (1+ε) / Real.log (i:ℝ) ≤ 10 / Real.log (Δ:ℝ) := by
          rw [div_le_div_iff₀ hlogi hlogΔ]
          nlinarith [hε1, hlogi_le, hlogΔ.le, hlogi.le]
        have hmain : (1+ε) * (i:ℝ)^(-(2+ε)) * (5 * (i:ℝ) / Real.log (i:ℝ))
            ≤ (10 / Real.log (Δ:ℝ)) * (i:ℝ)^(-(1+ε)) := by
          have hpos : (0:ℝ) ≤ (i:ℝ)^(-(1+ε)) := Real.rpow_nonneg hiR.le _
          have hre : (1+ε) * (i:ℝ)^(-(2+ε)) * (5 * (i:ℝ) / Real.log (i:ℝ))
              = (5 * (1+ε) / Real.log (i:ℝ)) * (i:ℝ)^(-(1+ε)) := by
            rw [show (1+ε) * (i:ℝ)^(-(2+ε)) * (5 * (i:ℝ) / Real.log (i:ℝ))
                  = 5 * (1+ε) * ((i:ℝ)^(-(2+ε)) * (i:ℝ)) / Real.log (i:ℝ) by ring, hpow1]
            ring
          rw [hre]
          exact mul_le_mul_of_nonneg_right hA hpos
        calc (w i - w (i+1)) * (∑ k ∈ Finset.range (i+1), a k)
            ≤ ((1+ε) * (i:ℝ)^(-(2+ε))) * ((Nat.primesLE i).card : ℝ) := by
              rw [hGi]; exact mul_le_mul_of_nonneg_right hdiff hGinn
          _ ≤ ((1+ε) * (i:ℝ)^(-(2+ε))) * (5 * (i:ℝ) / Real.log (i:ℝ)) :=
              mul_le_mul_of_nonneg_left hpi (mul_nonneg (by linarith) (Real.rpow_nonneg hiR.le _))
          _ ≤ (10 / Real.log (Δ:ℝ)) * (i:ℝ)^(-(1+ε)) := hmain
      calc ∑ i ∈ Finset.Ioc (Δ-1) (Y-1), (w i - w (i+1)) * (∑ k ∈ Finset.range (i+1), a k)
          ≤ ∑ i ∈ Finset.Ioc (Δ-1) (Y-1), (10 / Real.log (Δ:ℝ)) * (i:ℝ)^(-(1+ε)) :=
            Finset.sum_le_sum hstep
        _ = (10 / Real.log (Δ:ℝ)) * ∑ i ∈ Finset.Ioc (Δ-1) (Y-1), (i:ℝ)^(-(1+ε)) := by
            rw [Finset.mul_sum]
        _ = (10 / Real.log (Δ:ℝ)) * ∑ i ∈ Finset.Icc Δ (Y-1), (i:ℝ)^(-(1+ε)) := by
            rw [Ioc_sub_one_eq_Icc hΔ1]
        _ ≤ (10 / Real.log (Δ:ℝ)) * ((1/ε) * (((Δ-1:ℕ):ℝ)^(-ε))) :=
            mul_le_mul_of_nonneg_left (sum_Icc_rpow_neg_le hε0 hε1 hΔ) (by positivity)
        _ ≤ 10 / (ε * Real.log (Δ:ℝ)) := by
            have hΔm : ((Δ-1:ℕ):ℝ)^(-ε) ≤ 1 :=
              Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (by omega : 1 ≤ Δ-1))
                (by linarith : -ε ≤ 0)
            calc (10 / Real.log (Δ:ℝ)) * ((1/ε) * ((Δ-1:ℕ):ℝ)^(-ε))
                ≤ (10 / Real.log (Δ:ℝ)) * ((1/ε) * 1) := by
                  apply mul_le_mul_of_nonneg_left _ (div_nonneg (by norm_num) hlogΔ.le)
                  exact mul_le_mul_of_nonneg_left hΔm (by positivity)
              _ = 10 / (ε * Real.log (Δ:ℝ)) := by ring
    calc (∑ p ∈ (Finset.Icc Δ Y).filter Nat.Prime, (p:ℝ)^(-(1+ε)))
        ≤ w Y * (∑ i ∈ Finset.range (Y+1), a i)
          + ∑ i ∈ Finset.Ioc (Δ-1) (Y-1), (w i - w (i+1)) * (∑ k ∈ Finset.range (i+1), a k) :=
          hS_bound
      _ ≤ 5 / (ε * Real.log (Δ:ℝ)) + 10 / (ε * Real.log (Δ:ℝ)) := add_le_add hT1 hT2
      _ = 15 / (ε * Real.log (Δ:ℝ)) := by ring
      _ ≤ 32 / (ε * Real.log (Δ:ℝ)) :=
          div_le_div_of_nonneg_right (by norm_num) hden.le

end Commons.NumberTheory.Chebyshev