import Mathlib
import Submission.Work.FIArea4.S15_hard_defs
import Submission.Work.FIArea4.polarBox_card_le
import Submission.Work.FIArea4.S15_energy_defs
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_sum_sq_root_count_le_two_pow_omega
import Submission.Commons.NumberTheory.Divisors.sum_tau_pow_div_le
import Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound_ge_three
import Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound
import Submission.Commons.NumberTheory.Divisors.small_divisor_tau_le
import Submission.Commons.NumberTheory.DivisorSum.tau_pow_eight_le_sum_dvd_cube
import Submission.Work.FIArea4.S15box
import Submission.Work.FIArea4.S15_polar_joint_count
import Submission.Work.FIArea4.S15_tau10_d2_sum

set_option maxHeartbeats 800000

namespace Work.FIArea4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## An auxiliary two-factor bound -/

/-- Two-factor bound used in the closing estimate:
`(A + K^{1/4})·(A + K^{1/3}) ≤ 200·(θ²N + N^{5/6} + 1)` for `A = 10θ√N` and `K ≤ 2N + 1`. -/
lemma S15bea_Th_bound (Pa : Work.FITop.Params) (K : ℕ) (Aw : ℝ)
    (hAw : Aw = 10 * Pa.θ * Real.sqrt Pa.N) (hAw0 : 0 ≤ Aw)
    (hK1 : 1 ≤ K) (hKle : (K : ℝ) ≤ 2 * Pa.N + 1)
    (hθ1 : Pa.θ ≤ 1) (hN1 : 1 ≤ Pa.N) :
    (Aw + (K : ℝ) ^ (1 / 4 : ℝ)) * (Aw + (K : ℝ) ^ (1 / 3 : ℝ))
      ≤ 200 * (Pa.θ ^ 2 * Pa.N + Pa.N ^ ((5 : ℝ) / 6) + 1) := by
  set Th : ℝ := Pa.θ ^ 2 * Pa.N + Pa.N ^ ((5 : ℝ) / 6) + 1 with hTh
  have h1 : (K : ℝ) ^ (1 / 4 : ℝ) ≤ (K : ℝ) ^ (1 / 3 : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le
    · exact_mod_cast hK1
    · norm_num
  have h2 : (Aw + (K : ℝ) ^ (1 / 4 : ℝ)) ≤ (Aw + (K : ℝ) ^ (1 / 3 : ℝ)) := by linarith
  have h3 : 0 ≤ Aw + (K : ℝ) ^ (1 / 3 : ℝ) := by
    have := Real.rpow_nonneg (by positivity : (0:ℝ) ≤ (K:ℝ)) (1/3:ℝ); linarith
  have h4 : (Aw + (K : ℝ) ^ (1 / 3 : ℝ)) ^ 2 ≤ 200 * Th := by
    have hAw2 : Aw ^ 2 = 100 * (Pa.θ ^ 2 * Pa.N) := by
      rw [hAw]
      rw [show (10 * Pa.θ * Real.sqrt Pa.N) ^ 2 = 100 * Pa.θ ^ 2 * (Real.sqrt Pa.N)^2 by ring,
        Real.sq_sqrt (by linarith)]
      ring
    have hK13 : (K : ℝ) ^ (1 / 3 : ℝ) ≤ (2 * Pa.N + 1) ^ (1 / 3 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hKle (by norm_num)
    have hK13sq : ((K : ℝ) ^ (1 / 3 : ℝ)) ^ 2 = (K : ℝ) ^ (2 / 3 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    have hK23 : (K : ℝ) ^ (2 / 3 : ℝ) ≤ (2 * Pa.N + 1) ^ (2 / 3 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hKle (by norm_num)
    have h2N1 : (2 * Pa.N + 1) ^ (2 / 3 : ℝ) ≤ (3 * Pa.N) ^ (2 / 3 : ℝ) :=
      Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
    have h3N : (3 * Pa.N) ^ (2 / 3 : ℝ) = (3:ℝ) ^ (2/3:ℝ) * Pa.N ^ (2/3:ℝ) :=
      Real.mul_rpow (by norm_num) (by linarith)
    have hN23 : Pa.N ^ (2 / 3 : ℝ) ≤ Pa.N ^ ((5:ℝ) / 6) := by
      apply Real.rpow_le_rpow_of_exponent_le
      · exact hN1
      · norm_num
    have hA3 : Aw * (K : ℝ) ^ (1 / 3 : ℝ) ≤ 10 * (3:ℝ) ^ (1/3:ℝ) * Pa.N ^ ((5:ℝ)/6) := by
      have hK13' : (K : ℝ) ^ (1 / 3 : ℝ) ≤ (3 * Pa.N) ^ (1 / 3 : ℝ) :=
        le_trans hK13 (Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num))
      have h3N' : (3 * Pa.N) ^ (1 / 3 : ℝ) = (3:ℝ) ^ (1/3:ℝ) * Pa.N ^ (1/3:ℝ) :=
        Real.mul_rpow (by norm_num) (by linarith)
      have hNadd : Pa.N ^ (1/2:ℝ) * Pa.N ^ (1/3:ℝ) = Pa.N ^ ((5:ℝ)/6) := by
        rw [← Real.rpow_add (by linarith)]
        norm_num
      have hN56 : 0 ≤ Pa.N ^ ((5:ℝ)/6) := Real.rpow_nonneg (by linarith) _
      have h3a : (0:ℝ) ≤ (3:ℝ) ^ (1/3:ℝ) := Real.rpow_nonneg (by norm_num) _
      have h1 : Aw * (K : ℝ) ^ (1 / 3 : ℝ) ≤ Aw * (3 * Pa.N) ^ (1 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_left hK13' hAw0
      have h2 : Aw * (3 * Pa.N) ^ (1 / 3 : ℝ) ≤ 10 * (3:ℝ) ^ (1/3:ℝ) * Pa.N ^ ((5:ℝ)/6) := by
        rw [hAw, h3N', Real.sqrt_eq_rpow]
        calc (10 * Pa.θ * Pa.N ^ (1/2:ℝ)) * ((3:ℝ) ^ (1/3:ℝ) * Pa.N ^ (1/3:ℝ))
            = 10 * (3:ℝ) ^ (1/3:ℝ) * Pa.θ * (Pa.N ^ (1/2:ℝ) * Pa.N ^ (1/3:ℝ)) := by ring
          _ = 10 * (3:ℝ) ^ (1/3:ℝ) * Pa.θ * Pa.N ^ ((5:ℝ)/6) := by rw [hNadd]
          _ ≤ 10 * (3:ℝ) ^ (1/3:ℝ) * Pa.N ^ ((5:ℝ)/6) := by
              apply mul_le_mul_of_nonneg_right _ hN56
              nlinarith [hθ1, h3a]
      linarith [h1, h2]
    have hTh0 : 0 ≤ Th := by
      rw [hTh]
      have := Real.rpow_nonneg (by linarith : (0:ℝ) ≤ Pa.N) ((5:ℝ)/6)
      positivity
    have hexpand : (Aw + (K : ℝ) ^ (1 / 3 : ℝ)) ^ 2
        = Aw^2 + 2 * (Aw * (K : ℝ) ^ (1 / 3 : ℝ)) + ((K : ℝ) ^ (1 / 3 : ℝ))^2 := by ring
    rw [hexpand, hAw2, hK13sq]
    have hterm3 : (K : ℝ) ^ (2/3:ℝ) ≤ (3:ℝ) ^ (2/3:ℝ) * Pa.N ^ ((5:ℝ)/6) :=
      le_trans (le_trans hK23 h2N1) (le_trans (le_of_eq h3N) (mul_le_mul_of_nonneg_left hN23 (by positivity)))
    have h56nn : 0 ≤ Pa.N ^ ((5:ℝ)/6) := Real.rpow_nonneg (by linarith) _
    have hθ2N : 0 ≤ Pa.θ ^ 2 * Pa.N := by positivity
    have h3a1 : (3:ℝ) ^ (1/3:ℝ) ≤ 3 := by
      have h := Real.rpow_le_rpow_of_exponent_le (show (1:ℝ) ≤ 3 by norm_num) (show (1/3:ℝ) ≤ 1 by norm_num)
      simpa using h
    have h3b1 : (3:ℝ) ^ (2/3:ℝ) ≤ 3 := by
      have h := Real.rpow_le_rpow_of_exponent_le (show (1:ℝ) ≤ 3 by norm_num) (show (2/3:ℝ) ≤ 1 by norm_num)
      simpa using h
    have hA3b : Aw * (K:ℝ)^(1/3:ℝ) ≤ 30 * Pa.N ^ ((5:ℝ)/6) := by
      have hm := mul_le_mul_of_nonneg_right h3a1 h56nn
      linarith [hA3, hm]
    have hterm3b : (K:ℝ)^(2/3:ℝ) ≤ 3 * Pa.N ^ ((5:ℝ)/6) := by
      have hm := mul_le_mul_of_nonneg_right h3b1 h56nn
      linarith [hterm3, hm]
    rw [hTh]
    linarith [hA3b, hterm3b, h56nn, hθ2N]
  calc (Aw + (K : ℝ) ^ (1 / 4 : ℝ)) * (Aw + (K : ℝ) ^ (1 / 3 : ℝ))
      ≤ (Aw + (K : ℝ) ^ (1 / 3 : ℝ)) * (Aw + (K : ℝ) ^ (1 / 3 : ℝ)) :=
        mul_le_mul_of_nonneg_right h2 h3
    _ = (Aw + (K : ℝ) ^ (1 / 3 : ℝ)) ^ 2 := by ring
    _ ≤ 200 * Th := h4

/-- The `L`-factor: `Σ_{L⁴ ≤ K} (2τ(L))⁶(Aw/L + 1) ≤ 2⁶ C₁ (log (K+2))^{2⁶} (Aw + K^{1/4})`.

This is the first of the two divisor-sums into which FI's Lemma 2.2 turns `τ(re z)³`; the
hypothesis `hC_1` is the divisor-sum estimate `Σ_{d ≤ y} τ(d)⁶/d ≤ C₁ (log (y+2))^{2⁶}`. -/
lemma S15bea_L_bound (C_1 : ℝ) (hC_1pos : 0 < C_1)
    (hC_1 : ∀ y : ℕ, 1 ≤ y → (∑ d ∈ Finset.Icc 1 y,
          ((((d.divisors.card : ℕ) : ℝ)) ^ 6 / (d : ℝ)))
        ≤ C_1 * (Real.log ((y : ℝ) + 2)) ^ (2 ^ 6))
    (K : ℕ) (hK1 : 1 ≤ K) (Aw : ℝ) (hAw0 : 0 ≤ Aw) :
    (∑ L ∈ (Finset.Icc 1 K).filter (fun L => L ^ 4 ≤ K),
        (2 * ((L.divisors.card : ℕ) : ℝ)) ^ 6 * (Aw / (L : ℝ) + 1))
      ≤ 2 ^ 6 * (C_1 * (Real.log ((K : ℝ) + 2)) ^ (2 ^ 6)) * (Aw + (K : ℝ) ^ (1 / 4 : ℝ)) := by
    set BigL : Finset ℕ := (Finset.Icc 1 K).filter (fun L => L ^ 4 ≤ K) with hBigL
    set fL : ℕ → ℝ := fun L => (2 * ((L.divisors.card : ℕ) : ℝ)) ^ 6 with hfL
    have hT1 : (∑ L ∈ BigL, ((((L.divisors.card : ℕ) : ℝ)) ^ 6 / (L : ℝ)))
        ≤ C_1 * (Real.log ((K : ℝ) + 2)) ^ (2 ^ 6) := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (hC_1 K hK1)
      · intro L hL
        rw [hBigL, Finset.mem_filter] at hL
        exact hL.1
      · intro L _ _
        positivity
    have hT2 : (∑ L ∈ BigL, ((((L.divisors.card : ℕ) : ℝ)) ^ 6))
        ≤ (K : ℝ) ^ (1 / 4 : ℝ) * (∑ L ∈ BigL, ((((L.divisors.card : ℕ) : ℝ)) ^ 6 / (L : ℝ))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum; intro L hL
      rw [hBigL, Finset.mem_filter] at hL
      obtain ⟨hLI, hL4⟩ := hL
      obtain ⟨hL1, hLK⟩ := Finset.mem_Icc.mp hLI
      have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL1
      have hLpow : ((L : ℝ) ^ 4) ^ (1 / 4 : ℝ) = (L : ℝ) := by
        rw [← Real.rpow_natCast (L : ℝ) 4, ← Real.rpow_mul (by positivity)]
        norm_num
      have hLK4 : (L : ℝ) ≤ (K : ℝ) ^ (1 / 4 : ℝ) := by
        rw [← hLpow]
        apply Real.rpow_le_rpow (by positivity)
        · have : ((L ^ 4 : ℕ) : ℝ) ≤ ((K : ℕ) : ℝ) := by exact_mod_cast hL4
          push_cast at this
          exact this
        · norm_num
      calc ((((L.divisors.card : ℕ) : ℝ)) ^ 6)
          = (L : ℝ) * ((((L.divisors.card : ℕ) : ℝ)) ^ 6 / (L : ℝ)) := by field_simp
        _ ≤ (K : ℝ) ^ (1 / 4 : ℝ) * ((((L.divisors.card : ℕ) : ℝ)) ^ 6 / (L : ℝ)) :=
            mul_le_mul_of_nonneg_right hLK4 (by positivity)
    have hT1nn : 0 ≤ C_1 * (Real.log ((K : ℝ) + 2)) ^ (2 ^ 6) := by
      apply mul_nonneg hC_1pos.le
      apply pow_nonneg
      apply Real.log_nonneg
      have : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK1
      linarith
    have hkey : (∑ L ∈ BigL, fL L * (Aw / (L : ℝ) + 1))
        = 2 ^ 6 * (Aw * (∑ L ∈ BigL, ((((L.divisors.card : ℕ) : ℝ)) ^ 6 / (L : ℝ)))
            + (∑ L ∈ BigL, ((((L.divisors.card : ℕ) : ℝ)) ^ 6))) := by
      have hpt : ∀ L : ℕ, fL L * (Aw / (L : ℝ) + 1)
          = 2 ^ 6 * (Aw * ((((L.divisors.card : ℕ) : ℝ)) ^ 6 / (L : ℝ))
              + ((((L.divisors.card : ℕ) : ℝ)) ^ 6)) := by
        intro L; simp only [hfL]; rw [mul_pow]; ring
      calc (∑ L ∈ BigL, fL L * (Aw / (L : ℝ) + 1))
          = ∑ L ∈ BigL, 2 ^ 6 * (Aw * ((((L.divisors.card : ℕ) : ℝ)) ^ 6 / (L : ℝ))
              + ((((L.divisors.card : ℕ) : ℝ)) ^ 6)) :=
            Finset.sum_congr rfl (fun L _ => hpt L)
        _ = 2 ^ 6 * (∑ L ∈ BigL, (Aw * ((((L.divisors.card : ℕ) : ℝ)) ^ 6 / (L : ℝ))
              + ((((L.divisors.card : ℕ) : ℝ)) ^ 6))) := by rw [Finset.mul_sum]
        _ = 2 ^ 6 * (Aw * (∑ L ∈ BigL, ((((L.divisors.card : ℕ) : ℝ)) ^ 6 / (L : ℝ)))
              + (∑ L ∈ BigL, ((((L.divisors.card : ℕ) : ℝ)) ^ 6))) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum]
    rw [hkey]
    have hstep : Aw * (∑ L ∈ BigL, ((((L.divisors.card : ℕ) : ℝ)) ^ 6 / (L : ℝ)))
          + (∑ L ∈ BigL, ((((L.divisors.card : ℕ) : ℝ)) ^ 6))
        ≤ Aw * (C_1 * (Real.log ((K : ℝ) + 2)) ^ (2 ^ 6))
          + (K : ℝ) ^ (1 / 4 : ℝ) * (C_1 * (Real.log ((K : ℝ) + 2)) ^ (2 ^ 6)) := by
      have h1 := mul_le_mul_of_nonneg_left hT1 hAw0
      have h2 := le_trans hT2 (mul_le_mul_of_nonneg_left hT1 (Real.rpow_nonneg (by positivity : (0:ℝ) ≤ (K:ℝ)) _))
      linarith
    calc 2 ^ 6 * (Aw * (∑ L ∈ BigL, ((((L.divisors.card : ℕ) : ℝ)) ^ 6 / (L : ℝ)))
            + (∑ L ∈ BigL, ((((L.divisors.card : ℕ) : ℝ)) ^ 6)))
        = 2 ^ 6 * (Aw * (∑ L ∈ BigL, ((((L.divisors.card : ℕ) : ℝ)) ^ 6 / (L : ℝ)))
            + (∑ L ∈ BigL, ((((L.divisors.card : ℕ) : ℝ)) ^ 6))) := rfl
      _ ≤ 2 ^ 6 * (Aw * (C_1 * (Real.log ((K : ℝ) + 2)) ^ (2 ^ 6))
            + (K : ℝ) ^ (1 / 4 : ℝ) * (C_1 * (Real.log ((K : ℝ) + 2)) ^ (2 ^ 6))) :=
          mul_le_mul_of_nonneg_left hstep (by norm_num)
      _ = 2 ^ 6 * (C_1 * (Real.log ((K : ℝ) + 2)) ^ (2 ^ 6)) * (Aw + (K : ℝ) ^ (1 / 4 : ℝ)) := by ring

/-- The `d`-factor: `Σ_{d³ ≤ K} (2τ(d))¹⁰((Aw/d + 1) 2^{ω(d)} d₂(d)) ≤ 2¹⁰ C₂ (log (K+2))^B
(Aw + K^{1/3})`, the second divisor-sum (from `τ(|z|²)²`). -/
lemma S15bea_D_bound (C_2 B : ℝ) (hC_2 : 0 < C_2)
    (hsum : ∀ Y : ℕ, (∑ d ∈ Finset.Icc 1 Y,
          ((d.divisors.card : ℝ) ^ (10 : ℕ)) * (2 : ℝ) ^ (Nat.primeFactors d).card
            * ((S15d2 d : ℕ) : ℝ) / (d : ℝ))
        ≤ C_2 * (Real.log ((Y : ℝ) + 2)) ^ B)
    (K : ℕ) (hK1 : 1 ≤ K) (Aw : ℝ) (hAw0 : 0 ≤ Aw) :
    (∑ d ∈ (Finset.Icc 1 K).filter (fun d => d ^ 3 ≤ K),
        (2 * ((d.divisors.card : ℕ) : ℝ)) ^ 10 * ((Aw / (d : ℝ) + 1)
          * (2 : ℝ) ^ (Nat.primeFactors d).card * ((S15d2 d : ℕ) : ℝ)))
      ≤ 2 ^ 10 * (C_2 * (Real.log ((K : ℝ) + 2)) ^ B) * (Aw + (K : ℝ) ^ (1 / 3 : ℝ)) := by
    set Bigd : Finset ℕ := (Finset.Icc 1 K).filter (fun d => d ^ 3 ≤ K) with hBigd
    set gL : ℕ → ℝ := fun d => (2 * ((d.divisors.card : ℕ) : ℝ)) ^ 10 with hgL
    have hS1 : (∑ d ∈ Bigd, ((((d.divisors.card : ℕ) : ℝ)) ^ 10)
          * (2 : ℝ) ^ (Nat.primeFactors d).card * ((S15d2 d : ℕ) : ℝ) / (d : ℝ))
        ≤ C_2 * (Real.log ((K : ℝ) + 2)) ^ B := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (hsum K)
      · intro d hd
        rw [hBigd, Finset.mem_filter] at hd
        exact hd.1
      · intro d _ _
        positivity
    have hS2 : (∑ d ∈ Bigd, ((((d.divisors.card : ℕ) : ℝ)) ^ 10)
          * (2 : ℝ) ^ (Nat.primeFactors d).card * ((S15d2 d : ℕ) : ℝ))
        ≤ (K : ℝ) ^ (1 / 3 : ℝ) * (∑ d ∈ Bigd, ((((d.divisors.card : ℕ) : ℝ)) ^ 10)
          * (2 : ℝ) ^ (Nat.primeFactors d).card * ((S15d2 d : ℕ) : ℝ) / (d : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum; intro d hd
      rw [hBigd, Finset.mem_filter] at hd
      obtain ⟨hLI, hd3⟩ := hd
      obtain ⟨hd1, hdK⟩ := Finset.mem_Icc.mp hLI
      have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
      have hdpow : ((d : ℝ) ^ 3) ^ (1 / 3 : ℝ) = (d : ℝ) := by
        rw [← Real.rpow_natCast (d : ℝ) 3, ← Real.rpow_mul (by positivity)]
        norm_num
      have hdK3 : (d : ℝ) ≤ (K : ℝ) ^ (1 / 3 : ℝ) := by
        rw [← hdpow]
        apply Real.rpow_le_rpow (by positivity)
        · have : ((d ^ 3 : ℕ) : ℝ) ≤ ((K : ℕ) : ℝ) := by exact_mod_cast hd3
          push_cast at this
          exact this
        · norm_num
      have hdn : 0 ≤ ((((d.divisors.card : ℕ) : ℝ)) ^ 10) * (2 : ℝ) ^ (Nat.primeFactors d).card
            * ((S15d2 d : ℕ) : ℝ) / (d : ℝ) := by positivity
      calc ((((d.divisors.card : ℕ) : ℝ)) ^ 10) * (2 : ℝ) ^ (Nat.primeFactors d).card * ((S15d2 d : ℕ) : ℝ)
          = ((((d.divisors.card : ℕ) : ℝ)) ^ 10) * (2 : ℝ) ^ (Nat.primeFactors d).card
              * ((S15d2 d : ℕ) : ℝ) / (d : ℝ) * (d : ℝ) := by field_simp
        _ ≤ ((((d.divisors.card : ℕ) : ℝ)) ^ 10) * (2 : ℝ) ^ (Nat.primeFactors d).card
              * ((S15d2 d : ℕ) : ℝ) / (d : ℝ) * (K : ℝ) ^ (1 / 3 : ℝ) :=
            mul_le_mul_of_nonneg_left hdK3 hdn
        _ = (K : ℝ) ^ (1 / 3 : ℝ) * (((((d.divisors.card : ℕ) : ℝ)) ^ 10)
              * (2 : ℝ) ^ (Nat.primeFactors d).card * ((S15d2 d : ℕ) : ℝ) / (d : ℝ)) := by ring
    have hkey : (∑ d ∈ Bigd, gL d * ((Aw / (d : ℝ) + 1)
          * (2 : ℝ) ^ (Nat.primeFactors d).card * ((S15d2 d : ℕ) : ℝ)))
        = 2 ^ 10 * (Aw * (∑ d ∈ Bigd, ((((d.divisors.card : ℕ) : ℝ)) ^ 10)
              * (2 : ℝ) ^ (Nat.primeFactors d).card * ((S15d2 d : ℕ) : ℝ) / (d : ℝ))
            + (∑ d ∈ Bigd, ((((d.divisors.card : ℕ) : ℝ)) ^ 10)
              * (2 : ℝ) ^ (Nat.primeFactors d).card * ((S15d2 d : ℕ) : ℝ))) := by
      have hpt : ∀ d : ℕ, gL d * ((Aw / (d : ℝ) + 1)
            * (2 : ℝ) ^ (Nat.primeFactors d).card * ((S15d2 d : ℕ) : ℝ))
          = 2 ^ 10 * (Aw * ((((d.divisors.card : ℕ) : ℝ)) ^ 10)
              * (2 : ℝ) ^ (Nat.primeFactors d).card * ((S15d2 d : ℕ) : ℝ) / (d : ℝ)
            + ((((d.divisors.card : ℕ) : ℝ)) ^ 10)
              * (2 : ℝ) ^ (Nat.primeFactors d).card * ((S15d2 d : ℕ) : ℝ)) := by
        intro d; simp only [hgL]; rw [mul_pow]; ring
      calc (∑ d ∈ Bigd, gL d * ((Aw / (d : ℝ) + 1)
            * (2 : ℝ) ^ (Nat.primeFactors d).card * ((S15d2 d : ℕ) : ℝ)))
          = ∑ d ∈ Bigd, 2 ^ 10 * (Aw * ((((d.divisors.card : ℕ) : ℝ)) ^ 10)
              * (2 : ℝ) ^ (Nat.primeFactors d).card * ((S15d2 d : ℕ) : ℝ) / (d : ℝ)
            + ((((d.divisors.card : ℕ) : ℝ)) ^ 10)
              * (2 : ℝ) ^ (Nat.primeFactors d).card * ((S15d2 d : ℕ) : ℝ)) :=
            Finset.sum_congr rfl (fun d _ => hpt d)
        _ = 2 ^ 10 * (∑ d ∈ Bigd, (Aw * ((((d.divisors.card : ℕ) : ℝ)) ^ 10)
              * (2 : ℝ) ^ (Nat.primeFactors d).card * ((S15d2 d : ℕ) : ℝ) / (d : ℝ)
            + ((((d.divisors.card : ℕ) : ℝ)) ^ 10)
              * (2 : ℝ) ^ (Nat.primeFactors d).card * ((S15d2 d : ℕ) : ℝ))) := by rw [Finset.mul_sum]
        _ = 2 ^ 10 * (Aw * (∑ d ∈ Bigd, ((((d.divisors.card : ℕ) : ℝ)) ^ 10)
              * (2 : ℝ) ^ (Nat.primeFactors d).card * ((S15d2 d : ℕ) : ℝ) / (d : ℝ))
            + (∑ d ∈ Bigd, ((((d.divisors.card : ℕ) : ℝ)) ^ 10)
              * (2 : ℝ) ^ (Nat.primeFactors d).card * ((S15d2 d : ℕ) : ℝ))) := by
            rw [Finset.sum_add_distrib]
            have h1 : (∑ d ∈ Bigd, (Aw * ((((d.divisors.card : ℕ) : ℝ)) ^ 10)
                  * (2 : ℝ) ^ (Nat.primeFactors d).card * ((S15d2 d : ℕ) : ℝ) / (d : ℝ)))
                = ∑ d ∈ Bigd, Aw * (((((d.divisors.card : ℕ) : ℝ)) ^ 10)
                  * (2 : ℝ) ^ (Nat.primeFactors d).card * ((S15d2 d : ℕ) : ℝ) / (d : ℝ)) := by
              apply Finset.sum_congr rfl; intro d _
              ring
            rw [h1, Finset.mul_sum]
    rw [hkey]
    have hS1nn : 0 ≤ C_2 * (Real.log ((K : ℝ) + 2)) ^ B := by
      apply mul_nonneg hC_2.le
      apply Real.rpow_nonneg
      apply Real.log_nonneg
      have : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK1
      linarith
    have hK13 : (0 : ℝ) ≤ (K : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_nonneg (by positivity) _
    have hstep : Aw * (∑ d ∈ Bigd, ((((d.divisors.card : ℕ) : ℝ)) ^ 10)
            * (2 : ℝ) ^ (Nat.primeFactors d).card * ((S15d2 d : ℕ) : ℝ) / (d : ℝ))
          + (∑ d ∈ Bigd, ((((d.divisors.card : ℕ) : ℝ)) ^ 10)
            * (2 : ℝ) ^ (Nat.primeFactors d).card * ((S15d2 d : ℕ) : ℝ))
        ≤ Aw * (C_2 * (Real.log ((K : ℝ) + 2)) ^ B)
          + (K : ℝ) ^ (1 / 3 : ℝ) * (C_2 * (Real.log ((K : ℝ) + 2)) ^ B) := by
      have h1 := mul_le_mul_of_nonneg_left hS1 hAw0
      have h2 := le_trans hS2 (mul_le_mul_of_nonneg_left hS1 hK13)
      linarith
    calc 2 ^ 10 * (Aw * (∑ d ∈ Bigd, ((((d.divisors.card : ℕ) : ℝ)) ^ 10)
            * (2 : ℝ) ^ (Nat.primeFactors d).card * ((S15d2 d : ℕ) : ℝ) / (d : ℝ))
          + (∑ d ∈ Bigd, ((((d.divisors.card : ℕ) : ℝ)) ^ 10)
            * (2 : ℝ) ^ (Nat.primeFactors d).card * ((S15d2 d : ℕ) : ℝ)))
        ≤ 2 ^ 10 * (Aw * (C_2 * (Real.log ((K : ℝ) + 2)) ^ B)
          + (K : ℝ) ^ (1 / 3 : ℝ) * (C_2 * (Real.log ((K : ℝ) + 2)) ^ B)) :=
          mul_le_mul_of_nonneg_left hstep (by norm_num)
      _ = 2 ^ 10 * (C_2 * (Real.log ((K : ℝ) + 2)) ^ B) * (Aw + (K : ℝ) ^ (1 / 3 : ℝ)) := by ring

/-- Steps 1–3 of the box-energy estimate: pointwise expansion, exchange of summations and the
joint lattice count, assembled into the product of the two divisor-sums. -/
lemma S15bea_main_bound (C_A : ℝ) (hC_A : 0 < C_A)
    (hcount : ∀ (Pa : Work.FITop.Params) (φ : ℝ) (L d : ℕ), 1 ≤ L → 1 ≤ d →
      (((S15polarBox Pa φ).filter (fun z => L ∣ z.re.natAbs ∧ d ∣ Work.FIPlan.gnorm z)).card : ℝ)
        ≤ C_A * ((10 * Pa.θ * Real.sqrt Pa.N) / (d : ℝ) + 1)
            * ((10 * Pa.θ * Real.sqrt Pa.N) / (L : ℝ) + 1)
            * (2 : ℝ) ^ (Nat.primeFactors d).card * ((S15d2 d : ℕ) : ℝ))
    (Pa : Work.FITop.Params) (φ : ℝ) :
    (∑ z ∈ S15polarBox Pa φ,
        ((z.re.natAbs.divisors.card : ℕ) : ℝ) ^ 3
          * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ^ 2)
      ≤ C_A * (∑ L ∈ (Finset.Icc 1 ⌈2 * Pa.N⌉₊).filter (fun L => L ^ 4 ≤ ⌈2 * Pa.N⌉₊),
            (2 * ((L.divisors.card : ℕ) : ℝ)) ^ 6 * (10 * Pa.θ * Real.sqrt Pa.N / (L : ℝ) + 1))
        * (∑ d ∈ (Finset.Icc 1 ⌈2 * Pa.N⌉₊).filter (fun d => d ^ 3 ≤ ⌈2 * Pa.N⌉₊),
            (2 * ((d.divisors.card : ℕ) : ℝ)) ^ 10 * ((10 * Pa.θ * Real.sqrt Pa.N / (d : ℝ) + 1)
              * (2 : ℝ) ^ (Nat.primeFactors d).card * ((S15d2 d : ℕ) : ℝ))) := by
  set K : ℕ := ⌈2 * Pa.N⌉₊ with hK
  set BigL : Finset ℕ := (Finset.Icc 1 K).filter (fun L => L ^ 4 ≤ K) with hBigL
  set Bigd : Finset ℕ := (Finset.Icc 1 K).filter (fun d => d ^ 3 ≤ K) with hBigd
  set fL : ℕ → ℝ := fun L => (2 * ((L.divisors.card : ℕ) : ℝ)) ^ 6 with hfL
  set gL : ℕ → ℝ := fun d => (2 * ((d.divisors.card : ℕ) : ℝ)) ^ 10 with hgL
  set S : Finset GaussianInt := S15polarBox Pa φ with hS
  set Aw : ℝ := 10 * Pa.θ * Real.sqrt Pa.N with hAw
  have hθ0 : 0 < Pa.θ := Pa.hθ0
  have hθ1 : Pa.θ ≤ 1 := theta_le_one Pa
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  have hN0 : (0 : ℝ) ≤ Pa.N := le_trans zero_le_one Pa.hN1
  have hKpos : 0 < K := by
    have h : (1 : ℝ) ≤ 2 * Pa.N := by linarith
    have h2 : (1 : ℝ) ≤ (K : ℝ) := by rw [hK]; exact le_trans h (Nat.le_ceil (2 * Pa.N))
    exact_mod_cast h2
  have hK1 : 1 ≤ K := hKpos
  have hKle : (K : ℝ) ≤ 2 * Pa.N + 1 := by
    rw [hK]; exact le_of_lt (Nat.ceil_lt_add_one (by linarith))
  have hAw0 : 0 ≤ Aw := by rw [hAw]; positivity
  have hgnorm_le_K : ∀ z ∈ S, Work.FIPlan.gnorm z ≤ K := by
    intro z hz
    rw [hS] at hz
    have h1 : (Work.FIPlan.gnorm z : ℝ) ≤ 2 * Pa.N := polar_gnorm_le Pa φ hz
    have h2 : (2 * Pa.N : ℝ) ≤ (K : ℝ) := by rw [hK]; exact Nat.le_ceil (2 * Pa.N)
    exact_mod_cast (le_trans h1 h2)
  have hgnorm_pos : ∀ z ∈ S, 1 ≤ Work.FIPlan.gnorm z := by
    intro z hz
    rw [hS] at hz
    exact polar_gnorm_pos Pa φ hz
  -- ## Step 1: pointwise expansion
  have hsumLnn : ∀ z : GaussianInt, 0 ≤ (∑ L ∈ BigL, (if L ∣ z.re.natAbs then fL L else 0)) := by
    intro z
    apply Finset.sum_nonneg
    intro L _
    split_ifs with h
    · rw [hfL]; positivity
    · norm_num
  have hsumDnn : ∀ z : GaussianInt, 0 ≤ (∑ d ∈ Bigd, (if d ∣ Work.FIPlan.gnorm z then gL d else 0)) := by
    intro z
    apply Finset.sum_nonneg
    intro d _
    split_ifs with h
    · rw [hgL]; positivity
    · norm_num
  have hzstep : ∀ z ∈ S,
      ((z.re.natAbs.divisors.card : ℕ) : ℝ) ^ 3
          * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ^ 2
        ≤ (∑ L ∈ BigL, (if L ∣ z.re.natAbs then fL L else 0))
          * (∑ d ∈ Bigd, (if d ∣ Work.FIPlan.gnorm z then gL d else 0)) := by
    intro z hz
    by_cases hre0 : z.re.natAbs = 0
    · have hcard : z.re.natAbs.divisors.card = 0 := by
        rw [hre0]; simp
      have hzero : (((0 : ℕ) : ℝ)) ^ 3 = 0 := by norm_num
      rw [hcard, hzero, zero_mul]
      exact mul_nonneg (hsumLnn z) (hsumDnn z)
    · have hre1 : 1 ≤ z.re.natAbs := Nat.pos_of_ne_zero hre0
      have hm1 : 1 ≤ Work.FIPlan.gnorm z := hgnorm_pos z hz
      have hre_le : z.re.natAbs ≤ Work.FIPlan.gnorm z := natAbs_re_le_gnorm z
      have hre_sq : z.re.natAbs ^ 2 ≤ Work.FIPlan.gnorm z := re_sq_le_gnorm z
      have hmK : Work.FIPlan.gnorm z ≤ K := hgnorm_le_K z hz
      have h1 : ((z.re.natAbs.divisors.card : ℕ) : ℝ) ^ 3
          ≤ ∑ L ∈ (z.re.natAbs.divisors.filter (fun L => L ^ 2 ≤ z.re.natAbs)), fL L := by
        rw [hfL]
        exact tau_cube_le_sum_divisors_sq _ hre1
      have h2 : (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ^ 2
          ≤ ∑ d ∈ ((Work.FIPlan.gnorm z).divisors.filter (fun d => d ^ 3 ≤ Work.FIPlan.gnorm z)), gL d := by
        rw [hgL]
        exact tau_sq_le_sum_divisors_cube _ hm1
      have hinnerLnn : 0 ≤ ∑ L ∈ (z.re.natAbs.divisors.filter (fun L => L ^ 2 ≤ z.re.natAbs)), fL L := by
        apply Finset.sum_nonneg; intro L _; rw [hfL]; positivity
      have hinnerDnn : 0 ≤ ∑ d ∈ ((Work.FIPlan.gnorm z).divisors.filter (fun d => d ^ 3 ≤ Work.FIPlan.gnorm z)), gL d := by
        apply Finset.sum_nonneg; intro d _; rw [hgL]; positivity
      have hsubL : (z.re.natAbs.divisors.filter (fun L => L ^ 2 ≤ z.re.natAbs))
          ⊆ BigL.filter (fun L => L ∣ z.re.natAbs) := by
        intro L hL
        rw [Finset.mem_filter] at hL ⊢
        obtain ⟨hdvd, hLsq⟩ := hL
        obtain ⟨hLdvd, hre0'⟩ := Nat.mem_divisors.mp hdvd
        have hL1 : 1 ≤ L := Nat.pos_of_dvd_of_pos hLdvd (Nat.pos_of_ne_zero hre0)
        have hLle : L ≤ z.re.natAbs := Nat.le_of_dvd (Nat.pos_of_ne_zero hre0) hLdvd
        have hL4 : L ^ 4 ≤ K := by
          calc L ^ 4 = (L ^ 2) ^ 2 := by ring
            _ ≤ z.re.natAbs ^ 2 := Nat.pow_le_pow_left hLsq 2
            _ ≤ Work.FIPlan.gnorm z := hre_sq
            _ ≤ K := hmK
        have hLK : L ≤ K := le_trans hLle (le_trans hre_le hmK)
        exact ⟨by
          rw [hBigL, Finset.mem_filter]
          exact ⟨Finset.mem_Icc.mpr ⟨hL1, hLK⟩, hL4⟩, hLdvd⟩
      have hsubD : ((Work.FIPlan.gnorm z).divisors.filter (fun d => d ^ 3 ≤ Work.FIPlan.gnorm z))
          ⊆ Bigd.filter (fun d => d ∣ Work.FIPlan.gnorm z) := by
        intro d hd
        rw [Finset.mem_filter] at hd ⊢
        obtain ⟨hdvd, hdcube⟩ := hd
        obtain ⟨hddvd, hm0'⟩ := Nat.mem_divisors.mp hdvd
        have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hddvd (Nat.pos_of_ne_zero hm0')
        have hdK : d ≤ K := le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0') hddvd) hmK
        exact ⟨by
          rw [hBigd, Finset.mem_filter]
          exact ⟨Finset.mem_Icc.mpr ⟨hd1, hdK⟩, le_trans hdcube hmK⟩, hddvd⟩
      have hLb : (∑ L ∈ (z.re.natAbs.divisors.filter (fun L => L ^ 2 ≤ z.re.natAbs)), fL L)
          ≤ (∑ L ∈ BigL, (if L ∣ z.re.natAbs then fL L else 0)) := by
        calc (∑ L ∈ (z.re.natAbs.divisors.filter (fun L => L ^ 2 ≤ z.re.natAbs)), fL L)
            ≤ ∑ L ∈ BigL.filter (fun L => L ∣ z.re.natAbs), fL L :=
              Finset.sum_le_sum_of_subset_of_nonneg hsubL (fun i _ _ => by rw [hfL]; positivity)
          _ = ∑ L ∈ BigL, (if L ∣ z.re.natAbs then fL L else 0) := Finset.sum_filter _ _
      have hDb : (∑ d ∈ ((Work.FIPlan.gnorm z).divisors.filter (fun d => d ^ 3 ≤ Work.FIPlan.gnorm z)), gL d)
          ≤ (∑ d ∈ Bigd, (if d ∣ Work.FIPlan.gnorm z then gL d else 0)) := by
        calc (∑ d ∈ ((Work.FIPlan.gnorm z).divisors.filter (fun d => d ^ 3 ≤ Work.FIPlan.gnorm z)), gL d)
            ≤ ∑ d ∈ Bigd.filter (fun d => d ∣ Work.FIPlan.gnorm z), gL d :=
              Finset.sum_le_sum_of_subset_of_nonneg hsubD (fun i _ _ => by rw [hgL]; positivity)
          _ = ∑ d ∈ Bigd, (if d ∣ Work.FIPlan.gnorm z then gL d else 0) := Finset.sum_filter _ _
      exact le_trans (mul_le_mul h1 h2 (by positivity) hinnerLnn)
        (mul_le_mul hLb hDb hinnerDnn (hsumLnn z))
  -- ## Step 2: swap the sums
  have hswap : (∑ z ∈ S, (∑ L ∈ BigL, (if L ∣ z.re.natAbs then fL L else 0))
          * (∑ d ∈ Bigd, (if d ∣ Work.FIPlan.gnorm z then gL d else 0)))
      = ∑ L ∈ BigL, ∑ d ∈ Bigd, fL L * gL d
          * (((S.filter (fun z => L ∣ z.re.natAbs ∧ d ∣ Work.FIPlan.gnorm z)).card : ℕ) : ℝ) := by
    have hpt : ∀ (L d : ℕ) (z : GaussianInt),
        (if L ∣ z.re.natAbs then fL L else 0) * (if d ∣ Work.FIPlan.gnorm z then gL d else 0)
          = fL L * gL d * (if (L ∣ z.re.natAbs ∧ d ∣ Work.FIPlan.gnorm z) then (1 : ℝ) else 0) := by
      intro L d z
      by_cases h1 : L ∣ z.re.natAbs <;> by_cases h2 : d ∣ Work.FIPlan.gnorm z <;> simp [h1, h2]
    calc (∑ z ∈ S, (∑ L ∈ BigL, (if L ∣ z.re.natAbs then fL L else 0))
            * (∑ d ∈ Bigd, (if d ∣ Work.FIPlan.gnorm z then gL d else 0)))
        = ∑ z ∈ S, ∑ L ∈ BigL, ∑ d ∈ Bigd,
            fL L * gL d * (if (L ∣ z.re.natAbs ∧ d ∣ Work.FIPlan.gnorm z) then (1 : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro z _
          rw [Finset.sum_mul_sum]
          apply Finset.sum_congr rfl; intro L _
          apply Finset.sum_congr rfl; intro d _
          exact hpt L d z
      _ = ∑ L ∈ BigL, ∑ d ∈ Bigd, ∑ z ∈ S,
            fL L * gL d * (if (L ∣ z.re.natAbs ∧ d ∣ Work.FIPlan.gnorm z) then (1 : ℝ) else 0) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro L _
          rw [Finset.sum_comm]
      _ = ∑ L ∈ BigL, ∑ d ∈ Bigd, fL L * gL d
            * (((S.filter (fun z => L ∣ z.re.natAbs ∧ d ∣ Work.FIPlan.gnorm z)).card : ℕ) : ℝ) := by
          apply Finset.sum_congr rfl; intro L _
          apply Finset.sum_congr rfl; intro d _
          rw [← Finset.mul_sum, Finset.sum_boole]
  have hmain : (∑ z ∈ S,
        ((z.re.natAbs.divisors.card : ℕ) : ℝ) ^ 3
          * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ^ 2)
      ≤ ∑ L ∈ BigL, ∑ d ∈ Bigd, fL L * gL d
          * (((S.filter (fun z => L ∣ z.re.natAbs ∧ d ∣ Work.FIPlan.gnorm z)).card : ℕ) : ℝ) :=
    le_trans (Finset.sum_le_sum hzstep) hswap.le
  -- ## Step 3: apply the joint count and factor
  have hcount_step : ∀ L ∈ BigL, ∀ d ∈ Bigd,
      (((S.filter (fun z => L ∣ z.re.natAbs ∧ d ∣ Work.FIPlan.gnorm z)).card : ℕ) : ℝ)
        ≤ C_A * (Aw / (d : ℝ) + 1) * (Aw / (L : ℝ) + 1)
            * (2 : ℝ) ^ (Nat.primeFactors d).card * ((S15d2 d : ℕ) : ℝ) := by
    intro L hL d hd
    have hL1 : 1 ≤ L := (Finset.mem_Icc.mp (Finset.mem_filter.mp hL).1).1
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
    rw [hS, hAw] at *
    exact hcount Pa φ L d hL1 hd1
  have hfac : (∑ L ∈ BigL, ∑ d ∈ Bigd, fL L * gL d
          * (((S.filter (fun z => L ∣ z.re.natAbs ∧ d ∣ Work.FIPlan.gnorm z)).card : ℕ) : ℝ))
      ≤ C_A * (∑ L ∈ BigL, fL L * (Aw / (L : ℝ) + 1))
          * (∑ d ∈ Bigd, gL d * ((Aw / (d : ℝ) + 1)
              * (2 : ℝ) ^ (Nat.primeFactors d).card * ((S15d2 d : ℕ) : ℝ))) := by
    rw [show C_A * (∑ L ∈ BigL, fL L * (Aw / (L : ℝ) + 1))
          * (∑ d ∈ Bigd, gL d * ((Aw / (d : ℝ) + 1)
              * (2 : ℝ) ^ (Nat.primeFactors d).card * ((S15d2 d : ℕ) : ℝ)))
        = ∑ L ∈ BigL, ∑ d ∈ Bigd, C_A * ((fL L * (Aw / (L : ℝ) + 1))
            * (gL d * ((Aw / (d : ℝ) + 1)
              * (2 : ℝ) ^ (Nat.primeFactors d).card * ((S15d2 d : ℕ) : ℝ)))) from by
      rw [show C_A * (∑ L ∈ BigL, fL L * (Aw / (L : ℝ) + 1))
            * (∑ d ∈ Bigd, gL d * ((Aw / (d : ℝ) + 1)
                * (2 : ℝ) ^ (Nat.primeFactors d).card * ((S15d2 d : ℕ) : ℝ)))
          = C_A * ((∑ L ∈ BigL, fL L * (Aw / (L : ℝ) + 1))
            * (∑ d ∈ Bigd, gL d * ((Aw / (d : ℝ) + 1)
                * (2 : ℝ) ^ (Nat.primeFactors d).card * ((S15d2 d : ℕ) : ℝ)))) from by ring]
      rw [Finset.sum_mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro L _
      rw [Finset.mul_sum]]
    apply Finset.sum_le_sum; intro L hL
    apply Finset.sum_le_sum; intro d hd
    calc fL L * gL d * (((S.filter (fun z => L ∣ z.re.natAbs ∧ d ∣ Work.FIPlan.gnorm z)).card : ℕ) : ℝ)
        ≤ fL L * gL d * (C_A * (Aw / (d : ℝ) + 1) * (Aw / (L : ℝ) + 1)
            * (2 : ℝ) ^ (Nat.primeFactors d).card * ((S15d2 d : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left (hcount_step L hL d hd) (by
            have h1 : 0 ≤ fL L := by rw [hfL]; positivity
            have h2 : 0 ≤ gL d := by rw [hgL]; positivity
            positivity)
      _ = C_A * ((fL L * (Aw / (L : ℝ) + 1)) * (gL d * ((Aw / (d : ℝ) + 1)
            * (2 : ℝ) ^ (Nat.primeFactors d).card * ((S15d2 d : ℕ) : ℝ)))) := by ring
  exact le_trans hmain hfac

/-- The bulk of the box-energy estimate: the two-factor bound for `Σ_{z ∈ box} τ(re z)³ τ(|z|²)²`. -/
lemma S15bea_stepA
    (C_A : ℝ) (hC_A : 0 < C_A)
    (hcount : ∀ (Pa : Work.FITop.Params) (φ : ℝ) (L d : ℕ), 1 ≤ L → 1 ≤ d →
      (((S15polarBox Pa φ).filter (fun z => L ∣ z.re.natAbs ∧ d ∣ Work.FIPlan.gnorm z)).card : ℝ)
        ≤ C_A * ((10 * Pa.θ * Real.sqrt Pa.N) / (d : ℝ) + 1)
            * ((10 * Pa.θ * Real.sqrt Pa.N) / (L : ℝ) + 1)
            * (2 : ℝ) ^ (Nat.primeFactors d).card * ((S15d2 d : ℕ) : ℝ))
    (C_2 B : ℝ) (hC_2 : 0 < C_2) (hB : B ≤ 900000)
    (hsum : ∀ Y : ℕ, (∑ d ∈ Finset.Icc 1 Y,
          ((d.divisors.card : ℝ) ^ (10 : ℕ)) * (2 : ℝ) ^ (Nat.primeFactors d).card
            * ((S15d2 d : ℕ) : ℝ) / (d : ℝ))
        ≤ C_2 * (Real.log ((Y : ℝ) + 2)) ^ B)
    (C_1 : ℝ) (hC_1pos : 0 < C_1)
    (hC_1 : ∀ y : ℕ, 1 ≤ y → (∑ d ∈ Finset.Icc 1 y,
          ((((d.divisors.card : ℕ) : ℝ)) ^ 6 / (d : ℝ)))
        ≤ C_1 * (Real.log ((y : ℝ) + 2)) ^ (2 ^ 6))
    (Pa : Work.FITop.Params) (φ : ℝ) :
    (∑ z ∈ S15polarBox Pa φ,
        ((z.re.natAbs.divisors.card : ℕ) : ℝ) ^ 3
          * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ^ 2)
      ≤ C_A * (2 ^ 6 * (C_1 * (Real.log ((((⌈2 * Pa.N⌉₊ : ℕ)) : ℝ) + 2)) ^ (2 ^ 6))
            * (10 * Pa.θ * Real.sqrt Pa.N + (⌈2 * Pa.N⌉₊ : ℝ) ^ (1 / 4 : ℝ)))
        * (2 ^ 10 * (C_2 * (Real.log ((((⌈2 * Pa.N⌉₊ : ℕ)) : ℝ) + 2)) ^ B)
            * (10 * Pa.θ * Real.sqrt Pa.N + (⌈2 * Pa.N⌉₊ : ℝ) ^ (1 / 3 : ℝ))) := by
  have hθ0 : 0 < Pa.θ := Pa.hθ0
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  have hKpos : 0 < ⌈2 * Pa.N⌉₊ := by
    have h : (1 : ℝ) ≤ 2 * Pa.N := by linarith
    have h2 : (1 : ℝ) ≤ (((⌈2 * Pa.N⌉₊ : ℕ)) : ℝ) := le_trans h (Nat.le_ceil (2 * Pa.N))
    exact_mod_cast h2
  have hK1 : 1 ≤ ⌈2 * Pa.N⌉₊ := hKpos
  have hAw0 : 0 ≤ 10 * Pa.θ * Real.sqrt Pa.N :=
    mul_nonneg (mul_nonneg (by norm_num) hθ0.le) (Real.sqrt_nonneg Pa.N)
  have hnb := S15bea_main_bound C_A hC_A hcount Pa φ
  have hF1 := S15bea_L_bound C_1 hC_1pos hC_1 ⌈2 * Pa.N⌉₊ hK1 (10 * Pa.θ * Real.sqrt Pa.N) hAw0
  have hF2 := S15bea_D_bound C_2 B hC_2 hsum ⌈2 * Pa.N⌉₊ hK1 (10 * Pa.θ * Real.sqrt Pa.N) hAw0
  have hFF : C_A * ((∑ L ∈ (Finset.Icc 1 ⌈2 * Pa.N⌉₊).filter (fun L => L ^ 4 ≤ ⌈2 * Pa.N⌉₊),
            (2 * ((L.divisors.card : ℕ) : ℝ)) ^ 6 * (10 * Pa.θ * Real.sqrt Pa.N / (L : ℝ) + 1)))
        * ((∑ d ∈ (Finset.Icc 1 ⌈2 * Pa.N⌉₊).filter (fun d => d ^ 3 ≤ ⌈2 * Pa.N⌉₊),
            (2 * ((d.divisors.card : ℕ) : ℝ)) ^ 10 * ((10 * Pa.θ * Real.sqrt Pa.N / (d : ℝ) + 1)
              * (2 : ℝ) ^ (Nat.primeFactors d).card * ((S15d2 d : ℕ) : ℝ))))
      ≤ C_A * (2 ^ 6 * (C_1 * (Real.log ((((⌈2 * Pa.N⌉₊ : ℕ)) : ℝ) + 2)) ^ (2 ^ 6))
            * (10 * Pa.θ * Real.sqrt Pa.N + (⌈2 * Pa.N⌉₊ : ℝ) ^ (1 / 4 : ℝ)))
        * (2 ^ 10 * (C_2 * (Real.log ((((⌈2 * Pa.N⌉₊ : ℕ)) : ℝ) + 2)) ^ B)
            * (10 * Pa.θ * Real.sqrt Pa.N + (⌈2 * Pa.N⌉₊ : ℝ) ^ (1 / 3 : ℝ))) := by
    have hK2 : (1 : ℝ) ≤ (((⌈2 * Pa.N⌉₊ : ℕ)) : ℝ) + 2 := by
      have h1 : (1 : ℝ) ≤ (((⌈2 * Pa.N⌉₊ : ℕ)) : ℝ) := by exact_mod_cast hK1
      linarith
    have hL2nn : 0 ≤ (∑ d ∈ (Finset.Icc 1 ⌈2 * Pa.N⌉₊).filter (fun d => d ^ 3 ≤ ⌈2 * Pa.N⌉₊),
            (2 * ((d.divisors.card : ℕ) : ℝ)) ^ 10 * ((10 * Pa.θ * Real.sqrt Pa.N / (d : ℝ) + 1)
              * (2 : ℝ) ^ (Nat.primeFactors d).card * ((S15d2 d : ℕ) : ℝ))) := by
      apply Finset.sum_nonneg
      intro d _
      have h1 : (0 : ℝ) ≤ 10 * Pa.θ * Real.sqrt Pa.N / (d : ℝ) + 1 := by
        have h2 : 0 ≤ 10 * Pa.θ * Real.sqrt Pa.N / (d : ℝ) :=
          div_nonneg hAw0 (Nat.cast_nonneg d)
        linarith
      have h3 : (0 : ℝ) ≤ (2 : ℝ) ^ (Nat.primeFactors d).card := by positivity
      have h4 : (0 : ℝ) ≤ ((S15d2 d : ℕ) : ℝ) := Nat.cast_nonneg _
      have h5 : (0 : ℝ) ≤ (2 * ((d.divisors.card : ℕ) : ℝ)) ^ 10 := by positivity
      exact mul_nonneg h5 (mul_nonneg (mul_nonneg h1 h3) h4)
    have hB1nn : 0 ≤ 2 ^ 6 * (C_1 * (Real.log ((((⌈2 * Pa.N⌉₊ : ℕ)) : ℝ) + 2)) ^ (2 ^ 6))
            * (10 * Pa.θ * Real.sqrt Pa.N + (⌈2 * Pa.N⌉₊ : ℝ) ^ (1 / 4 : ℝ)) := by
      apply mul_nonneg
      · apply mul_nonneg (by norm_num)
        apply mul_nonneg hC_1pos.le
        have hL0 : 0 ≤ Real.log ((((⌈2 * Pa.N⌉₊ : ℕ)) : ℝ) + 2) := Real.log_nonneg hK2
        positivity
      · have h5 : (0 : ℝ) ≤ (⌈2 * Pa.N⌉₊ : ℝ) ^ (1 / 4 : ℝ) :=
          Real.rpow_nonneg (Nat.cast_nonneg _) _
        linarith
    have hprod := mul_le_mul hF1 hF2 hL2nn hB1nn
    have hCA' := mul_le_mul_of_nonneg_left hprod hC_A.le
    calc C_A * ((∑ L ∈ (Finset.Icc 1 ⌈2 * Pa.N⌉₊).filter (fun L => L ^ 4 ≤ ⌈2 * Pa.N⌉₊),
            (2 * ((L.divisors.card : ℕ) : ℝ)) ^ 6 * (10 * Pa.θ * Real.sqrt Pa.N / (L : ℝ) + 1)))
          * ((∑ d ∈ (Finset.Icc 1 ⌈2 * Pa.N⌉₊).filter (fun d => d ^ 3 ≤ ⌈2 * Pa.N⌉₊),
            (2 * ((d.divisors.card : ℕ) : ℝ)) ^ 10 * ((10 * Pa.θ * Real.sqrt Pa.N / (d : ℝ) + 1)
              * (2 : ℝ) ^ (Nat.primeFactors d).card * ((S15d2 d : ℕ) : ℝ))))
        = C_A * (((∑ L ∈ (Finset.Icc 1 ⌈2 * Pa.N⌉₊).filter (fun L => L ^ 4 ≤ ⌈2 * Pa.N⌉₊),
            (2 * ((L.divisors.card : ℕ) : ℝ)) ^ 6 * (10 * Pa.θ * Real.sqrt Pa.N / (L : ℝ) + 1)))
          * ((∑ d ∈ (Finset.Icc 1 ⌈2 * Pa.N⌉₊).filter (fun d => d ^ 3 ≤ ⌈2 * Pa.N⌉₊),
            (2 * ((d.divisors.card : ℕ) : ℝ)) ^ 10 * ((10 * Pa.θ * Real.sqrt Pa.N / (d : ℝ) + 1)
              * (2 : ℝ) ^ (Nat.primeFactors d).card * ((S15d2 d : ℕ) : ℝ))))) := by ring
      _ ≤ C_A * ((2 ^ 6 * (C_1 * (Real.log ((((⌈2 * Pa.N⌉₊ : ℕ)) : ℝ) + 2)) ^ (2 ^ 6))
            * (10 * Pa.θ * Real.sqrt Pa.N + (⌈2 * Pa.N⌉₊ : ℝ) ^ (1 / 4 : ℝ)))
          * (2 ^ 10 * (C_2 * (Real.log ((((⌈2 * Pa.N⌉₊ : ℕ)) : ℝ) + 2)) ^ B)
            * (10 * Pa.θ * Real.sqrt Pa.N + (⌈2 * Pa.N⌉₊ : ℝ) ^ (1 / 3 : ℝ)))) := hCA'
      _ = C_A * (2 ^ 6 * (C_1 * (Real.log ((((⌈2 * Pa.N⌉₊ : ℕ)) : ℝ) + 2)) ^ (2 ^ 6))
            * (10 * Pa.θ * Real.sqrt Pa.N + (⌈2 * Pa.N⌉₊ : ℝ) ^ (1 / 4 : ℝ)))
          * (2 ^ 10 * (C_2 * (Real.log ((((⌈2 * Pa.N⌉₊ : ℕ)) : ℝ) + 2)) ^ B)
            * (10 * Pa.θ * Real.sqrt Pa.N + (⌈2 * Pa.N⌉₊ : ℝ) ^ (1 / 3 : ℝ))) := by ring
  calc (∑ z ∈ S15polarBox Pa φ,
        ((z.re.natAbs.divisors.card : ℕ) : ℝ) ^ 3
          * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ^ 2)
      ≤ C_A * ((∑ L ∈ (Finset.Icc 1 ⌈2 * Pa.N⌉₊).filter (fun L => L ^ 4 ≤ ⌈2 * Pa.N⌉₊),
            (2 * ((L.divisors.card : ℕ) : ℝ)) ^ 6 * (10 * Pa.θ * Real.sqrt Pa.N / (L : ℝ) + 1)))
          * ((∑ d ∈ (Finset.Icc 1 ⌈2 * Pa.N⌉₊).filter (fun d => d ^ 3 ≤ ⌈2 * Pa.N⌉₊),
            (2 * ((d.divisors.card : ℕ) : ℝ)) ^ 10 * ((10 * Pa.θ * Real.sqrt Pa.N / (d : ℝ) + 1)
              * (2 : ℝ) ^ (Nat.primeFactors d).card * ((S15d2 d : ℕ) : ℝ)))) := hnb
    _ ≤ C_A * (2 ^ 6 * (C_1 * (Real.log ((((⌈2 * Pa.N⌉₊ : ℕ)) : ℝ) + 2)) ^ (2 ^ 6))
            * (10 * Pa.θ * Real.sqrt Pa.N + (⌈2 * Pa.N⌉₊ : ℝ) ^ (1 / 4 : ℝ)))
          * (2 ^ 10 * (C_2 * (Real.log ((((⌈2 * Pa.N⌉₊ : ℕ)) : ℝ) + 2)) ^ B)
            * (10 * Pa.θ * Real.sqrt Pa.N + (⌈2 * Pa.N⌉₊ : ℝ) ^ (1 / 3 : ℝ))) := hFF
end

end Work.FIArea4
