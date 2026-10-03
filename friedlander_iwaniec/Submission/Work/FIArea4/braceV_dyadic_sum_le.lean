import Mathlib
import Submission.Work.FIArea4.prop_11_1_defs
import Submission.Work.FIArea4.sum_rpow_two_pow_le

set_option maxHeartbeats 1000000

namespace Work.FIArea4

open Finset
open scoped BigOperators

/-- `√4 = 2`. -/
lemma sqrt_four : Real.sqrt (4:ℝ) = 2 := by
  rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- Per-term bound used in the dyadic summation `braceV_dyadic_sum_le`.
The exponent `ε` of `(2^(j+k))^ε` is replaced by the constant `(4RS)^ε` (legitimate since
`2^(j+k) = 2^j·2^k ≤ 4RS` when `2^j ≤ 2R`, `2^k ≤ 2S` and `ε ≥ 0`), and the square root
`√(2^j·2^k)` is split as `(2^j)^(1/2)·(2^k)^(1/2)`, so that each of the four summands is a
product of a function of `j` times a function of `k`. -/
lemma braceV_dyadic_term_le (D R S j k : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hj : (2:ℝ)^j ≤ 2*(R:ℝ)) (hk : (2:ℝ)^k ≤ 2*(S:ℝ)) :
    braceV D ((2:ℕ)^j) ((2:ℕ)^k) ε
      ≤ ((D:ℝ)^(-(1:ℝ)/2) * (2:ℝ)^j) * (2:ℝ)^k
        + ((4*(R:ℝ)*(S:ℝ))^ε * ((D:ℝ) * ((2:ℝ)^j)^((1:ℝ)/2))) * ((2:ℝ)^k)^((1:ℝ)/2)
        + ((4*(R:ℝ)*(S:ℝ))^ε * (2:ℝ)^j) * ((2:ℝ)^k)^((3:ℝ)/4)
        + ((4*(R:ℝ)*(S:ℝ))^ε * ((2:ℝ)^j)^((3:ℝ)/4)) * (2:ℝ)^k := by
  have hle : ((2:ℝ)^j * (2:ℝ)^k)^ε ≤ (4*(R:ℝ)*(S:ℝ))^ε := by
    rw [← pow_add]
    refine Real.rpow_le_rpow (by positivity) ?_ hε
    calc (2:ℝ)^(j+k) = (2:ℝ)^j * (2:ℝ)^k := by rw [pow_add]
      _ ≤ (2*(R:ℝ)) * (2*(S:ℝ)) := mul_le_mul hj hk (by positivity) (by positivity)
      _ = 4*(R:ℝ)*(S:ℝ) := by ring
  have hsqrt : Real.sqrt ((2:ℝ)^j * (2:ℝ)^k)
      = ((2:ℝ)^j)^((1:ℝ)/2) * ((2:ℝ)^k)^((1:ℝ)/2) := by
    rw [Real.sqrt_eq_rpow, Real.mul_rpow (by positivity) (by positivity)]
  have hb1 : (D:ℝ) * (((2:ℝ)^j)^((1:ℝ)/2) * ((2:ℝ)^k)^((1:ℝ)/2))
        * (((2:ℝ)^j * (2:ℝ)^k)^ε)
      ≤ ((4*(R:ℝ)*(S:ℝ))^ε * ((D:ℝ) * ((2:ℝ)^j)^((1:ℝ)/2))) * ((2:ℝ)^k)^((1:ℝ)/2) := by
    calc (D:ℝ) * (((2:ℝ)^j)^((1:ℝ)/2) * ((2:ℝ)^k)^((1:ℝ)/2)) * (((2:ℝ)^j * (2:ℝ)^k)^ε)
        ≤ (D:ℝ) * (((2:ℝ)^j)^((1:ℝ)/2) * ((2:ℝ)^k)^((1:ℝ)/2)) * (4*(R:ℝ)*(S:ℝ))^ε :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = ((4*(R:ℝ)*(S:ℝ))^ε * ((D:ℝ) * ((2:ℝ)^j)^((1:ℝ)/2))) * ((2:ℝ)^k)^((1:ℝ)/2) := by
          ring
  have hb2 : (2:ℝ)^j * ((2:ℝ)^k)^((3:ℝ)/4) * (((2:ℝ)^j * (2:ℝ)^k)^ε)
      ≤ ((4*(R:ℝ)*(S:ℝ))^ε * (2:ℝ)^j) * ((2:ℝ)^k)^((3:ℝ)/4) := by
    calc (2:ℝ)^j * ((2:ℝ)^k)^((3:ℝ)/4) * (((2:ℝ)^j * (2:ℝ)^k)^ε)
        ≤ (2:ℝ)^j * ((2:ℝ)^k)^((3:ℝ)/4) * (4*(R:ℝ)*(S:ℝ))^ε :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = ((4*(R:ℝ)*(S:ℝ))^ε * (2:ℝ)^j) * ((2:ℝ)^k)^((3:ℝ)/4) := by ring
  have hb3 : (2:ℝ)^k * ((2:ℝ)^j)^((3:ℝ)/4) * (((2:ℝ)^j * (2:ℝ)^k)^ε)
      ≤ ((4*(R:ℝ)*(S:ℝ))^ε * ((2:ℝ)^j)^((3:ℝ)/4)) * (2:ℝ)^k := by
    calc (2:ℝ)^k * ((2:ℝ)^j)^((3:ℝ)/4) * (((2:ℝ)^j * (2:ℝ)^k)^ε)
        ≤ (2:ℝ)^k * ((2:ℝ)^j)^((3:ℝ)/4) * (4*(R:ℝ)*(S:ℝ))^ε :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = ((4*(R:ℝ)*(S:ℝ))^ε * ((2:ℝ)^j)^((3:ℝ)/4)) * (2:ℝ)^k := by ring
  simp only [braceV, Nat.cast_pow, Nat.cast_ofNat]
  rw [hsqrt, add_mul, add_mul]
  linarith [hb1, hb2, hb3]

lemma braceV_dyadic_sum_le (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D R S JR JS : ℕ), 1 ≤ D → 1 ≤ R → 1 ≤ S →
        (2:ℕ)^JR ≤ 2*R → (2:ℕ)^JS ≤ 2*S →
        (∑ j ∈ Finset.range (JR+1), ∑ k ∈ Finset.range (JS+1),
          Work.FIArea4.braceV D ((2:ℕ)^j) ((2:ℕ)^k) ε)
          ≤ C * Work.FIArea4.braceV D R S ε := by
  have hε0 : (0:ℝ) ≤ ε := hε.le
  set c12 : ℝ := (2:ℝ)^((1:ℝ)/2) / ((2:ℝ)^((1:ℝ)/2) - 1) with hc12
  set c34 : ℝ := (2:ℝ)^((3:ℝ)/4) / ((2:ℝ)^((3:ℝ)/4) - 1) with hc34
  have hc12pos : 0 < c12 := by
    rw [hc12]
    exact div_pos (by positivity)
      (by linarith [Real.one_lt_rpow (show (1:ℝ) < 2 by norm_num) (show (0:ℝ) < (1:ℝ)/2 by norm_num)])
  have hc34pos : 0 < c34 := by
    rw [hc34]
    exact div_pos (by positivity)
      (by linarith [Real.one_lt_rpow (show (1:ℝ) < 2 by norm_num) (show (0:ℝ) < (3:ℝ)/4 by norm_num)])
  have h2qpos : (0:ℝ) < (2:ℝ)^((3:ℝ)/4) := Real.rpow_pos_of_pos (by norm_num) _
  have h4pos : (0:ℝ) < (4:ℝ)^ε := Real.rpow_pos_of_pos (by norm_num) ε
  refine ⟨16 + 2*c12^2*(4:ℝ)^ε + 2*(4*c34*(2:ℝ)^((3:ℝ)/4)*(4:ℝ)^ε), ?_, ?_⟩
  · have hk2 : (0:ℝ) ≤ 2*c12^2*(4:ℝ)^ε :=
      mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg c12)) h4pos.le
    have hk3 : (0:ℝ) ≤ 4*c34*(2:ℝ)^((3:ℝ)/4)*(4:ℝ)^ε :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hc34pos.le) h2qpos.le) h4pos.le
    linarith
  · intro D R S JR JS hD hR hS hJR hJS
    have hJR' : (2:ℝ)^JR ≤ 2*(R:ℝ) := by
      have h1 : ((2:ℕ)^JR : ℝ) ≤ ((2*R : ℕ) : ℝ) := by exact_mod_cast hJR
      simpa [Nat.cast_pow] using h1
    have hJS' : (2:ℝ)^JS ≤ 2*(S:ℝ) := by
      have h1 : ((2:ℕ)^JS : ℝ) ≤ ((2*S : ℕ) : ℝ) := by exact_mod_cast hJS
      simpa [Nat.cast_pow] using h1
    set Fj1 : ℝ := ∑ j ∈ Finset.range (JR+1), (2:ℝ)^j with hFj1
    set Fj2 : ℝ := ∑ j ∈ Finset.range (JR+1), ((2:ℝ)^j)^((1:ℝ)/2) with hFj2
    set Fj3 : ℝ := ∑ j ∈ Finset.range (JR+1), ((2:ℝ)^j)^((3:ℝ)/4) with hFj3
    set Fk1 : ℝ := ∑ k ∈ Finset.range (JS+1), (2:ℝ)^k with hFk1
    set Fk2 : ℝ := ∑ k ∈ Finset.range (JS+1), ((2:ℝ)^k)^((1:ℝ)/2) with hFk2
    set Fk3 : ℝ := ∑ k ∈ Finset.range (JS+1), ((2:ℝ)^k)^((3:ℝ)/4) with hFk3
    set T1 : ℝ := (D:ℝ)^(-(1:ℝ)/2) * (R:ℝ) * (S:ℝ) with hT1
    set T2 : ℝ := (D:ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ)) * (((R:ℝ)*(S:ℝ))^ε) with hT2
    set T3 : ℝ := (R:ℝ) * (S:ℝ)^((3:ℝ)/4) * (((R:ℝ)*(S:ℝ))^ε) with hT3
    set T4 : ℝ := (S:ℝ) * (R:ℝ)^((3:ℝ)/4) * (((R:ℝ)*(S:ℝ))^ε) with hT4
    -- the four dyadic sum bounds
    have hsum1j : Fj1 ≤ 4*(R:ℝ) := by
      rw [hFj1]
      calc (∑ j ∈ Finset.range (JR+1), (2:ℝ)^j)
          = ∑ j ∈ Finset.range (JR+1), ((2:ℝ)^j)^(1:ℝ) := by simp
        _ ≤ ((2:ℝ)^(1:ℝ) / ((2:ℝ)^(1:ℝ) - 1)) * (2*(R:ℝ))^(1:ℝ) :=
              sum_rpow_two_pow_le 1 (by norm_num) JR R hJR'
        _ = 4*(R:ℝ) := by rw [Real.rpow_one, Real.rpow_one]; ring
    have hsum2j : Fj2 ≤ c12 * (2*(R:ℝ))^((1:ℝ)/2) := by
      rw [hFj2, hc12]
      exact sum_rpow_two_pow_le ((1:ℝ)/2) (by norm_num) JR R hJR'
    have hsum3j : Fj3 ≤ c34 * (2*(R:ℝ))^((3:ℝ)/4) := by
      rw [hFj3, hc34]
      exact sum_rpow_two_pow_le ((3:ℝ)/4) (by norm_num) JR R hJR'
    have hsum1k : Fk1 ≤ 4*(S:ℝ) := by
      rw [hFk1]
      calc (∑ k ∈ Finset.range (JS+1), (2:ℝ)^k)
          = ∑ k ∈ Finset.range (JS+1), ((2:ℝ)^k)^(1:ℝ) := by simp
        _ ≤ ((2:ℝ)^(1:ℝ) / ((2:ℝ)^(1:ℝ) - 1)) * (2*(S:ℝ))^(1:ℝ) :=
              sum_rpow_two_pow_le 1 (by norm_num) JS S hJS'
        _ = 4*(S:ℝ) := by rw [Real.rpow_one, Real.rpow_one]; ring
    have hsum2k : Fk2 ≤ c12 * (2*(S:ℝ))^((1:ℝ)/2) := by
      rw [hFk2, hc12]
      exact sum_rpow_two_pow_le ((1:ℝ)/2) (by norm_num) JS S hJS'
    have hsum3k : Fk3 ≤ c34 * (2*(S:ℝ))^((3:ℝ)/4) := by
      rw [hFk3, hc34]
      exact sum_rpow_two_pow_le ((3:ℝ)/4) (by norm_num) JS S hJS'
    have hbrace : braceV D R S ε = T1 + T2 + T3 + T4 := by
      simp only [hT1, hT2, hT3, hT4, braceV]
      ring
    -- the per-term bound
    have hstep : (∑ j ∈ Finset.range (JR+1), ∑ k ∈ Finset.range (JS+1),
          braceV D ((2:ℕ)^j) ((2:ℕ)^k) ε)
        ≤ ∑ j ∈ Finset.range (JR+1), ∑ k ∈ Finset.range (JS+1),
            (((D:ℝ)^(-(1:ℝ)/2) * (2:ℝ)^j) * (2:ℝ)^k
              + ((4*(R:ℝ)*(S:ℝ))^ε * ((D:ℝ) * ((2:ℝ)^j)^((1:ℝ)/2))) * ((2:ℝ)^k)^((1:ℝ)/2)
              + ((4*(R:ℝ)*(S:ℝ))^ε * (2:ℝ)^j) * ((2:ℝ)^k)^((3:ℝ)/4)
              + ((4*(R:ℝ)*(S:ℝ))^ε * ((2:ℝ)^j)^((3:ℝ)/4)) * (2:ℝ)^k) := by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro k hk
      have hj1 : (2:ℝ)^j ≤ 2*(R:ℝ) := by
        have hjle : j ≤ JR := by
          simp only [Finset.mem_range] at hj
          omega
        calc (2:ℝ)^j ≤ (2:ℝ)^JR := pow_le_pow_right₀ (by norm_num) hjle
          _ ≤ 2*(R:ℝ) := hJR'
      have hk1 : (2:ℝ)^k ≤ 2*(S:ℝ) := by
        have hkle : k ≤ JS := by
          simp only [Finset.mem_range] at hk
          omega
        calc (2:ℝ)^k ≤ (2:ℝ)^JS := pow_le_pow_right₀ (by norm_num) hkle
          _ ≤ 2*(S:ℝ) := hJS'
      exact braceV_dyadic_term_le D R S j k ε hε0 hj1 hk1
    -- factorization of each of the four double sums
    have hA : (∑ j ∈ Finset.range (JR+1), ∑ k ∈ Finset.range (JS+1),
          ((D:ℝ)^(-(1:ℝ)/2) * (2:ℝ)^j) * (2:ℝ)^k)
        = (∑ j ∈ Finset.range (JR+1), (D:ℝ)^(-(1:ℝ)/2) * (2:ℝ)^j)
            * (∑ k ∈ Finset.range (JS+1), (2:ℝ)^k) :=
      (Finset.sum_mul_sum (Finset.range (JR+1)) (Finset.range (JS+1))
        (fun j => (D:ℝ)^(-(1:ℝ)/2) * (2:ℝ)^j) (fun k => (2:ℝ)^k)).symm
    have hB : (∑ j ∈ Finset.range (JR+1), ∑ k ∈ Finset.range (JS+1),
          ((4*(R:ℝ)*(S:ℝ))^ε * ((D:ℝ) * ((2:ℝ)^j)^((1:ℝ)/2))) * ((2:ℝ)^k)^((1:ℝ)/2))
        = (∑ j ∈ Finset.range (JR+1), (4*(R:ℝ)*(S:ℝ))^ε * ((D:ℝ) * ((2:ℝ)^j)^((1:ℝ)/2)))
            * (∑ k ∈ Finset.range (JS+1), ((2:ℝ)^k)^((1:ℝ)/2)) :=
      (Finset.sum_mul_sum (Finset.range (JR+1)) (Finset.range (JS+1))
        (fun j => (4*(R:ℝ)*(S:ℝ))^ε * ((D:ℝ) * ((2:ℝ)^j)^((1:ℝ)/2)))
        (fun k => ((2:ℝ)^k)^((1:ℝ)/2))).symm
    have hC : (∑ j ∈ Finset.range (JR+1), ∑ k ∈ Finset.range (JS+1),
          ((4*(R:ℝ)*(S:ℝ))^ε * (2:ℝ)^j) * ((2:ℝ)^k)^((3:ℝ)/4))
        = (∑ j ∈ Finset.range (JR+1), (4*(R:ℝ)*(S:ℝ))^ε * (2:ℝ)^j)
            * (∑ k ∈ Finset.range (JS+1), ((2:ℝ)^k)^((3:ℝ)/4)) :=
      (Finset.sum_mul_sum (Finset.range (JR+1)) (Finset.range (JS+1))
        (fun j => (4*(R:ℝ)*(S:ℝ))^ε * (2:ℝ)^j) (fun k => ((2:ℝ)^k)^((3:ℝ)/4))).symm
    have hD' : (∑ j ∈ Finset.range (JR+1), ∑ k ∈ Finset.range (JS+1),
          ((4*(R:ℝ)*(S:ℝ))^ε * ((2:ℝ)^j)^((3:ℝ)/4)) * (2:ℝ)^k)
        = (∑ j ∈ Finset.range (JR+1), (4*(R:ℝ)*(S:ℝ))^ε * ((2:ℝ)^j)^((3:ℝ)/4))
            * (∑ k ∈ Finset.range (JS+1), (2:ℝ)^k) :=
      (Finset.sum_mul_sum (Finset.range (JR+1)) (Finset.range (JS+1))
        (fun j => (4*(R:ℝ)*(S:ℝ))^ε * ((2:ℝ)^j)^((3:ℝ)/4)) (fun k => (2:ℝ)^k)).symm
    have hfac : (∑ j ∈ Finset.range (JR+1), ∑ k ∈ Finset.range (JS+1),
            (((D:ℝ)^(-(1:ℝ)/2) * (2:ℝ)^j) * (2:ℝ)^k
              + ((4*(R:ℝ)*(S:ℝ))^ε * ((D:ℝ) * ((2:ℝ)^j)^((1:ℝ)/2))) * ((2:ℝ)^k)^((1:ℝ)/2)
              + ((4*(R:ℝ)*(S:ℝ))^ε * (2:ℝ)^j) * ((2:ℝ)^k)^((3:ℝ)/4)
              + ((4*(R:ℝ)*(S:ℝ))^ε * ((2:ℝ)^j)^((3:ℝ)/4)) * (2:ℝ)^k))
        = (∑ j ∈ Finset.range (JR+1), (D:ℝ)^(-(1:ℝ)/2) * (2:ℝ)^j)
            * (∑ k ∈ Finset.range (JS+1), (2:ℝ)^k)
          + (∑ j ∈ Finset.range (JR+1), (4*(R:ℝ)*(S:ℝ))^ε * ((D:ℝ) * ((2:ℝ)^j)^((1:ℝ)/2)))
            * (∑ k ∈ Finset.range (JS+1), ((2:ℝ)^k)^((1:ℝ)/2))
          + (∑ j ∈ Finset.range (JR+1), (4*(R:ℝ)*(S:ℝ))^ε * (2:ℝ)^j)
            * (∑ k ∈ Finset.range (JS+1), ((2:ℝ)^k)^((3:ℝ)/4))
          + (∑ j ∈ Finset.range (JR+1), (4*(R:ℝ)*(S:ℝ))^ε * ((2:ℝ)^j)^((3:ℝ)/4))
            * (∑ k ∈ Finset.range (JS+1), (2:ℝ)^k) := by
      rw [← hA, ← hB, ← hC, ← hD']
      simp only [Finset.sum_add_distrib]
    -- bounds on the four products
    have hbj : (∑ j ∈ Finset.range (JR+1), (D:ℝ)^(-(1:ℝ)/2) * (2:ℝ)^j)
        = (D:ℝ)^(-(1:ℝ)/2) * Fj1 := by
      rw [hFj1]
      exact (Finset.mul_sum _ _ _).symm
    have hbk : (∑ k ∈ Finset.range (JS+1), (2:ℝ)^k) = Fk1 := hFk1
    have hb1 : (∑ j ∈ Finset.range (JR+1), (D:ℝ)^(-(1:ℝ)/2) * (2:ℝ)^j)
          * (∑ k ∈ Finset.range (JS+1), (2:ℝ)^k) ≤ 16*T1 := by
      rw [hbj, hbk, hT1]
      have hnn1 : (0:ℝ) ≤ Fj1 := by rw [hFj1]; exact Finset.sum_nonneg (fun j _ => by positivity)
      have hnn2 : (0:ℝ) ≤ Fk1 := by rw [hFk1]; exact Finset.sum_nonneg (fun k _ => by positivity)
      have hc : (0:ℝ) ≤ (D:ℝ)^(-(1:ℝ)/2) := Real.rpow_nonneg (Nat.cast_nonneg D) _
      calc (D:ℝ)^(-(1:ℝ)/2) * Fj1 * Fk1
          = (D:ℝ)^(-(1:ℝ)/2) * (Fj1 * Fk1) := by ring
        _ ≤ (D:ℝ)^(-(1:ℝ)/2) * ((4*(R:ℝ)) * (4*(S:ℝ))) := by
              refine mul_le_mul_of_nonneg_left ?_ hc
              exact mul_le_mul hsum1j hsum1k hnn2 (by positivity)
        _ = 16 * ((D:ℝ)^(-(1:ℝ)/2) * (R:ℝ) * (S:ℝ)) := by ring
    have hBj : (∑ j ∈ Finset.range (JR+1), (4*(R:ℝ)*(S:ℝ))^ε * ((D:ℝ) * ((2:ℝ)^j)^((1:ℝ)/2)))
        = (4*(R:ℝ)*(S:ℝ))^ε * ((D:ℝ) * Fj2) := by
      rw [hFj2]
      calc (∑ j ∈ Finset.range (JR+1), (4*(R:ℝ)*(S:ℝ))^ε * ((D:ℝ) * ((2:ℝ)^j)^((1:ℝ)/2)))
          = (4*(R:ℝ)*(S:ℝ))^ε
              * (∑ j ∈ Finset.range (JR+1), (D:ℝ) * ((2:ℝ)^j)^((1:ℝ)/2)) :=
            (Finset.mul_sum _ _ _).symm
        _ = (4*(R:ℝ)*(S:ℝ))^ε
              * ((D:ℝ) * (∑ j ∈ Finset.range (JR+1), ((2:ℝ)^j)^((1:ℝ)/2))) :=
            congrArg (fun z => (4*(R:ℝ)*(S:ℝ))^ε * z) (Finset.mul_sum _ _ _).symm
    have hb2 : (∑ j ∈ Finset.range (JR+1), (4*(R:ℝ)*(S:ℝ))^ε * ((D:ℝ) * ((2:ℝ)^j)^((1:ℝ)/2)))
          * (∑ k ∈ Finset.range (JS+1), ((2:ℝ)^k)^((1:ℝ)/2)) ≤ 2*c12^2*(4:ℝ)^ε*T2 := by
      rw [hBj, ← hFk2, hT2]
      have hY0 : (0:ℝ) ≤ (4*(R:ℝ)*(S:ℝ))^ε := Real.rpow_nonneg (by positivity) ε
      have hnnk : (0:ℝ) ≤ Fk2 := by rw [hFk2]; exact Finset.sum_nonneg (fun k _ => by positivity)
      have hD0 : (0:ℝ) ≤ (D:ℝ) := Nat.cast_nonneg D
      have hmono : ((D:ℝ) * Fj2) * Fk2
          ≤ ((D:ℝ) * (c12 * (2*(R:ℝ))^((1:ℝ)/2))) * (c12 * (2*(S:ℝ))^((1:ℝ)/2)) := by
        have h1 : (D:ℝ) * Fj2 ≤ (D:ℝ) * (c12 * (2*(R:ℝ))^((1:ℝ)/2)) :=
          mul_le_mul_of_nonneg_left hsum2j hD0
        exact mul_le_mul h1 hsum2k hnnk (mul_nonneg hD0 (mul_nonneg hc12pos.le (by positivity)))
      have hsq2 : ((2*(R:ℝ))^((1:ℝ)/2)) * ((2*(S:ℝ))^((1:ℝ)/2))
          = 2 * Real.sqrt ((R:ℝ)*(S:ℝ)) := by
        rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
          ← Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2*(R:ℝ)),
          show (2*(R:ℝ))*(2*(S:ℝ)) = 4*((R:ℝ)*(S:ℝ)) by ring,
          Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4), sqrt_four]
      have hmono2 : (4*(R:ℝ)*(S:ℝ))^ε * (((D:ℝ) * Fj2) * Fk2)
          ≤ (4*(R:ℝ)*(S:ℝ))^ε
              * (((D:ℝ) * (c12 * (2*(R:ℝ))^((1:ℝ)/2))) * (c12 * (2*(S:ℝ))^((1:ℝ)/2))) :=
        mul_le_mul_of_nonneg_left hmono hY0
      calc (4*(R:ℝ)*(S:ℝ))^ε * ((D:ℝ) * Fj2) * Fk2
          = (4*(R:ℝ)*(S:ℝ))^ε * (((D:ℝ) * Fj2) * Fk2) := by ring
        _ ≤ (4*(R:ℝ)*(S:ℝ))^ε
              * (((D:ℝ) * (c12 * (2*(R:ℝ))^((1:ℝ)/2))) * (c12 * (2*(S:ℝ))^((1:ℝ)/2))) := hmono2
        _ = (4*(R:ℝ)*(S:ℝ))^ε * (D:ℝ) * c12^2 *
              (((2*(R:ℝ))^((1:ℝ)/2)) * ((2*(S:ℝ))^((1:ℝ)/2))) := by ring
        _ = (4*(R:ℝ)*(S:ℝ))^ε * (D:ℝ) * c12^2 * (2 * Real.sqrt ((R:ℝ)*(S:ℝ))) := by
              rw [hsq2]
        _ = 2*c12^2*(4:ℝ)^ε*((D:ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ)) * (((R:ℝ)*(S:ℝ))^ε)) := by
              rw [show (4:ℝ)*(R:ℝ)*(S:ℝ) = 4*((R:ℝ)*(S:ℝ)) by ring,
                Real.mul_rpow (by norm_num) (by positivity)]
              ring
    have hCj : (∑ j ∈ Finset.range (JR+1), (4*(R:ℝ)*(S:ℝ))^ε * (2:ℝ)^j)
        = (4*(R:ℝ)*(S:ℝ))^ε * Fj1 := by
      rw [hFj1]
      exact (Finset.mul_sum _ _ _).symm
    have hb3 : (∑ j ∈ Finset.range (JR+1), (4*(R:ℝ)*(S:ℝ))^ε * (2:ℝ)^j)
          * (∑ k ∈ Finset.range (JS+1), ((2:ℝ)^k)^((3:ℝ)/4))
        ≤ (4*c34*(2:ℝ)^((3:ℝ)/4)*(4:ℝ)^ε)*T3 := by
      rw [hCj, ← hFk3, hT3]
      have hY0 : (0:ℝ) ≤ (4*(R:ℝ)*(S:ℝ))^ε := Real.rpow_nonneg (by positivity) ε
      have hnnk : (0:ℝ) ≤ Fk3 := by rw [hFk3]; exact Finset.sum_nonneg (fun k _ => by positivity)
      have hmono : Fj1 * Fk3 ≤ (4*(R:ℝ)) * (c34 * (2*(S:ℝ))^((3:ℝ)/4)) :=
        mul_le_mul hsum1j hsum3k hnnk (by positivity)
      calc (4*(R:ℝ)*(S:ℝ))^ε * Fj1 * Fk3
          = (4*(R:ℝ)*(S:ℝ))^ε * (Fj1 * Fk3) := by ring
        _ ≤ (4*(R:ℝ)*(S:ℝ))^ε * ((4*(R:ℝ)) * (c34 * (2*(S:ℝ))^((3:ℝ)/4))) :=
              mul_le_mul_of_nonneg_left hmono hY0
        _ = (4*c34*(2:ℝ)^((3:ℝ)/4)*(4:ℝ)^ε) * ((R:ℝ) * (S:ℝ)^((3:ℝ)/4) * (((R:ℝ)*(S:ℝ))^ε)) := by
              rw [show (4:ℝ)*(R:ℝ)*(S:ℝ) = 4*((R:ℝ)*(S:ℝ)) by ring,
                Real.mul_rpow (by norm_num) (by positivity),
                Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by positivity : (0:ℝ) ≤ (S:ℝ))]
              ring
    have hDj : (∑ j ∈ Finset.range (JR+1), (4*(R:ℝ)*(S:ℝ))^ε * ((2:ℝ)^j)^((3:ℝ)/4))
        = (4*(R:ℝ)*(S:ℝ))^ε * Fj3 := by
      rw [hFj3]
      exact (Finset.mul_sum _ _ _).symm
    have hb4 : (∑ j ∈ Finset.range (JR+1), (4*(R:ℝ)*(S:ℝ))^ε * ((2:ℝ)^j)^((3:ℝ)/4))
          * (∑ k ∈ Finset.range (JS+1), (2:ℝ)^k)
        ≤ (4*c34*(2:ℝ)^((3:ℝ)/4)*(4:ℝ)^ε)*T4 := by
      rw [hDj, hbk, hT4]
      have hY0 : (0:ℝ) ≤ (4*(R:ℝ)*(S:ℝ))^ε := Real.rpow_nonneg (by positivity) ε
      have hnn1 : (0:ℝ) ≤ Fk1 := by rw [hFk1]; exact Finset.sum_nonneg (fun k _ => by positivity)
      have hmono : Fj3 * Fk1 ≤ (c34 * (2*(R:ℝ))^((3:ℝ)/4)) * (4*(S:ℝ)) :=
        mul_le_mul hsum3j hsum1k hnn1 (by positivity)
      calc (4*(R:ℝ)*(S:ℝ))^ε * Fj3 * Fk1
          = (4*(R:ℝ)*(S:ℝ))^ε * (Fj3 * Fk1) := by ring
        _ ≤ (4*(R:ℝ)*(S:ℝ))^ε * ((c34 * (2*(R:ℝ))^((3:ℝ)/4)) * (4*(S:ℝ))) :=
              mul_le_mul_of_nonneg_left hmono hY0
        _ = (4*c34*(2:ℝ)^((3:ℝ)/4)*(4:ℝ)^ε) * ((S:ℝ) * (R:ℝ)^((3:ℝ)/4) * (((R:ℝ)*(S:ℝ))^ε)) := by
              rw [show (4:ℝ)*(R:ℝ)*(S:ℝ) = 4*((R:ℝ)*(S:ℝ)) by ring,
                Real.mul_rpow (by norm_num) (by positivity),
                Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by positivity : (0:ℝ) ≤ (R:ℝ))]
              ring
    have hT1nn : (0:ℝ) ≤ T1 := by rw [hT1]; positivity
    have hT2nn : (0:ℝ) ≤ T2 := by rw [hT2]; positivity
    have hT3nn : (0:ℝ) ≤ T3 := by rw [hT3]; positivity
    have hT4nn : (0:ℝ) ≤ T4 := by rw [hT4]; positivity
    have hk2nn : (0:ℝ) ≤ 2*c12^2*(4:ℝ)^ε :=
      mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg c12)) h4pos.le
    have hk3nn : (0:ℝ) ≤ 4*c34*(2:ℝ)^((3:ℝ)/4)*(4:ℝ)^ε :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hc34pos.le) h2qpos.le) h4pos.le
    have hfinal : 16*T1 + 2*c12^2*(4:ℝ)^ε*T2 + (4*c34*(2:ℝ)^((3:ℝ)/4)*(4:ℝ)^ε)*T3
          + (4*c34*(2:ℝ)^((3:ℝ)/4)*(4:ℝ)^ε)*T4
        ≤ (16 + 2*c12^2*(4:ℝ)^ε + 2*(4*c34*(2:ℝ)^((3:ℝ)/4)*(4:ℝ)^ε)) * (T1+T2+T3+T4) := by
      nlinarith [hT1nn, hT2nn, hT3nn, hT4nn, hk2nn, hk3nn]
    calc (∑ j ∈ Finset.range (JR+1), ∑ k ∈ Finset.range (JS+1),
          braceV D ((2:ℕ)^j) ((2:ℕ)^k) ε)
        ≤ ∑ j ∈ Finset.range (JR+1), ∑ k ∈ Finset.range (JS+1),
            (((D:ℝ)^(-(1:ℝ)/2) * (2:ℝ)^j) * (2:ℝ)^k
              + ((4*(R:ℝ)*(S:ℝ))^ε * ((D:ℝ) * ((2:ℝ)^j)^((1:ℝ)/2))) * ((2:ℝ)^k)^((1:ℝ)/2)
              + ((4*(R:ℝ)*(S:ℝ))^ε * (2:ℝ)^j) * ((2:ℝ)^k)^((3:ℝ)/4)
              + ((4*(R:ℝ)*(S:ℝ))^ε * ((2:ℝ)^j)^((3:ℝ)/4)) * (2:ℝ)^k) := hstep
      _ = (∑ j ∈ Finset.range (JR+1), (D:ℝ)^(-(1:ℝ)/2) * (2:ℝ)^j)
            * (∑ k ∈ Finset.range (JS+1), (2:ℝ)^k)
          + (∑ j ∈ Finset.range (JR+1), (4*(R:ℝ)*(S:ℝ))^ε * ((D:ℝ) * ((2:ℝ)^j)^((1:ℝ)/2)))
            * (∑ k ∈ Finset.range (JS+1), ((2:ℝ)^k)^((1:ℝ)/2))
          + (∑ j ∈ Finset.range (JR+1), (4*(R:ℝ)*(S:ℝ))^ε * (2:ℝ)^j)
            * (∑ k ∈ Finset.range (JS+1), ((2:ℝ)^k)^((3:ℝ)/4))
          + (∑ j ∈ Finset.range (JR+1), (4*(R:ℝ)*(S:ℝ))^ε * ((2:ℝ)^j)^((3:ℝ)/4))
            * (∑ k ∈ Finset.range (JS+1), (2:ℝ)^k) := hfac
      _ ≤ 16*T1 + 2*c12^2*(4:ℝ)^ε*T2 + (4*c34*(2:ℝ)^((3:ℝ)/4)*(4:ℝ)^ε)*T3
          + (4*c34*(2:ℝ)^((3:ℝ)/4)*(4:ℝ)^ε)*T4 := by linarith [hb1, hb2, hb3, hb4]
      _ ≤ (16 + 2*c12^2*(4:ℝ)^ε + 2*(4*c34*(2:ℝ)^((3:ℝ)/4)*(4:ℝ)^ε)) * (T1+T2+T3+T4) :=
            hfinal
      _ = (16 + 2*c12^2*(4:ℝ)^ε + 2*(4*c34*(2:ℝ)^((3:ℝ)/4)*(4:ℝ)^ε)) * braceV D R S ε := by
            rw [hbrace]

end Work.FIArea4
