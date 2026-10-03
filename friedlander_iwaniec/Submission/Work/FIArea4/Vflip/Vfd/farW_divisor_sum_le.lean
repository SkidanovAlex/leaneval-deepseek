import Mathlib
import Submission.Work.FIArea4.Vflip.Vfd.FarWDefs
import Submission.Work.FIArea4.Vflip.Vfd.FarBasic
import Submission.Work.FIArea4.Vflip.Vfd.farT_A_le
import Submission.Work.FIArea4.Vflip.Vfd.farT_B1_le
import Submission.Work.FIArea4.Vflip.Vfd.farB_absorptionZ

/-!
# The divisor sum of the far weight

This module proves `farW_divisor_sum_le`: the double divisor sum
`Σ_{c | r} Σ_{m | c} farW D R S H ε m c` is at most a constant (depending only on `ε`) times
`farB D R S H ε · τ(r)`, under the far-range hypotheses `D ≤ RS < D²` and `H = (RS/D)^{1/3}`.

The proof splits `farT` into its four summands, bounds each of them pointwise with
`⌈R/c⌉ ≤ 2R/c`, sums over `m | c` and `c | r` with the divisor-count estimates
`τ(c) ≤ 2√c`, `τ(c)/c ≤ 2` and `τ(c)c^{-1/2} ≤ 2`, and absorbs the logarithms with the
elementary estimate `log (2x) + 1 ≤ C x^{ε/4}`.
-/

namespace Work.FIArea4.Vflip.Vfd

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## The log-growth bound in the exact form needed -/

/-- For `ε > 0` there is `C > 0` with `log (2x) + 1 ≤ C x^{ε/4}` for all `x ≥ 1`. -/
lemma exists_log_two_mul_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x → Real.log (2 * x) + 1 ≤ C * x ^ (ε / 4) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := log_two_mul_add_le ε hε
  refine ⟨C₀ + 1, by positivity, ?_⟩
  intro x hx
  have hxpos : 0 < x := lt_of_lt_of_le one_pos hx
  have hlog : Real.log (2 * x) ≤ Real.log (2 * x + 1) :=
    Real.log_le_log (by linarith) (by linarith)
  have h2 : Real.log (2 * x + 1) ≤ C₀ * x ^ (ε / 4) := hC₀ x hx
  have h3 : (1 : ℝ) ≤ x ^ (ε / 4) := Real.one_le_rpow hx (by linarith)
  have h4 : Real.log (2 * x) + 1 ≤ C₀ * x ^ (ε / 4) + x ^ (ε / 4) := by linarith
  calc Real.log (2 * x) + 1 ≤ C₀ * x ^ (ε / 4) + x ^ (ε / 4) := h4
    _ = (C₀ + 1) * x ^ (ε / 4) := by ring

/-! ## The four summands of `farT` -/

/-- The first summand `A` of `farT`. -/
private def fAp (D R S : ℕ) (H ε : ℝ) (m c : ℕ) : ℝ :=
  ((m : ℝ) * ((S : ℝ) * (R : ℝ) / (5 * H * (c : ℝ) * (D : ℝ)))) ^ (-(1 : ℝ) / 2)
    * ((cR c R : ℝ) * (S : ℝ))

/-- The second summand of `farT`. -/
private def fB1p (D R S : ℕ) (H ε : ℝ) (m c : ℕ) : ℝ :=
  (m : ℝ) * (16 * (R : ℝ) * (S : ℝ) / ((c : ℝ) * (D : ℝ)))
    * Real.sqrt ((cR c R : ℝ) * (S : ℝ))

/-- The third summand of `farT`. -/
private def fB2p (D R S : ℕ) (H ε : ℝ) (m c : ℕ) : ℝ :=
  (Real.log (160 * H) + 1) * ((cR c R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4)
    + (S : ℝ) * (cR c R : ℝ) ^ ((3 : ℝ) / 4))

/-- The bracket on the right of the target. -/
private def Brk (D R S : ℕ) (H ε : ℝ) : ℝ :=
  4 * Real.sqrt 5 * ((D : ℝ) * H * (R : ℝ) * (S : ℝ)) ^ ((1 : ℝ) / 2)
    + ((R : ℝ) * (S : ℝ)) ^ (ε / 4)
      * (32 * Real.sqrt 2 * (((R : ℝ) * (S : ℝ)) ^ ((3 : ℝ) / 2)) / (D : ℝ)
          + (Real.log (160 * H) + 1)
            * (4 * (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4)
                + 2 * (2 * (R : ℝ)) ^ ((3 : ℝ) / 4) * (S : ℝ)))

/-- `farB` divided by `(log (2H) + 1)^2`. -/
private def ZBr (D R S : ℕ) (H ε : ℝ) : ℝ :=
  (Real.log (2 * (R : ℝ) * (S : ℝ)) + 1) ^ 2
      * ((D : ℝ) * H * (R : ℝ) * (S : ℝ)) ^ ((1 : ℝ) / 2)
    + (Real.log (2 * H) + 1) ^ 2 * ((R : ℝ) * (S : ℝ)) ^ (ε / 2)
        * (((R : ℝ) * (S : ℝ)) ^ ((3 : ℝ) / 2) / (D : ℝ)
            + (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4)
            + (S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4))

private lemma farB_eq_K2_ZBr (D R S : ℕ) (H ε : ℝ) :
    farB D R S H ε = (Real.log (2 * H) + 1) ^ 2 * ZBr D R S H ε := by
  rw [farB, ZBr]; ring

private lemma farT_eq_pieces (D R S : ℕ) (H ε : ℝ) (m c : ℕ) :
    farT D R S H ε m c
      = fAp D R S H ε m c
        + ((R : ℝ) * (S : ℝ)) ^ (ε / 4) * (fB1p D R S H ε m c + fB2p D R S H ε m c) :=
  rfl

private lemma farT_nonneg (D R S : ℕ) (H ε : ℝ) (m c : ℕ)
    (hD : (0 : ℝ) < D) (hH : 1 ≤ H) (hR : (0 : ℝ) < R) (hS : (0 : ℝ) < S) :
    0 ≤ farT D R S H ε m c := by
  rw [farT]
  have hlog : 0 ≤ Real.log (160 * H) + 1 := by
    have h1 : (1 : ℝ) ≤ 160 * H := by linarith
    have := Real.log_nonneg h1; linarith
  have hA : 0 ≤ (m : ℝ) * ((S : ℝ) * (R : ℝ) / (5 * H * (c : ℝ) * (D : ℝ))) := by positivity
  have hB1 : 0 ≤ (m : ℝ) * (16 * (R : ℝ) * (S : ℝ) / ((c : ℝ) * (D : ℝ))) := by positivity
  have hB2 : 0 ≤ (cR c R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4) + (S : ℝ) * (cR c R : ℝ) ^ ((3 : ℝ) / 4) := by
    apply add_nonneg <;> positivity
  exact add_nonneg (mul_nonneg (Real.rpow_nonneg hA _) (by positivity))
    (mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (add_nonneg (mul_nonneg hB1 (Real.sqrt_nonneg _)) (mul_nonneg hlog hB2)))

theorem farW_divisor_sum_le (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D R S : ℕ) (H : ℝ) (r : ℕ),
      1 ≤ D → 1 ≤ R → 1 ≤ S → D ≤ R * S → R * S < D * D →
      H = ((R : ℝ) * (S : ℝ) / (D : ℝ)) ^ ((1 : ℝ) / 3) →
      1 ≤ r → r ≤ 2 * R →
      (∑ c ∈ r.divisors, ∑ m ∈ c.divisors, farW D R S H ε m c)
        ≤ C * farB D R S H ε * ((r.divisors.card : ℕ) : ℝ) := by
  obtain ⟨Clog, hClogpos, hClog⟩ := exists_log_two_mul_bound ε hε
  refine ⟨12 + 64 * Clog + 8 * (Real.log 80 + 1) * Clog, ?_, ?_⟩
  · have h : 0 < Real.log 80 := Real.log_pos (by norm_num)
    positivity
  intro D R S H r hD hR hS hDRS hRSD hH hr1 hr2
  have hD0 : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  have hR0 : (0 : ℝ) < (R : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hR)
  have hS0 : (0 : ℝ) < (S : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hS)
  have hR1' : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hS1' : (1 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hS
  have hH1 : 1 ≤ H := by
    rw [hH]
    refine Real.one_le_rpow ?_ (by norm_num)
    rw [le_div_iff₀ hD0, one_mul]; exact_mod_cast hDRS
  have hH0 : 0 < H := lt_of_lt_of_le zero_lt_one hH1
  have hP1 : (1 : ℝ) ≤ (R : ℝ) * (S : ℝ) := by nlinarith
  have hDHRS0 : 0 ≤ (D : ℝ) * H * (R : ℝ) * (S : ℝ) := by positivity
  have hτnn : (0 : ℝ) ≤ ((r.divisors.card : ℕ) : ℝ) := Nat.cast_nonneg _
  have hL₀nn : 0 ≤ Real.log (2 * (R : ℝ)) + 1 := by
    have h1 : (1 : ℝ) ≤ 2 * (R : ℝ) := by linarith
    have := Real.log_nonneg h1; linarith
  have hlog160nn : 0 ≤ Real.log (160 * H) + 1 := by
    have h1 : (1 : ℝ) ≤ 160 * H := by linarith
    have := Real.log_nonneg h1; linarith
  -- ### The `A` summand
  have hsumA : (∑ c ∈ r.divisors, ∑ m ∈ c.divisors, fAp D R S H ε m c)
      ≤ 4 * Real.sqrt 5 * Real.sqrt ((D : ℝ) * H * (R : ℝ) * (S : ℝ))
          * ((r.divisors.card : ℕ) : ℝ) := by
    have hinner : ∀ c ∈ r.divisors,
        (∑ m ∈ c.divisors, fAp D R S H ε m c)
          ≤ 4 * Real.sqrt 5 * Real.sqrt ((D : ℝ) * H * (R : ℝ) * (S : ℝ)) := by
      intro c hc
      have hc1 : 1 ≤ c := Nat.pos_of_mem_divisors hc
      have hc2R : c ≤ 2 * R := by
        have h1 : c ≤ r := Nat.le_of_dvd (by omega) (Nat.mem_divisors.mp hc).1
        omega
      have hpt : ∀ m ∈ c.divisors,
          fAp D R S H ε m c ≤ 2 * Real.sqrt 5 * Real.sqrt ((D : ℝ) * H * (R : ℝ) * (S : ℝ) / (c : ℝ)) := by
        intro m hm
        have hm1 : 1 ≤ m := Nat.pos_of_mem_divisors hm
        refine (farT_A_le D R S H m c hD hR (by omega) hH0 hm1 hc1 hc2R).trans ?_
        rw [← Real.sqrt_eq_rpow]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.sqrt_le_sqrt
        refine div_le_div_of_nonneg_left hDHRS0 (by positivity) ?_
        have hm1' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
        exact le_mul_of_one_le_right (by positivity) hm1'
      calc (∑ m ∈ c.divisors, fAp D R S H ε m c)
          ≤ ∑ _m ∈ c.divisors, (2 * Real.sqrt 5 * Real.sqrt ((D : ℝ) * H * (R : ℝ) * (S : ℝ) / (c : ℝ))) :=
            Finset.sum_le_sum hpt
        _ = ((c.divisors.card : ℕ) : ℝ) * (2 * Real.sqrt 5 * Real.sqrt ((D : ℝ) * H * (R : ℝ) * (S : ℝ) / (c : ℝ))) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 4 * Real.sqrt 5 * Real.sqrt ((D : ℝ) * H * (R : ℝ) * (S : ℝ)) := by
            have hτc : ((c.divisors.card : ℕ) : ℝ) ≤ 2 * Real.sqrt (c : ℝ) :=
              divisors_card_le_two_sqrt c hc1
            calc ((c.divisors.card : ℕ) : ℝ) * (2 * Real.sqrt 5 * Real.sqrt ((D : ℝ) * H * (R : ℝ) * (S : ℝ) / (c : ℝ)))
                = 2 * Real.sqrt 5 * (Real.sqrt ((D : ℝ) * H * (R : ℝ) * (S : ℝ)) / Real.sqrt (c : ℝ))
                    * ((c.divisors.card : ℕ) : ℝ) := by
                  rw [Real.sqrt_div hDHRS0]; ring
              _ ≤ 2 * Real.sqrt 5 * (Real.sqrt ((D : ℝ) * H * (R : ℝ) * (S : ℝ)) / Real.sqrt (c : ℝ))
                    * (2 * Real.sqrt (c : ℝ)) := by
                  apply mul_le_mul_of_nonneg_left hτc; positivity
              _ = 4 * Real.sqrt 5 * Real.sqrt ((D : ℝ) * H * (R : ℝ) * (S : ℝ)) := by
                  field_simp
                  norm_num
    calc (∑ c ∈ r.divisors, ∑ m ∈ c.divisors, fAp D R S H ε m c)
        ≤ ∑ _c ∈ r.divisors,
            (4 * Real.sqrt 5 * Real.sqrt ((D : ℝ) * H * (R : ℝ) * (S : ℝ))) :=
          Finset.sum_le_sum hinner
      _ = ((r.divisors.card : ℕ) : ℝ)
            * (4 * Real.sqrt 5 * Real.sqrt ((D : ℝ) * H * (R : ℝ) * (S : ℝ))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = 4 * Real.sqrt 5 * Real.sqrt ((D : ℝ) * H * (R : ℝ) * (S : ℝ))
            * ((r.divisors.card : ℕ) : ℝ) := by ring
  -- ### The `B1` summand
  have hsumB1 : (∑ c ∈ r.divisors, ∑ m ∈ c.divisors, fB1p D R S H ε m c)
      ≤ 32 * Real.sqrt 2 * (((R : ℝ) * (S : ℝ)) ^ ((3 : ℝ) / 2)) / (D : ℝ)
          * ((r.divisors.card : ℕ) : ℝ) := by
    have hinner : ∀ c ∈ r.divisors,
        (∑ m ∈ c.divisors, fB1p D R S H ε m c)
          ≤ 32 * Real.sqrt 2 * (((R : ℝ) * (S : ℝ)) ^ ((3 : ℝ) / 2)) / (D : ℝ) := by
      intro c hc
      have hc1 : 1 ≤ c := Nat.pos_of_mem_divisors hc
      have hc2R : c ≤ 2 * R := by
        have h1 : c ≤ r := Nat.le_of_dvd (by omega) (Nat.mem_divisors.mp hc).1
        omega
      have hpt : ∀ m ∈ c.divisors, fB1p D R S H ε m c
          ≤ 16 * Real.sqrt 2 * (m : ℝ) * (((R : ℝ) * (S : ℝ) / (c : ℝ)) ^ ((3 : ℝ) / 2)) / (D : ℝ) := by
        intro m hm
        exact farT_B1_le D R S H m c hD hR (by omega) hc1 hc2R
      have hcc : (c : ℝ) * Real.sqrt (c : ℝ) = (c : ℝ) ^ ((3 : ℝ) / 2) := by
        rw [Real.sqrt_eq_rpow, show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num,
          Real.rpow_add (by positivity : (0 : ℝ) < (c : ℝ)), Real.rpow_one]
      have hmul : (((R : ℝ) * (S : ℝ) / (c : ℝ)) ^ ((3 : ℝ) / 2)) * ((c : ℝ) ^ ((3 : ℝ) / 2))
          = ((R : ℝ) * (S : ℝ)) ^ ((3 : ℝ) / 2) := by
        rw [← Real.mul_rpow (by positivity) (by positivity)]
        congr 1
        field_simp
      calc (∑ m ∈ c.divisors, fB1p D R S H ε m c)
          ≤ ∑ m ∈ c.divisors,
              (16 * Real.sqrt 2 * (m : ℝ) * (((R : ℝ) * (S : ℝ) / (c : ℝ)) ^ ((3 : ℝ) / 2)) / (D : ℝ)) :=
            Finset.sum_le_sum hpt
        _ = 16 * Real.sqrt 2 * (((R : ℝ) * (S : ℝ) / (c : ℝ)) ^ ((3 : ℝ) / 2)) / (D : ℝ)
              * (∑ m ∈ c.divisors, (m : ℝ)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro m _; ring
        _ ≤ 16 * Real.sqrt 2 * (((R : ℝ) * (S : ℝ) / (c : ℝ)) ^ ((3 : ℝ) / 2)) / (D : ℝ)
              * ((c : ℝ) * ((c.divisors.card : ℕ) : ℝ)) := by
            apply mul_le_mul_of_nonneg_left (sum_divisors_le_card_mul c (by omega))
            positivity
        _ ≤ 32 * Real.sqrt 2 * (((R : ℝ) * (S : ℝ)) ^ ((3 : ℝ) / 2)) / (D : ℝ) := by
            have hτc : ((c.divisors.card : ℕ) : ℝ) ≤ 2 * Real.sqrt (c : ℝ) :=
              divisors_card_le_two_sqrt c hc1
            have h1 : (16 : ℝ) * Real.sqrt 2 * (((R : ℝ) * (S : ℝ) / (c : ℝ)) ^ ((3 : ℝ) / 2)) / (D : ℝ)
                * ((c : ℝ) * ((c.divisors.card : ℕ) : ℝ))
                ≤ 16 * Real.sqrt 2 * (((R : ℝ) * (S : ℝ) / (c : ℝ)) ^ ((3 : ℝ) / 2)) / (D : ℝ)
                  * ((c : ℝ) * (2 * Real.sqrt (c : ℝ))) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact mul_le_mul_of_nonneg_left hτc (by positivity)
            refine h1.trans (le_of_eq ?_)
            rw [show (c : ℝ) * (2 * Real.sqrt (c : ℝ)) = 2 * ((c : ℝ) * Real.sqrt (c : ℝ)) by ring, hcc]
            rw [show (16 : ℝ) * Real.sqrt 2 * (((R : ℝ) * (S : ℝ) / (c : ℝ)) ^ ((3 : ℝ) / 2)) / (D : ℝ)
                  * (2 * ((c : ℝ) ^ ((3 : ℝ) / 2)))
                = 32 * Real.sqrt 2 / (D : ℝ)
                    * ((((R : ℝ) * (S : ℝ) / (c : ℝ)) ^ ((3 : ℝ) / 2)) * ((c : ℝ) ^ ((3 : ℝ) / 2))) by ring,
                hmul]
            ring
    calc (∑ c ∈ r.divisors, ∑ m ∈ c.divisors, fB1p D R S H ε m c)
        ≤ ∑ _c ∈ r.divisors,
            (32 * Real.sqrt 2 * (((R : ℝ) * (S : ℝ)) ^ ((3 : ℝ) / 2)) / (D : ℝ)) :=
          Finset.sum_le_sum hinner
      _ = 32 * Real.sqrt 2 * (((R : ℝ) * (S : ℝ)) ^ ((3 : ℝ) / 2)) / (D : ℝ)
            * ((r.divisors.card : ℕ) : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
  -- ### The `B2` summand
  have hsumB2 : (∑ c ∈ r.divisors, ∑ m ∈ c.divisors, fB2p D R S H ε m c)
      ≤ (Real.log (160 * H) + 1)
          * (4 * (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4)
              + 2 * (2 * (R : ℝ)) ^ ((3 : ℝ) / 4) * (S : ℝ))
          * ((r.divisors.card : ℕ) : ℝ) := by
    have hS1 : (∑ c ∈ r.divisors, ((c.divisors.card : ℕ) : ℝ) / (c : ℝ))
        ≤ 2 * ((r.divisors.card : ℕ) : ℝ) := by
      calc (∑ c ∈ r.divisors, ((c.divisors.card : ℕ) : ℝ) / (c : ℝ))
          ≤ ∑ _c ∈ r.divisors, (2 : ℝ) := by
            apply Finset.sum_le_sum
            intro c hc
            have hc1 : 1 ≤ c := Nat.pos_of_mem_divisors hc
            calc ((c.divisors.card : ℕ) : ℝ) / (c : ℝ)
                ≤ 2 * (c : ℝ) ^ (-(1 : ℝ) / 2) := card_div_le_two_mul_rpow_neg_half c hc1
              _ ≤ 2 := by
                have h : (c : ℝ) ^ (-(1 : ℝ) / 2) ≤ 1 :=
                  Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hc1) (by norm_num)
                linarith
        _ = 2 * ((r.divisors.card : ℕ) : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
    have hS2 : (∑ c ∈ r.divisors, ((c.divisors.card : ℕ) : ℝ) * (c : ℝ) ^ (-(3 : ℝ) / 4))
        ≤ 2 * ((r.divisors.card : ℕ) : ℝ) := by
      calc (∑ c ∈ r.divisors, ((c.divisors.card : ℕ) : ℝ) * (c : ℝ) ^ (-(3 : ℝ) / 4))
          ≤ ∑ _c ∈ r.divisors, (2 : ℝ) := by
            apply Finset.sum_le_sum
            intro c hc
            have hc1 : 1 ≤ c := Nat.pos_of_mem_divisors hc
            calc ((c.divisors.card : ℕ) : ℝ) * (c : ℝ) ^ (-(3 : ℝ) / 4)
                ≤ ((c.divisors.card : ℕ) : ℝ) * (c : ℝ) ^ (-(1 : ℝ) / 2) :=
                  card_mul_rpow_neg_three_quarter_le c hc1
              _ ≤ 2 := card_mul_rpow_neg_half_le_two c hc1
        _ = 2 * ((r.divisors.card : ℕ) : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
    have hinner : ∀ c ∈ r.divisors,
        (∑ m ∈ c.divisors, fB2p D R S H ε m c)
          ≤ (Real.log (160 * H) + 1)
              * (2 * (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4) * (((c.divisors.card : ℕ) : ℝ) / (c : ℝ))
                + (2 * (R : ℝ)) ^ ((3 : ℝ) / 4) * (S : ℝ)
                  * (((c.divisors.card : ℕ) : ℝ) * (c : ℝ) ^ (-(3 : ℝ) / 4))) := by
      intro c hc
      have hc1 : 1 ≤ c := Nat.pos_of_mem_divisors hc
      have hc2R : c ≤ 2 * R := by
        have h1 : c ≤ r := Nat.le_of_dvd (by omega) (Nat.mem_divisors.mp hc).1
        omega
      have hcRle : (cR c R : ℝ) ≤ 2 * (R : ℝ) / (c : ℝ) := cR_le_two_mul_div hc1 hR hc2R
      have hsumconst : (∑ m ∈ c.divisors, fB2p D R S H ε m c)
          = ((c.divisors.card : ℕ) : ℝ)
              * ((Real.log (160 * H) + 1)
                  * ((cR c R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4)
                      + (S : ℝ) * (cR c R : ℝ) ^ ((3 : ℝ) / 4))) := by
        rw [show (∑ m ∈ c.divisors, fB2p D R S H ε m c)
              = ∑ _m ∈ c.divisors, fB2p D R S H ε 0 c from by
              apply Finset.sum_congr rfl; intro m _; rfl]
        rw [Finset.sum_const, nsmul_eq_mul]
        rfl
      have hdiv1 : (2 * (R : ℝ) / (c : ℝ)) * (S : ℝ) ^ ((3 : ℝ) / 4) * ((c.divisors.card : ℕ) : ℝ)
          = 2 * (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4) * (((c.divisors.card : ℕ) : ℝ) / (c : ℝ)) := by
        field_simp
      have hdiv2 : (2 * (R : ℝ) / (c : ℝ)) ^ ((3 : ℝ) / 4) * (S : ℝ) * ((c.divisors.card : ℕ) : ℝ)
          = (2 * (R : ℝ)) ^ ((3 : ℝ) / 4) * (S : ℝ)
              * (((c.divisors.card : ℕ) : ℝ) * (c : ℝ) ^ (-(3 : ℝ) / 4)) := by
        rw [Real.div_rpow (by positivity) (by positivity), div_eq_mul_inv,
          ← Real.rpow_neg (by positivity : (0 : ℝ) ≤ (c : ℝ)) (3 / 4),
          show (-(3 : ℝ) / 4) = -((3 : ℝ) / 4) by ring]
        ring
      have hB2nonneg : 0 ≤ Real.log (160 * H) + 1 := by
        have h1 : (1 : ℝ) ≤ 160 * H := by linarith
        have := Real.log_nonneg h1; linarith
      rw [hsumconst]
      calc ((c.divisors.card : ℕ) : ℝ)
            * ((Real.log (160 * H) + 1) * ((cR c R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4)
                + (S : ℝ) * (cR c R : ℝ) ^ ((3 : ℝ) / 4)))
          ≤ ((c.divisors.card : ℕ) : ℝ)
            * ((Real.log (160 * H) + 1) * ((2 * (R : ℝ) / (c : ℝ)) * (S : ℝ) ^ ((3 : ℝ) / 4)
                + (S : ℝ) * (2 * (R : ℝ) / (c : ℝ)) ^ ((3 : ℝ) / 4))) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply mul_le_mul_of_nonneg_left _ hB2nonneg
            apply add_le_add
            · exact mul_le_mul_of_nonneg_right hcRle (by positivity)
            · exact mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow (by positivity) hcRle (by norm_num)) (by positivity)
        _ = (Real.log (160 * H) + 1)
              * (2 * (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4) * (((c.divisors.card : ℕ) : ℝ) / (c : ℝ))
                + (2 * (R : ℝ)) ^ ((3 : ℝ) / 4) * (S : ℝ)
                  * (((c.divisors.card : ℕ) : ℝ) * (c : ℝ) ^ (-(3 : ℝ) / 4))) := by
            rw [← hdiv1, ← hdiv2]; ring
    calc (∑ c ∈ r.divisors, ∑ m ∈ c.divisors, fB2p D R S H ε m c)
        ≤ ∑ c ∈ r.divisors,
            ((Real.log (160 * H) + 1)
              * (2 * (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4) * (((c.divisors.card : ℕ) : ℝ) / (c : ℝ))
                + (2 * (R : ℝ)) ^ ((3 : ℝ) / 4) * (S : ℝ)
                  * (((c.divisors.card : ℕ) : ℝ) * (c : ℝ) ^ (-(3 : ℝ) / 4)))) :=
          Finset.sum_le_sum hinner
      _ = (Real.log (160 * H) + 1)
            * (2 * (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4)
                * (∑ c ∈ r.divisors, ((c.divisors.card : ℕ) : ℝ) / (c : ℝ))
              + (2 * (R : ℝ)) ^ ((3 : ℝ) / 4) * (S : ℝ)
                * (∑ c ∈ r.divisors, ((c.divisors.card : ℕ) : ℝ) * (c : ℝ) ^ (-(3 : ℝ) / 4))) := by
          rw [← Finset.mul_sum]
          congr 1
          rw [Finset.sum_add_distrib]
          congr 1 <;> rw [← Finset.mul_sum]
      _ ≤ (Real.log (160 * H) + 1)
            * (2 * (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4) * (2 * ((r.divisors.card : ℕ) : ℝ))
              + (2 * (R : ℝ)) ^ ((3 : ℝ) / 4) * (S : ℝ) * (2 * ((r.divisors.card : ℕ) : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ hlog160nn
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left hS1 (by positivity)
          · exact mul_le_mul_of_nonneg_left hS2 (by positivity)
      _ = (Real.log (160 * H) + 1)
            * (4 * (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4)
                + 2 * (2 * (R : ℝ)) ^ ((3 : ℝ) / 4) * (S : ℝ))
            * ((r.divisors.card : ℕ) : ℝ) := by ring
  -- ### Combine the four bounds into `ΣΣ farT ≤ Brk * τ`
  have hdecomp1 : (∑ c ∈ r.divisors, ∑ m ∈ c.divisors, farT D R S H ε m c)
      = ∑ c ∈ r.divisors, ((∑ m ∈ c.divisors, fAp D R S H ε m c)
          + ((R : ℝ) * (S : ℝ)) ^ (ε / 4)
            * ((∑ m ∈ c.divisors, fB1p D R S H ε m c)
                + (∑ m ∈ c.divisors, fB2p D R S H ε m c))) := by
    apply Finset.sum_congr rfl
    intro c hc
    simp only [farT_eq_pieces]
    rw [Finset.sum_add_distrib]
    congr 1
    rw [← Finset.mul_sum, Finset.sum_add_distrib]
  have hdecomp2 : (∑ c ∈ r.divisors, ((∑ m ∈ c.divisors, fAp D R S H ε m c)
          + ((R : ℝ) * (S : ℝ)) ^ (ε / 4)
            * ((∑ m ∈ c.divisors, fB1p D R S H ε m c)
                + (∑ m ∈ c.divisors, fB2p D R S H ε m c))))
      = (∑ c ∈ r.divisors, ∑ m ∈ c.divisors, fAp D R S H ε m c)
        + ((R : ℝ) * (S : ℝ)) ^ (ε / 4)
          * ((∑ c ∈ r.divisors, ∑ m ∈ c.divisors, fB1p D R S H ε m c)
              + (∑ c ∈ r.divisors, ∑ m ∈ c.divisors, fB2p D R S H ε m c)) := by
    rw [Finset.sum_add_distrib]
    congr 1
    rw [← Finset.mul_sum, Finset.sum_add_distrib]
  have hsumT : (∑ c ∈ r.divisors, ∑ m ∈ c.divisors, farT D R S H ε m c)
      ≤ Brk D R S H ε * ((r.divisors.card : ℕ) : ℝ) := by
    rw [hdecomp1, hdecomp2]
    calc (∑ c ∈ r.divisors, ∑ m ∈ c.divisors, fAp D R S H ε m c)
          + ((R : ℝ) * (S : ℝ)) ^ (ε / 4)
            * ((∑ c ∈ r.divisors, ∑ m ∈ c.divisors, fB1p D R S H ε m c)
                + (∑ c ∈ r.divisors, ∑ m ∈ c.divisors, fB2p D R S H ε m c))
        ≤ 4 * Real.sqrt 5 * ((D : ℝ) * H * (R : ℝ) * (S : ℝ)) ^ ((1 : ℝ) / 2)
              * ((r.divisors.card : ℕ) : ℝ)
          + ((R : ℝ) * (S : ℝ)) ^ (ε / 4)
            * ((32 * Real.sqrt 2 * (((R : ℝ) * (S : ℝ)) ^ ((3 : ℝ) / 2)) / (D : ℝ)
                  * ((r.divisors.card : ℕ) : ℝ))
              + ((Real.log (160 * H) + 1)
                  * (4 * (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4)
                      + 2 * (2 * (R : ℝ)) ^ ((3 : ℝ) / 4) * (S : ℝ))
                  * ((r.divisors.card : ℕ) : ℝ))) := by
          apply add_le_add
          · have h1 : Real.sqrt ((D : ℝ) * H * (R : ℝ) * (S : ℝ))
                = ((D : ℝ) * H * (R : ℝ) * (S : ℝ)) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
            rw [← h1]; exact hsumA
          · apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by positivity) _)
            apply add_le_add hsumB1 hsumB2
      _ = Brk D R S H ε * ((r.divisors.card : ℕ) : ℝ) := by
          rw [Brk]; ring
  -- ### Sum `farW` via `ΣΣ farW ≤ (log 2H+1)^2 (log 2R+1) ΣΣ farT`
  have hWsum1 : ((Real.log (2 * H) + 1) ^ 2 * (Real.log (2 * (R : ℝ)) + 1))
        * (∑ c ∈ r.divisors, ∑ m ∈ c.divisors, farT D R S H ε m c)
      = ∑ c ∈ r.divisors, ∑ m ∈ c.divisors,
          ((Real.log (2 * H) + 1) ^ 2 * (Real.log (2 * (R : ℝ)) + 1)) * farT D R S H ε m c := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c hc
    rw [Finset.mul_sum]
  have hWsum : (∑ c ∈ r.divisors, ∑ m ∈ c.divisors, farW D R S H ε m c)
      ≤ (Real.log (2 * H) + 1) ^ 2 * (Real.log (2 * (R : ℝ)) + 1)
          * (∑ c ∈ r.divisors, ∑ m ∈ c.divisors, farT D R S H ε m c) := by
    rw [hWsum1]
    apply Finset.sum_le_sum
    intro c hc
    apply Finset.sum_le_sum
    intro m hm
    have hc1 : 1 ≤ c := Nat.pos_of_mem_divisors hc
    have hcRle : (cR c R : ℝ) ≤ (R : ℝ) := by exact_mod_cast cR_le_self hc1 hR
    have hcRpos : (0 : ℝ) < (cR c R : ℝ) := by
      have h := cR_pos hc1 hR
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one h)
    have hlog : Real.log (2 * (cR c R : ℝ)) + 1 ≤ Real.log (2 * (R : ℝ)) + 1 := by
      have h1 : (0 : ℝ) < 2 * (cR c R : ℝ) := by linarith
      have h2 : 2 * (cR c R : ℝ) ≤ 2 * (R : ℝ) := by linarith
      linarith [Real.log_le_log h1 h2]
    have hT : 0 ≤ farT D R S H ε m c := farT_nonneg D R S H ε m c hD0 hH1 hR0 hS0
    rw [farW_eq]
    calc (Real.log (2 * H) + 1) ^ 2 * (Real.log (2 * (cR c R : ℝ)) + 1) * farT D R S H ε m c
        = (Real.log (2 * H) + 1) ^ 2
            * ((Real.log (2 * (cR c R : ℝ)) + 1) * farT D R S H ε m c) := by ring
      _ ≤ (Real.log (2 * H) + 1) ^ 2
            * ((Real.log (2 * (R : ℝ)) + 1) * farT D R S H ε m c) := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          exact mul_le_mul_of_nonneg_right hlog hT
      _ = (Real.log (2 * H) + 1) ^ 2 * (Real.log (2 * (R : ℝ)) + 1) * farT D R S H ε m c := by ring
  -- ### Final comparison via `farB_absorptionZ`
  have hZabs := farB_absorptionZ ε hε Clog hClogpos hClog R S D H (Real.log (2 * (R : ℝ)) + 1)
    hR hS hD hH1 rfl
  calc (∑ c ∈ r.divisors, ∑ m ∈ c.divisors, farW D R S H ε m c)
      ≤ (Real.log (2 * H) + 1) ^ 2 * (Real.log (2 * (R : ℝ)) + 1)
          * (∑ c ∈ r.divisors, ∑ m ∈ c.divisors, farT D R S H ε m c) := hWsum
    _ ≤ (Real.log (2 * H) + 1) ^ 2 * (Real.log (2 * (R : ℝ)) + 1)
          * (Brk D R S H ε * ((r.divisors.card : ℕ) : ℝ)) := by
          apply mul_le_mul_of_nonneg_left hsumT
          exact mul_nonneg (sq_nonneg _) hL₀nn
    _ = (Real.log (2 * H) + 1) ^ 2 * ((Real.log (2 * (R : ℝ)) + 1) * Brk D R S H ε)
          * ((r.divisors.card : ℕ) : ℝ) := by ring
    _ ≤ (Real.log (2 * H) + 1) ^ 2
          * ((12 + 64 * Clog + 8 * (Real.log 80 + 1) * Clog) * ZBr D R S H ε)
          * ((r.divisors.card : ℕ) : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ hτnn
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          exact hZabs
    _ = (12 + 64 * Clog + 8 * (Real.log 80 + 1) * Clog) * farB D R S H ε
          * ((r.divisors.card : ℕ) : ℝ) := by
          rw [farB_eq_K2_ZBr]; ring

end

end Work.FIArea4.Vflip.Vfd
