import Mathlib
import Submission.Work.FIArea4.Vflip.Vfd.farGadgets
import Submission.Work.FIArea4.Vflip.Vfd.FarSepDefs
import Submission.Work.FIArea4.A4varbounds
import Submission.Work.FIArea4.Vflip.Vfd.log_growth
import Submission.Commons.NumberTheory.DivisorBound.card_divisors_le_rpow

/-!
# The weights of the far-numerics estimate

This module fixes the `(m,c)`-weight `farW` and the target bracket `farB` of the far part of the
flipped-moduli bound, together with the elementary divisor sums and logarithmic comparisons that
its numerical estimate needs.
-/

namespace Work.FIArea4.Vflip.Vfd

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The bracket of the `(m,c)`-piece of the far sum (without the logarithmic prefactors):
the large-sieve bracket of the flipped modulus `m · Q'` evaluated at its extreme value, with
`Q'` ranging over the dyadic interval `(SR/(5HcD), 16SR/(cD))`. -/
def farT (D R S : ℕ) (H ε : ℝ) (m c : ℕ) : ℝ :=
  ( (m * ((S : ℝ) * (R : ℝ) / (5 * H * (c : ℝ) * (D : ℝ)))) ^ (-(1 : ℝ) / 2)
      * ((cR c R : ℝ) * (S : ℝ))
    + ((R : ℝ) * (S : ℝ)) ^ (ε / 4)
      * ( m * (16 * (R : ℝ) * (S : ℝ) / ((c : ℝ) * (D : ℝ))) * Real.sqrt ((cR c R : ℝ) * (S : ℝ))
          + (Real.log (160 * H) + 1) * ((cR c R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4)
              + (S : ℝ) * (cR c R : ℝ) ^ ((3 : ℝ) / 4)) ) )

/-- The full weight of the `(m,c)`-piece of the far sum. -/
def farW (D R S : ℕ) (H ε : ℝ) (m c : ℕ) : ℝ :=
  (Real.log (2 * H) + 1) ^ 2 * (Real.log (2 * (cR c R : ℝ)) + 1) * farT D R S H ε m c

/-- The bracket of the far part of the flipped-moduli bound. -/
def farB (D R S : ℕ) (H ε : ℝ) : ℝ :=
  (Real.log (2 * H) + 1) ^ 2 * (Real.log (2 * (R : ℝ) * (S : ℝ)) + 1) ^ 2
      * ((D : ℝ) * H * (R : ℝ) * (S : ℝ)) ^ ((1 : ℝ) / 2)
  + (Real.log (2 * H) + 1) ^ 4 * ((R : ℝ) * (S : ℝ)) ^ (ε / 2)
      * (((R : ℝ) * (S : ℝ)) ^ ((3 : ℝ) / 2) / (D : ℝ)
          + (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4) + (S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4))

lemma farW_eq (D R S : ℕ) (H ε : ℝ) (m c : ℕ) :
    farW D R S H ε m c
      = (Real.log (2 * H) + 1) ^ 2 * (Real.log (2 * (cR c R : ℝ)) + 1) * farT D R S H ε m c :=
  rfl

/-- `⌈R/c⌉ ≤ R` for `c ≥ 1 ≤ R`. -/
lemma cR_le_self {c R : ℕ} (hc : 1 ≤ c) (hR : 1 ≤ R) : cR c R ≤ R := by
  rw [cR, Nat.div_le_iff_le_mul_add_pred (by omega : 0 < c)]
  have hRmul : R ≤ c * R := Nat.le_mul_of_pos_left R (by omega : 0 < c)
  omega

/-- `⌈R/c⌉ ≤ 2R/c` (as reals), for `1 ≤ c ≤ 2R`. -/
lemma cR_le_two_mul_div {c R : ℕ} (hc : 1 ≤ c) (hR : 1 ≤ R) (hc2 : c ≤ 2 * R) :
    (cR c R : ℝ) ≤ 2 * (R : ℝ) / (c : ℝ) := by
  have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  rw [le_div_iff₀ hcpos]
  have hkey : cR c R * c ≤ 2 * R := by
    rcases le_or_gt c R with hle | hlt
    · calc cR c R * c ≤ R + c - 1 := by rw [cR]; exact Nat.div_mul_le_self _ _
        _ ≤ 2 * R := by omega
    · have hcR1 : cR c R = 1 := by
        rw [cR]
        have h1 : 1 ≤ (R + c - 1) / c := (Nat.le_div_iff_mul_le (by omega : 0 < c)).mpr (by omega)
        have h2 : (R + c - 1) / c < 2 := by
          rw [Nat.div_lt_iff_lt_mul (by omega : 0 < c)]; omega
        omega
      rw [hcR1, one_mul]; omega
  calc (cR c R : ℝ) * (c : ℝ) = ((cR c R * c : ℕ) : ℝ) := by push_cast; ring
    _ ≤ ((2 * R : ℕ) : ℝ) := by exact_mod_cast hkey
    _ = 2 * (R : ℝ) := by push_cast; ring

/-- `farW` is nonnegative, for `H ≥ 1` and `c ≥ 1`. -/
lemma farW_nonneg {D R S : ℕ} {H ε : ℝ} {m c : ℕ}
    (hH : 1 ≤ H) (hR : 1 ≤ R) (hc : 1 ≤ c) :
    0 ≤ farW D R S H ε m c := by
  rw [farW_eq]
  have hlog2H : 0 ≤ Real.log (2 * H) + 1 := by
    have h2H : 1 ≤ 2 * H := by linarith
    have := Real.log_nonneg h2H; linarith
  have hcRpos : 1 ≤ cR c R := cR_pos hc hR
  have hlogR : 0 ≤ Real.log (2 * (cR c R : ℝ)) + 1 := by
    have h2 : 1 ≤ 2 * (cR c R : ℝ) := by
      have : (1:ℝ) ≤ (cR c R : ℝ) := by exact_mod_cast hcRpos
      linarith
    have := Real.log_nonneg h2; linarith
  have hlog160 : 0 ≤ Real.log (160 * H) + 1 := by
    have h160 : 1 ≤ 160 * H := by linarith
    have := Real.log_nonneg h160; linarith
  have hT : 0 ≤ farT D R S H ε m c := by
    rw [farT]
    have hA : 0 ≤ (m : ℝ) * ((S : ℝ) * (R : ℝ) / (5 * H * (c : ℝ) * (D : ℝ))) := by
      apply mul_nonneg (Nat.cast_nonneg _)
      exact div_nonneg (by positivity) (by positivity)
    have hB : 0 ≤ (cR c R : ℝ) * (S : ℝ) := by positivity
    have hC : 0 ≤ (m : ℝ) * (16 * (R : ℝ) * (S : ℝ) / ((c : ℝ) * (D : ℝ))) := by
      apply mul_nonneg (Nat.cast_nonneg _)
      exact div_nonneg (by positivity) (by positivity)
    have hD2 : 0 ≤ Real.sqrt ((cR c R : ℝ) * (S : ℝ)) := Real.sqrt_nonneg _
    have hE : 0 ≤ (cR c R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4) + (S : ℝ) * (cR c R : ℝ) ^ ((3 : ℝ) / 4) := by
      apply add_nonneg <;> positivity
    exact add_nonneg (mul_nonneg (Real.rpow_nonneg hA _) hB)
      (mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (add_nonneg (mul_nonneg hC hD2) (mul_nonneg hlog160 hE)))
  exact mul_nonneg (mul_nonneg (sq_nonneg _) hlogR) hT

/-! ## Elementary divisor sums and logarithmic comparisons -/

/-- `Σ_{c | n} Σ_{m | c} m · c^{-3/2} ≤ C τ(n)` for an absolute constant `C`. -/
lemma dsum_mul_cpow :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      (∑ c ∈ n.divisors, ∑ m ∈ c.divisors, (m : ℝ) * (c : ℝ) ^ (-(3 : ℝ) / 2))
        ≤ C * ((n.divisors.card : ℕ) : ℝ) := by
  obtain ⟨C0, hC0pos, hC0⟩ :=
    Commons.NumberTheory.DivisorBound.card_divisors_le_rpow (1 / 4) (by norm_num)
  refine ⟨C0, hC0pos, ?_⟩
  intro n
  have hσ : ∀ c : ℕ, (∑ m ∈ c.divisors, (m : ℝ)) ≤ (c : ℝ) * ((c.divisors.card : ℕ) : ℝ) := by
    intro c
    calc (∑ m ∈ c.divisors, (m : ℝ)) ≤ ∑ _m ∈ c.divisors, (c : ℝ) := by
          apply Finset.sum_le_sum; intro m hm
          exact_mod_cast Nat.divisor_le hm
      _ = (c : ℝ) * ((c.divisors.card : ℕ) : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hkey : ∀ c : ℕ,
      (c : ℝ) ^ (-(3 : ℝ) / 2) * ((c : ℝ) * ((c.divisors.card : ℕ) : ℝ))
        = (c : ℝ) ^ (-(1 : ℝ) / 2) * ((c.divisors.card : ℕ) : ℝ) := by
    intro c
    rcases eq_or_ne c 0 with rfl | hc0
    · simp
    · have hc0' : (0 : ℝ) < (c : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hc0
      have h3 : (c : ℝ) ^ (-(3 : ℝ) / 2) * (c : ℝ) = (c : ℝ) ^ (-(1 : ℝ) / 2) := by
        calc (c : ℝ) ^ (-(3 : ℝ) / 2) * (c : ℝ)
            = (c : ℝ) ^ (-(3 : ℝ) / 2) * (c : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = (c : ℝ) ^ (-(3 : ℝ) / 2 + 1) := (Real.rpow_add hc0' (-(3 : ℝ) / 2) 1).symm
          _ = (c : ℝ) ^ (-(1 : ℝ) / 2) := by congr 1; ring
      rw [← mul_assoc, h3]
  calc (∑ c ∈ n.divisors, ∑ m ∈ c.divisors, (m : ℝ) * (c : ℝ) ^ (-(3 : ℝ) / 2))
      = (∑ c ∈ n.divisors, (c : ℝ) ^ (-(3 : ℝ) / 2) * ∑ m ∈ c.divisors, (m : ℝ)) := by
        apply Finset.sum_congr rfl; intro c _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro m _; ring
    _ ≤ (∑ c ∈ n.divisors, (c : ℝ) ^ (-(3 : ℝ) / 2)
            * ((c : ℝ) * ((c.divisors.card : ℕ) : ℝ))) := by
        apply Finset.sum_le_sum; intro c _
        exact mul_le_mul_of_nonneg_left (hσ c) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = (∑ c ∈ n.divisors, (c : ℝ) ^ (-(1 : ℝ) / 2) * ((c.divisors.card : ℕ) : ℝ)) := by
        apply Finset.sum_congr rfl; intro c _; exact hkey c
    _ ≤ C0 * ((n.divisors.card : ℕ) : ℝ) := by
        have hb : ∀ c ∈ n.divisors,
            (c : ℝ) ^ (-(1 : ℝ) / 2) * ((c.divisors.card : ℕ) : ℝ) ≤ C0 := by
          intro c hcd
          have hc1 : 1 ≤ c := Nat.pos_of_mem_divisors hcd
          have hc0 : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc1
          have hτ : ((c.divisors.card : ℕ) : ℝ) ≤ C0 * (c : ℝ) ^ ((1 : ℝ) / 4) := hC0 c
          calc (c : ℝ) ^ (-(1 : ℝ) / 2) * ((c.divisors.card : ℕ) : ℝ)
              ≤ (c : ℝ) ^ (-(1 : ℝ) / 2) * (C0 * (c : ℝ) ^ ((1 : ℝ) / 4)) :=
                mul_le_mul_of_nonneg_left hτ (Real.rpow_nonneg hc0.le _)
            _ = C0 * ((c : ℝ) ^ (-(1 : ℝ) / 2) * (c : ℝ) ^ ((1 : ℝ) / 4)) := by ring
            _ = C0 * (c : ℝ) ^ (-(1 : ℝ) / 4) := by
                rw [← Real.rpow_add hc0 (-(1 : ℝ) / 2) ((1 : ℝ) / 4)]; congr 1; ring
            _ ≤ C0 * 1 := by
                apply mul_le_mul_of_nonneg_left _ (le_of_lt hC0pos)
                calc (c : ℝ) ^ (-(1 : ℝ) / 4) ≤ (c : ℝ) ^ (0 : ℝ) :=
                      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hc1) (by norm_num)
                  _ = 1 := Real.rpow_zero _
            _ = C0 := by ring
        calc (∑ c ∈ n.divisors, (c : ℝ) ^ (-(1 : ℝ) / 2) * ((c.divisors.card : ℕ) : ℝ))
            ≤ ∑ _c ∈ n.divisors, C0 := Finset.sum_le_sum hb
          _ = C0 * ((n.divisors.card : ℕ) : ℝ) := by
              rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- `Σ_{c | n} Σ_{m | c} c^{-3/4} ≤ C τ(n)` for an absolute constant `C`. -/
lemma dsum_cpow34 :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      (∑ c ∈ n.divisors, ∑ m ∈ c.divisors, (c : ℝ) ^ (-(3 : ℝ) / 4))
        ≤ C * ((n.divisors.card : ℕ) : ℝ) := by
  obtain ⟨C0, hC0pos, hC0⟩ :=
    Commons.NumberTheory.DivisorBound.card_divisors_le_rpow (1 / 4) (by norm_num)
  refine ⟨C0, hC0pos, ?_⟩
  intro n
  have hkey : ∀ c : ℕ, (∑ _m ∈ c.divisors, (c : ℝ) ^ (-(3 : ℝ) / 4))
      = (c : ℝ) ^ (-(3 : ℝ) / 4) * ((c.divisors.card : ℕ) : ℝ) := by
    intro c; rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  calc (∑ c ∈ n.divisors, ∑ m ∈ c.divisors, (c : ℝ) ^ (-(3 : ℝ) / 4))
      = (∑ c ∈ n.divisors, (c : ℝ) ^ (-(3 : ℝ) / 4) * ((c.divisors.card : ℕ) : ℝ)) := by
        apply Finset.sum_congr rfl; intro c _; exact hkey c
    _ ≤ C0 * ((n.divisors.card : ℕ) : ℝ) := by
        have hb : ∀ c ∈ n.divisors,
            (c : ℝ) ^ (-(3 : ℝ) / 4) * ((c.divisors.card : ℕ) : ℝ) ≤ C0 := by
          intro c hcd
          have hc1 : 1 ≤ c := Nat.pos_of_mem_divisors hcd
          have hc0 : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc1
          have hτ : ((c.divisors.card : ℕ) : ℝ) ≤ C0 * (c : ℝ) ^ ((1 : ℝ) / 4) := hC0 c
          calc (c : ℝ) ^ (-(3 : ℝ) / 4) * ((c.divisors.card : ℕ) : ℝ)
              ≤ (c : ℝ) ^ (-(3 : ℝ) / 4) * (C0 * (c : ℝ) ^ ((1 : ℝ) / 4)) :=
                mul_le_mul_of_nonneg_left hτ (Real.rpow_nonneg hc0.le _)
            _ = C0 * ((c : ℝ) ^ (-(3 : ℝ) / 4) * (c : ℝ) ^ ((1 : ℝ) / 4)) := by ring
            _ = C0 * (c : ℝ) ^ (-(1 : ℝ) / 2) := by
                rw [← Real.rpow_add hc0 (-(3 : ℝ) / 4) ((1 : ℝ) / 4)]; congr 1; ring
            _ ≤ C0 * 1 := by
                apply mul_le_mul_of_nonneg_left _ (le_of_lt hC0pos)
                calc (c : ℝ) ^ (-(1 : ℝ) / 2) ≤ (c : ℝ) ^ (0 : ℝ) :=
                      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hc1) (by norm_num)
                  _ = 1 := Real.rpow_zero _
            _ = C0 := by ring
        calc (∑ c ∈ n.divisors, (c : ℝ) ^ (-(3 : ℝ) / 4) * ((c.divisors.card : ℕ) : ℝ))
            ≤ ∑ _c ∈ n.divisors, C0 := Finset.sum_le_sum hb
          _ = C0 * ((n.divisors.card : ℕ) : ℝ) := by
              rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- `log (2x+1) ≤ C x^{ε/4}` for `x ≥ 1`, with `C` depending only on `ε > 0`. -/
lemma log_two_mul_add_le (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x → Real.log (2 * x + 1) ≤ C * x ^ (ε / 4) := by
  set a : ℝ := ε / 4 with ha
  have hapos : 0 < a := by rw [ha]; linarith
  refine ⟨4 ^ a / a + 1, by positivity, ?_⟩
  intro x hx
  have hxpos : 0 < x := lt_of_lt_of_le one_pos hx
  have h4 : 2 * x + 1 ≤ 4 * x := by linarith
  have hlog : Real.log (2 * x + 1) ≤ (2 * x + 1) ^ a / a :=
    Real.log_le_rpow_div (by linarith) hapos
  have hpow : (2 * x + 1) ^ a ≤ (4 * x) ^ a :=
    Real.rpow_le_rpow (by linarith) h4 (le_of_lt hapos)
  have h4x : (4 * x) ^ a = 4 ^ a * x ^ a := Real.mul_rpow (by norm_num) hxpos.le
  have hxa1 : 1 ≤ x ^ a := Real.one_le_rpow hx (le_of_lt hapos)
  have h4apos : 0 < 4 ^ a / a := by positivity
  calc Real.log (2 * x + 1) ≤ (2 * x + 1) ^ a / a := hlog
    _ ≤ (4 * x) ^ a / a := by
        rw [div_le_div_iff_of_pos_right hapos]; exact hpow
    _ = 4 ^ a * x ^ a / a := by rw [h4x]
    _ = (4 ^ a / a) * x ^ a := by ring
    _ ≤ (4 ^ a / a + 1) * x ^ a := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hxpos.le _)
        linarith
    _ = (4 ^ a / a + 1) * x ^ (ε / 4) := by rw [ha]

/-- `log (160 H) + 1 ≤ (log 80 + 1) (log (2H) + 1)` for `H ≥ 1`. -/
lemma log160_le_log2 (H : ℝ) (hH : 1 ≤ H) :
    Real.log (160 * H) + 1 ≤ (Real.log 80 + 1) * (Real.log (2 * H) + 1) := by
  have h2H : 0 < 2 * H := by linarith
  have h80 : 0 < (80 : ℝ) := by norm_num
  have h5 : (160 : ℝ) * H = 80 * (2 * H) := by ring
  have hlog : Real.log (160 * H) = Real.log 80 + Real.log (2 * H) := by
    rw [h5, Real.log_mul (ne_of_gt h80) (ne_of_gt h2H)]
  have hl2H : 0 ≤ Real.log (2 * H) := Real.log_nonneg (by linarith)
  have hl80 : 0 < Real.log 80 := Real.log_pos (by norm_num)
  rw [hlog]
  nlinarith [hl2H, hl80]

end
end Work.FIArea4.Vflip.Vfd
