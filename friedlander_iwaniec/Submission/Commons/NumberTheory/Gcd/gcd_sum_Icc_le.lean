import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.NumberTheory.Harmonic.Bounds

namespace Commons.NumberTheory.Gcd

open Finset

/-- Divisor-sum identity for `Nat.totient` in indicator form:
`n` equals the sum of `φ d` over `d ∈ [1,b]` dividing `n`, for `1 ≤ n ≤ b`. -/
lemma totient_indicator_sum (n b : ℕ) (hn : n ≠ 0) (hnb : n ≤ b) :
    (n : ℝ) = ∑ d ∈ Finset.Icc 1 b, (if d ∣ n then (Nat.totient d : ℝ) else 0) := by
  have hset : (Finset.Icc 1 b).filter (fun d => d ∣ n) = n.divisors := by
    ext d
    rw [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨hd, hdvd⟩
      exact ⟨hdvd, hn⟩
    · rintro ⟨hdvd, _⟩
      refine ⟨?_, hdvd⟩
      simp only [Finset.mem_Icc]
      exact ⟨Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hn),
             le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd) hnb⟩
  calc (n : ℝ) = ((n.divisors.sum Nat.totient : ℕ) : ℝ) := by rw [Nat.sum_totient]
    _ = ∑ d ∈ n.divisors, (Nat.totient d : ℝ) := by rw [Nat.cast_sum]
    _ = ∑ d ∈ (Finset.Icc 1 b).filter (fun d => d ∣ n), (Nat.totient d : ℝ) := by rw [← hset]
    _ = ∑ d ∈ Finset.Icc 1 b, (if d ∣ n then (Nat.totient d : ℝ) else 0) := by
          rw [Finset.sum_filter]

/-- The number of multiples of `d` in `[1,b]` is `b / d`. -/
lemma card_Icc_one_filter_dvd (b d : ℕ) :
    ((Finset.Icc 1 b).filter (fun l => d ∣ l)).card = b / d := by
  rw [← Nat.Ioc_filter_dvd_card_eq_div b d]
  apply congrArg Finset.card
  ext x
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
  omega

/-- `∑_{d ∈ [1,b]} 1/d = H_b`. -/
lemma sum_Icc_inv_eq_harmonic (b : ℕ) :
    (∑ d ∈ Finset.Icc 1 b, ((d : ℝ))⁻¹) = (harmonic b : ℝ) := by
  rw [harmonic_eq_sum_Icc, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Rat.cast_inv, Rat.cast_natCast]

/-- Sum of `gcd` over the square `[1,b]²`, evaluated via the totient function. -/
lemma sum_gcd_Icc_one_eq (b : ℕ) :
    (∑ l ∈ Finset.Icc 1 b, ∑ l' ∈ Finset.Icc 1 b, (Nat.gcd l l' : ℝ))
      = ∑ d ∈ Finset.Icc 1 b,
          (Nat.totient d : ℝ) * (((b / d : ℕ) : ℝ)) ^ 2 := by
  have hF : ∀ l ∈ Finset.Icc 1 b, ∀ l' ∈ Finset.Icc 1 b,
      (Nat.gcd l l' : ℝ) = ∑ d ∈ Finset.Icc 1 b,
          (if d ∣ l ∧ d ∣ l' then (Nat.totient d : ℝ) else 0) := by
    intro l hl l' hl'
    have hl1 : 1 ≤ l := (Finset.mem_Icc.mp hl).1
    have hl'1 : 1 ≤ l' := (Finset.mem_Icc.mp hl').1
    have hgpos : 0 < Nat.gcd l l' := Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left l l') (by omega)
    have hgb : Nat.gcd l l' ≤ b :=
      le_trans (Nat.gcd_le_right l (by omega)) (Finset.mem_Icc.mp hl').2
    rw [totient_indicator_sum (Nat.gcd l l') b (ne_of_gt hgpos) hgb]
    apply Finset.sum_congr rfl
    intro d hd
    simp only [Nat.dvd_gcd_iff]
  have h1 : (∑ l ∈ Finset.Icc 1 b, ∑ l' ∈ Finset.Icc 1 b, (Nat.gcd l l' : ℝ))
      = ∑ l ∈ Finset.Icc 1 b, ∑ l' ∈ Finset.Icc 1 b, ∑ d ∈ Finset.Icc 1 b,
          (if d ∣ l ∧ d ∣ l' then (Nat.totient d : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro l hl
    apply Finset.sum_congr rfl
    intro l' hl'
    exact hF l hl l' hl'
  have h2 : (∑ l ∈ Finset.Icc 1 b, ∑ l' ∈ Finset.Icc 1 b, ∑ d ∈ Finset.Icc 1 b,
          (if d ∣ l ∧ d ∣ l' then (Nat.totient d : ℝ) else 0))
      = ∑ l ∈ Finset.Icc 1 b, ∑ d ∈ Finset.Icc 1 b, ∑ l' ∈ Finset.Icc 1 b,
          (if d ∣ l ∧ d ∣ l' then (Nat.totient d : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro l hl
    rw [Finset.sum_comm]
  have h3 : (∑ l ∈ Finset.Icc 1 b, ∑ d ∈ Finset.Icc 1 b, ∑ l' ∈ Finset.Icc 1 b,
          (if d ∣ l ∧ d ∣ l' then (Nat.totient d : ℝ) else 0))
      = ∑ d ∈ Finset.Icc 1 b, ∑ l ∈ Finset.Icc 1 b, ∑ l' ∈ Finset.Icc 1 b,
          (if d ∣ l ∧ d ∣ l' then (Nat.totient d : ℝ) else 0) := Finset.sum_comm
  rw [h1, h2, h3]
  apply Finset.sum_congr rfl
  intro d hd
  have hinner : ∀ l ∈ Finset.Icc 1 b,
      (∑ l' ∈ Finset.Icc 1 b, (if d ∣ l ∧ d ∣ l' then (Nat.totient d : ℝ) else 0))
        = if d ∣ l
            then (((Finset.Icc 1 b).filter (fun l => d ∣ l)).card : ℝ) * (Nat.totient d : ℝ)
            else 0 := by
    intro l hl
    by_cases hdl : d ∣ l
    · rw [if_pos hdl]
      have hs : (∑ l' ∈ Finset.Icc 1 b,
            (if d ∣ l ∧ d ∣ l' then (Nat.totient d : ℝ) else 0))
          = ∑ l' ∈ Finset.Icc 1 b, (if d ∣ l' then (Nat.totient d : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro l' hl'
        simp [hdl]
      rw [hs, ← Finset.sum_filter]
      rw [Finset.sum_const, nsmul_eq_mul]
    · rw [if_neg hdl]
      apply Finset.sum_eq_zero
      intro l' hl'
      simp [hdl]
  calc (∑ l ∈ Finset.Icc 1 b, ∑ l' ∈ Finset.Icc 1 b,
          (if d ∣ l ∧ d ∣ l' then (Nat.totient d : ℝ) else 0))
      = ∑ l ∈ Finset.Icc 1 b, (if d ∣ l
            then (((Finset.Icc 1 b).filter (fun l => d ∣ l)).card : ℝ) * (Nat.totient d : ℝ)
            else 0) := Finset.sum_congr rfl hinner
    _ = ∑ l ∈ (Finset.Icc 1 b).filter (fun l => d ∣ l),
          ((((Finset.Icc 1 b).filter (fun l => d ∣ l)).card : ℝ) * (Nat.totient d : ℝ)) := by
          rw [Finset.sum_filter]
    _ = (((Finset.Icc 1 b).filter (fun l => d ∣ l)).card : ℝ)
          * ((((Finset.Icc 1 b).filter (fun l => d ∣ l)).card : ℝ) * (Nat.totient d : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ = (Nat.totient d : ℝ) * (((b / d : ℕ) : ℝ)) ^ 2 := by
          rw [card_Icc_one_filter_dvd]
          ring

/-- Bound for the totient weighted sum. -/
lemma sum_totient_mul_sq_le (b : ℕ) :
    (∑ d ∈ Finset.Icc 1 b, (Nat.totient d : ℝ) * (((b / d : ℕ) : ℝ)) ^ 2)
      ≤ 4 * (b : ℝ) ^ 2 * (Real.log (b : ℝ) + 1) := by
  have hstep : ∀ d ∈ Finset.Icc 1 b,
      (Nat.totient d : ℝ) * (((b / d : ℕ) : ℝ)) ^ 2 ≤ (b : ℝ) ^ 2 / (d : ℝ) := by
    intro d hd
    obtain ⟨hd1, hdb⟩ := Finset.mem_Icc.mp hd
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
    have hx : (((b / d : ℕ) : ℝ)) ≤ (b : ℝ) / (d : ℝ) := Nat.cast_div_le
    have hx0 : (0 : ℝ) ≤ ((b / d : ℕ) : ℝ) := by positivity
    have hphi : (Nat.totient d : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.totient_le d
    have hx2 : (((b / d : ℕ) : ℝ)) ^ 2 ≤ ((b : ℝ) / (d : ℝ)) ^ 2 :=
      pow_le_pow_left₀ hx0 hx 2
    calc (Nat.totient d : ℝ) * (((b / d : ℕ) : ℝ)) ^ 2
        ≤ (d : ℝ) * (((b / d : ℕ) : ℝ)) ^ 2 :=
          mul_le_mul_of_nonneg_right hphi (by positivity)
      _ ≤ (d : ℝ) * ((b : ℝ) / (d : ℝ)) ^ 2 :=
          mul_le_mul_of_nonneg_left hx2 (le_of_lt hdpos)
      _ = (b : ℝ) ^ 2 / (d : ℝ) := by
          field_simp
  calc (∑ d ∈ Finset.Icc 1 b, (Nat.totient d : ℝ) * (((b / d : ℕ) : ℝ)) ^ 2)
      ≤ ∑ d ∈ Finset.Icc 1 b, (b : ℝ) ^ 2 / (d : ℝ) := Finset.sum_le_sum hstep
    _ = (b : ℝ) ^ 2 * (∑ d ∈ Finset.Icc 1 b, ((d : ℝ))⁻¹) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d hd
        ring
    _ = (b : ℝ) ^ 2 * (harmonic b : ℝ) := by rw [sum_Icc_inv_eq_harmonic]
    _ ≤ (b : ℝ) ^ 2 * (1 + Real.log (b : ℝ)) :=
        mul_le_mul_of_nonneg_left (harmonic_le_one_add_log b) (by positivity)
    _ ≤ 4 * (b : ℝ) ^ 2 * (Real.log (b : ℝ) + 1) := by
        rcases Nat.eq_zero_or_pos b with hb0 | hb1
        · subst hb0; simp
        · have hb1' : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb1
          have hlog : 0 ≤ Real.log (b : ℝ) := Real.log_nonneg hb1'
          nlinarith [sq_nonneg (b : ℝ)]

theorem gcd_sum_Icc_le (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    (∑ l ∈ Finset.Icc a b, ∑ l' ∈ Finset.Icc a b, (Nat.gcd l l' : ℝ))
      ≤ 4 * (b : ℝ) ^ 2 * (Real.log (b : ℝ) + 1) := by
  have _ := hab
  have hsub : Finset.Icc a b ⊆ Finset.Icc 1 b := by
    intro x hx
    simp only [Finset.mem_Icc] at hx ⊢
    omega
  calc (∑ l ∈ Finset.Icc a b, ∑ l' ∈ Finset.Icc a b, (Nat.gcd l l' : ℝ))
      ≤ ∑ l ∈ Finset.Icc 1 b, ∑ l' ∈ Finset.Icc a b, (Nat.gcd l l' : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro l hl hnl
        apply Finset.sum_nonneg
        intro l' hl'
        exact Nat.cast_nonneg _
    _ ≤ ∑ l ∈ Finset.Icc 1 b, ∑ l' ∈ Finset.Icc 1 b, (Nat.gcd l l' : ℝ) := by
        apply Finset.sum_le_sum
        intro l hl
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro l' hl' hnl
        exact Nat.cast_nonneg _
    _ = ∑ d ∈ Finset.Icc 1 b, (Nat.totient d : ℝ) * (((b / d : ℕ) : ℝ)) ^ 2 :=
        sum_gcd_Icc_one_eq b
    _ ≤ 4 * (b : ℝ) ^ 2 * (Real.log (b : ℝ) + 1) := sum_totient_mul_sq_le b

end Commons.NumberTheory.Gcd