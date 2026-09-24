import Mathlib
import Submission.Commons.NumberTheory.DivisorSum.sum_divisor_count_div_le
import Submission.Commons.Data.Nat.mul_div_gcd_eq_lcm

namespace Commons.NumberTheory.DivisorBound

open Finset

/-- The number of pairs `(a,b)` with `1 ≤ a,b ≤ V` and `lcm a b ≤ x` is at most
`x * (1 + log V)^2`.

The proof parametrizes a pair by `b` together with the pair
`(gcd a b, a / gcd a b)`: the second coordinate is at most `x / b` because
`lcm a b = b * (a / gcd a b)`, while the first is a divisor of `b`.  This gives
an injection into `⨆_{b ≤ V} divisors b × [1, x/b]`, whose cardinality is
`∑_{b ≤ V} d(b) * ⌊x/b⌋ ≤ x · ∑_{b ≤ V} d(b)/b`, and the last sum is bounded by
`∑_{d ≤ V} (1/d) · H_V ≤ (1 + log V)^2`. -/
theorem pair_lcm_count_bound (x V : ℕ) :
    (((Finset.Icc 1 V).product (Finset.Icc 1 V)).filter (fun p => Nat.lcm p.1 p.2 ≤ x)).card
      ≤ x * (1 + Real.log V) ^ 2 := by
  classical
  change ((((Finset.Icc 1 V) ×ˢ (Finset.Icc 1 V)).filter
      (fun p => Nat.lcm p.1 p.2 ≤ x)).card : ℝ)
        ≤ (x : ℝ) * (1 + Real.log (V : ℝ)) ^ 2
  by_cases hV : V = 0
  · subst hV
    simp [Real.log_zero]
  · have hV1 : 1 ≤ V := by omega
    set S := ((Finset.Icc 1 V) ×ˢ (Finset.Icc 1 V)).filter
        (fun p => Nat.lcm p.1 p.2 ≤ x) with hS
    set T : Finset (Σ _b : ℕ, ℕ × ℕ) :=
        (Finset.Icc 1 V).sigma (fun b => (Nat.divisors b) ×ˢ (Finset.Icc 1 (x / b)))
      with hT
    set f : ℕ × ℕ → (Σ _b : ℕ, ℕ × ℕ) :=
        fun p => ⟨p.2, (Nat.gcd p.1 p.2, p.1 / Nat.gcd p.1 p.2)⟩ with hf
    have hcard : S.card ≤ T.card := by
      apply Finset.card_le_card_of_injOn f
      · -- the map lands in `T`
        intro p hpMem
        have hp' : p ∈ S := hpMem
        rw [hS] at hp'
        rw [Finset.mem_filter] at hp'
        obtain ⟨hp_prod, hplcm⟩ := hp'
        rw [Finset.mem_product] at hp_prod
        obtain ⟨hp1, hp2⟩ := hp_prod
        have hp1' : 1 ≤ p.1 := (Finset.mem_Icc.mp hp1).1
        have hb1 : 1 ≤ p.2 := (Finset.mem_Icc.mp hp2).1
        have hb0 : 0 < p.2 := hb1
        have hbne : p.2 ≠ 0 := by omega
        have hdiv : p.1 / Nat.gcd p.1 p.2 * Nat.gcd p.1 p.2 = p.1 :=
          Nat.div_mul_cancel (Nat.gcd_dvd_left p.1 p.2)
        have hs1 : 1 ≤ p.1 / Nat.gcd p.1 p.2 := by
          rcases Nat.eq_zero_or_pos (p.1 / Nat.gcd p.1 p.2) with h | h
          · rw [h, zero_mul] at hdiv; omega
          · exact h
        have hlcm : p.2 * (p.1 / Nat.gcd p.1 p.2) = Nat.lcm p.1 p.2 := by
          have h := Commons.Data.Nat.mul_div_gcd_eq_lcm p.2 p.1
          rw [Nat.gcd_comm, Nat.lcm_comm] at h
          exact h
        have hsle : p.1 / Nat.gcd p.1 p.2 ≤ x / p.2 := by
          rw [Nat.le_div_iff_mul_le hb0]
          calc p.1 / Nat.gcd p.1 p.2 * p.2 = p.2 * (p.1 / Nat.gcd p.1 p.2) :=
                Nat.mul_comm _ _
            _ = Nat.lcm p.1 p.2 := hlcm
            _ ≤ x := hplcm
        change f p ∈ T
        rw [hf, hT, Finset.mem_sigma]
        refine ⟨hp2, ?_⟩
        rw [Finset.mem_product]
        exact ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right p.1 p.2, hbne⟩,
               Finset.mem_Icc.mpr ⟨hs1, hsle⟩⟩
      · -- injectivity
        intro p _hp q _hq hpq
        simp only [hf] at hpq
        have hb : p.2 = q.2 := by
          simpa using congrArg (fun z : (Σ _b : ℕ, ℕ × ℕ) => z.1) hpq
        have h2 : (Nat.gcd p.1 p.2, p.1 / Nat.gcd p.1 p.2)
            = (Nat.gcd q.1 q.2, q.1 / Nat.gcd q.1 q.2) := by
          simpa using congrArg (fun z : (Σ _b : ℕ, ℕ × ℕ) => z.2) hpq
        have hg' : Nat.gcd p.1 p.2 = Nat.gcd q.1 q.2 := by
          simpa using congrArg (fun z : ℕ × ℕ => z.1) h2
        have hs' : p.1 / Nat.gcd p.1 p.2 = q.1 / Nat.gcd q.1 q.2 := by
          simpa using congrArg (fun z : ℕ × ℕ => z.2) h2
        have h1 : p.1 = q.1 := by
          calc p.1 = p.1 / Nat.gcd p.1 p.2 * Nat.gcd p.1 p.2 :=
                (Nat.div_mul_cancel (Nat.gcd_dvd_left p.1 p.2)).symm
            _ = q.1 / Nat.gcd q.1 q.2 * Nat.gcd q.1 q.2 := by rw [hs', hg']
            _ = q.1 := Nat.div_mul_cancel (Nat.gcd_dvd_left q.1 q.2)
        exact Prod.ext h1 hb
    have hTcard_nat : T.card = ∑ b ∈ Finset.Icc 1 V, (Nat.divisors b).card * (x / b) := by
      rw [hT]
      rw [Finset.card_sigma]
      apply Finset.sum_congr rfl
      intro b _hb
      rw [Finset.card_product, Nat.card_Icc, Nat.add_sub_cancel]
    have hTc : (T.card : ℝ)
        = ∑ b ∈ Finset.Icc 1 V, ((Nat.divisors b).card : ℝ) * ((x / b : ℕ) : ℝ) := by
      rw [hTcard_nat]
      push_cast
      rfl
    have hTbound : (T.card : ℝ)
        ≤ (x : ℝ) * ∑ b ∈ Finset.Icc 1 V, ((Nat.divisors b).card : ℝ) / (b : ℝ) := by
      rw [hTc, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro b hb
      have hdiv : ((x / b : ℕ) : ℝ) ≤ (x : ℝ) / (b : ℝ) := Nat.cast_div_le
      have hdnn : (0 : ℝ) ≤ ((Nat.divisors b).card : ℝ) := by positivity
      calc ((Nat.divisors b).card : ℝ) * ((x / b : ℕ) : ℝ)
          ≤ ((Nat.divisors b).card : ℝ) * ((x : ℝ) / (b : ℝ)) :=
            mul_le_mul_of_nonneg_left hdiv hdnn
        _ = (x : ℝ) * (((Nat.divisors b).card : ℝ) / (b : ℝ)) := by
            rw [div_eq_mul_inv, div_eq_mul_inv]; ring
    have hsum : ∑ b ∈ Finset.Icc 1 V, ((Nat.divisors b).card : ℝ) / (b : ℝ)
        ≤ (1 + Real.log V) ^ 2 :=
      Commons.NumberTheory.DivisorSum.sum_divisor_count_div_le V hV1
    calc (S.card : ℝ) ≤ (T.card : ℝ) := by exact_mod_cast hcard
      _ ≤ (x : ℝ) * ∑ b ∈ Finset.Icc 1 V, ((Nat.divisors b).card : ℝ) / (b : ℝ) := hTbound
      _ ≤ (x : ℝ) * (1 + Real.log V) ^ 2 :=
            mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg x)

end Commons.NumberTheory.DivisorBound
