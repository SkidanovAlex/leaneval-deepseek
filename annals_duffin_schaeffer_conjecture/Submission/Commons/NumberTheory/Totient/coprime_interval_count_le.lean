import Mathlib
import Submission.Commons.NumberTheory.Totient.coprime_window_mainTerm_bound
import Submission.Commons.NumberTheory.Nat.indicator_coprime_primeFactors_sum
import Submission.Commons.NumberTheory.Nat.main_term_eq_mul_prod_sub
import Submission.Commons.Data.Nat.nat_div_le_real_div
import Submission.Commons.Data.Nat.real_div_lt_nat_div_add_one
import Submission.Commons.Data.Finset.card_powerset_filter_odd

/-!
# The crude window bound for the Duffin–Schaeffer counting

For every `M ≥ 2` and every natural `x`,

`#{c ∈ [1,x] : (c,M) = 1} ≤ x·φ(M)/M + 2^(ω(M) − 1)`

where `ω(M)` is the number of distinct prime factors of `M`.

The proof expands the coprime count by inclusion–exclusion over the subsets
`S` of the set of prime factors of `M`:

`#{c ∈ [1,x] : (c,M)=1} = Σ_{S} (−1)^{|S|}·⌊x/∏_{p∈S}p⌋`,

while Euler's product formula `φ(M)/M = ∏_{p|M}(1 − 1/p)` gives the same
expansion for the main term with real division:

`x·φ(M)/M = Σ_{S} (−1)^{|S|}·x/∏_{p∈S}p`.

The discrepancy is therefore a weighted sum of the fractional parts
`{x/∏_{p∈S}p}`; the `+`-terms (odd-cardinality subsets) alone are bounded by
their number `2^(ω(M)−1)`, and the `−`-terms (even-cardinality subsets) are
non-positive.
-/

namespace Commons.NumberTheory.Totient

open scoped BigOperators
open scoped BigOperators

/-- Euler's product formula for `φ(n)/n` over the reals: for `n ≠ 0`,
`φ(n)/n = ∏_{p | n} (1 - 1/p)`. -/
private lemma totient_ratio_real_prod (n : ℕ) (hn : n ≠ 0) :
    (Nat.totient n : ℝ) / (n : ℝ) = ∏ p ∈ n.primeFactors, (1 - (1 : ℝ) / (p : ℝ)) := by
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  have hq : (Nat.totient n : ℚ) / (n : ℚ) = ∏ p ∈ n.primeFactors, (1 - (p : ℚ)⁻¹) := by
    rw [Nat.totient_eq_mul_prod_factors]
    field_simp [hnQ]
  calc
    (Nat.totient n : ℝ) / (n : ℝ) = (((Nat.totient n : ℚ) / (n : ℚ) : ℚ) : ℝ) := by
      norm_num [Rat.cast_div]
    _ = ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) := by
      have hc := congrArg (fun q : ℚ => (q : ℝ)) hq
      simpa [Rat.cast_div] using hc
    _ = ∏ p ∈ n.primeFactors, (1 - (1 : ℝ) / (p : ℝ)) := by
      refine Finset.prod_congr rfl ?_
      intro p hp
      rw [one_div]

/-- Inclusion–exclusion for the coprime count in `[1,x]` over the subsets of
the prime factors of `M`: `#{c ∈ [1,x] : (c,M)=1} = Σ_{S} (−1)^{|S|}⌊x/∏S⌋`. -/
private lemma count_coprime_Icc_powerset (M x : ℕ) (hM0 : M ≠ 0) :
    (((Finset.Icc 1 x).filter (fun s : ℕ => Nat.Coprime s M)).card : ℝ) =
      ∑ S ∈ M.primeFactors.powerset,
        (-1 : ℝ) ^ S.card * ((x / (∏ p ∈ S, p) : ℕ) : ℝ) := by
  classical
  calc
    (((Finset.Icc 1 x).filter (fun s : ℕ => Nat.Coprime s M)).card : ℝ)
        = ∑ s ∈ (Finset.Icc 1 x), (if Nat.Coprime s M then (1 : ℝ) else 0) := by
            rw [Finset.sum_boole]
    _ = ∑ s ∈ (Finset.Icc 1 x),
          (∑ S ∈ M.primeFactors.powerset,
            (-1 : ℝ) ^ S.card * (if (∏ p ∈ S, p) ∣ s then (1 : ℝ) else 0)) := by
            apply Finset.sum_congr rfl
            intro s hs
            exact (Commons.NumberTheory.Nat.indicator_coprime_primeFactors_sum (q := M) (x := s) hM0)
    _ = ∑ S ∈ M.primeFactors.powerset,
          (∑ s ∈ (Finset.Icc 1 x),
            (-1 : ℝ) ^ S.card * (if (∏ p ∈ S, p) ∣ s then (1 : ℝ) else 0)) := by
            rw [Finset.sum_comm]
    _ = ∑ S ∈ M.primeFactors.powerset,
          (-1 : ℝ) ^ S.card *
            (∑ s ∈ (Finset.Icc 1 x), (if (∏ p ∈ S, p) ∣ s then (1 : ℝ) else 0)) := by
            apply Finset.sum_congr rfl
            intro S hS
            rw [← Finset.mul_sum]
    _ = ∑ S ∈ M.primeFactors.powerset,
          (-1 : ℝ) ^ S.card * ((x / (∏ p ∈ S, p) : ℕ) : ℝ) := by
            apply Finset.sum_congr rfl
            intro S hS
            congr 1
            rw [Finset.sum_boole (p := fun s : ℕ => (∏ p ∈ S, p) ∣ s)]
            exact_mod_cast (card_multiples_Icc_one (∏ p ∈ S, p) x)

/-- Inclusion–exclusion for the main term: `x·φ(M)/M = Σ_{S} (−1)^{|S|}·x/∏S`
(real divisions), via Euler's product formula and the subset expansion of
`∏_{p|M}(1 − 1/p)`. -/
private lemma main_term_powerset (M x : ℕ) (hM0 : M ≠ 0) :
    (x : ℝ) * (Nat.totient M : ℝ) / (M : ℝ) =
      ∑ S ∈ M.primeFactors.powerset,
        (-1 : ℝ) ^ S.card * ((x : ℝ) / (∏ p ∈ S, (p : ℝ))) := by
  have hMℝ : (M : ℝ) ≠ 0 := by exact_mod_cast hM0
  have hφ : (Nat.totient M : ℝ) / (M : ℝ) =
      ∏ p ∈ M.primeFactors, (1 - (1 : ℝ) / (p : ℝ)) := totient_ratio_real_prod M hM0
  calc
    (x : ℝ) * (Nat.totient M : ℝ) / (M : ℝ)
        = (x : ℝ) * ((Nat.totient M : ℝ) / (M : ℝ)) := by
            field_simp [hMℝ]
    _ = (x : ℝ) * (∏ p ∈ M.primeFactors, (1 - (1 : ℝ) / (p : ℝ))) := by rw [hφ]
    _ = ∑ S ∈ M.primeFactors.powerset,
          (-1 : ℝ) ^ S.card * ((x : ℝ) / (∏ p ∈ S, (p : ℝ))) := by
          exact (Commons.NumberTheory.Nat.main_term_eq_mul_prod_sub M x).symm

/-- Pointwise discrepancy bound: for each subset `S` of the prime factors,
`(−1)^{|S|}·(⌊x/∏S⌋ − x/∏S) ≤ [|S| odd]`, since `⌊x/d⌋ − x/d ≤ 0` and
`x/d − ⌊x/d⌋ < 1`. -/
private lemma subset_term_le (x : ℕ) (S : Finset ℕ) :
    (-1 : ℝ) ^ S.card *
        (((x / (∏ p ∈ S, p) : ℕ) : ℝ) - (x : ℝ) / (∏ p ∈ S, (p : ℝ))) ≤
      (if Odd S.card then (1 : ℝ) else 0) := by
  classical
  have hconv : (x : ℝ) / (∏ p ∈ S, (p : ℝ)) = (x : ℝ) / ((∏ p ∈ S, p : ℕ) : ℝ) := by
    rw [← Nat.cast_prod]
  rw [hconv]
  let d : ℕ := ∏ p ∈ S, p
  by_cases hodd : Odd S.card
  · have hneg : (-1 : ℝ) ^ S.card = -1 := Odd.neg_one_pow hodd
    rw [if_pos hodd, hneg]
    have hlt := Commons.Data.Nat.real_div_lt_nat_div_add_one x d
    linarith
  · have heven : Even S.card := Nat.not_odd_iff_even.mp hodd
    have hone : (-1 : ℝ) ^ S.card = 1 := Even.neg_one_pow heven
    rw [if_neg hodd, hone]
    have hle := Commons.Data.Nat.nat_div_le_real_div x d
    linarith

/-- An integer `M ≥ 2` has at least one prime factor. -/
private lemma primeFactors_ne_empty_of_two_le (M : ℕ) (hM : 2 ≤ M) : M.primeFactors ≠ ∅ := by
  have hM1 : M ≠ 1 := by omega
  have hM0 : M ≠ 0 := by omega
  rcases Nat.exists_prime_and_dvd hM1 with ⟨p, hpP, hpd⟩
  exact Finset.nonempty_iff_ne_empty.mp ⟨p, Nat.mem_primeFactors.mpr ⟨hpP, hpd, hM0⟩⟩

/-- The main estimate, in the `Nat.Coprime` formulation: the number of
`c ∈ [1,x]` coprime to `M` is at most `x·φ(M)/M + 2^(ω(M) − 1)`. -/
private lemma count_coprime_Icc_le_main (M x : ℕ) (hM0 : M ≠ 0) (hM2 : 2 ≤ M) :
    (((Finset.Icc 1 x).filter (fun s : ℕ => Nat.Coprime s M)).card : ℝ) ≤
      (x : ℝ) * (Nat.totient M : ℝ) / (M : ℝ) +
        (2 : ℝ) ^ (M.primeFactors.card - 1) := by
  classical
  set P : Finset ℕ := M.primeFactors
  have hcnt := count_coprime_Icc_powerset M x hM0
  have hmain := main_term_powerset M x hM0
  have hdiff :
      (((Finset.Icc 1 x).filter (fun s : ℕ => Nat.Coprime s M)).card : ℝ) -
        (x : ℝ) * (Nat.totient M : ℝ) / (M : ℝ) =
      ∑ S ∈ P.powerset,
        (-1 : ℝ) ^ S.card *
          (((x / (∏ p ∈ S, p) : ℕ) : ℝ) - (x : ℝ) / (∏ p ∈ S, (p : ℝ))) := by
    dsimp [P]
    rw [hcnt, hmain]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro S hS
    ring
  have hbd :
      (((Finset.Icc 1 x).filter (fun s : ℕ => Nat.Coprime s M)).card : ℝ) -
        (x : ℝ) * (Nat.totient M : ℝ) / (M : ℝ) ≤ (2 : ℝ) ^ (P.card - 1) := by
    rw [hdiff]
    calc
      (∑ S ∈ P.powerset,
          (-1 : ℝ) ^ S.card *
            (((x / (∏ p ∈ S, p) : ℕ) : ℝ) - (x : ℝ) / (∏ p ∈ S, (p : ℝ))))
          ≤ ∑ S ∈ P.powerset, (if Odd S.card then (1 : ℝ) else 0) := by
              apply Finset.sum_le_sum
              intro S hS
              exact subset_term_le x S
      _ = ((P.powerset.filter (fun S : Finset ℕ => Odd S.card)).card : ℝ) := by
              rw [Finset.sum_boole (p := fun S : Finset ℕ => Odd S.card)]
      _ = (2 : ℝ) ^ (P.card - 1) := by
              have hω : P ≠ ∅ := by
                dsimp [P]
                exact primeFactors_ne_empty_of_two_le M hM2
              rw [Commons.Data.Finset.card_powerset_filter_odd P hω]
              norm_num [Nat.cast_pow]
  rw [show P.card = M.primeFactors.card by rfl]
  linarith

/-- **Crude window bound for coprime counts.**  For `M ≥ 2` and every natural
`x`, the number of `s ∈ [1,x]` with `(s,M) = 1` is at most
`x·φ(M)/M + 2^(ω(M) − 1)`, where `ω(M)` is the number of distinct prime
factors of `M`. -/
theorem coprime_interval_count_le (M x : ℕ) (hM : 2 ≤ M) :
    (((Finset.Icc 1 x).filter (fun s : ℕ => s.gcd M = 1)).card : ℝ) ≤
      (x : ℝ) * ((M.totient : ℕ) : ℝ) / (M : ℝ) +
        (2 : ℝ) ^ (M.primeFactors.card - 1) := by
  classical
  have hM0 : M ≠ 0 := by omega
  have h := count_coprime_Icc_le_main M x hM0 hM
  simpa [Nat.Coprime] using h

end Commons.NumberTheory.Totient
