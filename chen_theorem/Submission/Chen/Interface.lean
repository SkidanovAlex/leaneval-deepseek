import Mathlib
import ChallengeDeps

open LeanEval.NumberTheory.ChenTheorem
open scoped BigOperators
open scoped ArithmeticFunction.Omega

namespace Submission

/-- For `n ≥ 2`, `HasAtMostTwoPrimeFactors n` holds iff `n` has at most two prime
factors counted with multiplicity (mathlib's `Ω`). -/
theorem hasAtMostTwoPrimeFactors_iff_cardFactors_le_two_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    HasAtMostTwoPrimeFactors n ↔ ArithmeticFunction.cardFactors n ≤ 2 := by
  constructor
  · intro h
    rcases h with (⟨a, ha, h⟩ | ⟨a, b, ha, hb, h⟩)
    · rw [h]
      rw [ArithmeticFunction.cardFactors_apply_prime ha]
      omega
    · rw [h]
      rw [ArithmeticFunction.cardFactors_mul ha.ne_zero hb.ne_zero]
      rw [ArithmeticFunction.cardFactors_apply_prime ha,
        ArithmeticFunction.cardFactors_apply_prime hb]
  · intro hΩ
    have hn1 : n ≠ 1 := by omega
    obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hn1
    obtain ⟨m, hm⟩ := hqdvd
    have hqne0 : q ≠ 0 := hq.ne_zero
    have hm0 : m ≠ 0 := by
      intro hmz
      subst m
      have hz : n = 0 := by simpa using hm
      omega
    have hsplit : ArithmeticFunction.cardFactors (q * m) = 1 + ArithmeticFunction.cardFactors m := by
      rw [ArithmeticFunction.cardFactors_mul hqne0 hm0]
      rw [ArithmeticFunction.cardFactors_apply_prime hq]
    have hΩ' : ArithmeticFunction.cardFactors (q * m) ≤ 2 := by
      simpa [hm] using hΩ
    have hΩm : ArithmeticFunction.cardFactors m ≤ 1 := by
      rw [hsplit] at hΩ'
      omega
    by_cases hm1 : m = 1
    · left
      refine ⟨q, hq, ?_⟩
      rw [hm1] at hm
      simpa using hm
    · right
      have hΩm' : ArithmeticFunction.cardFactors m = 0 ∨ ArithmeticFunction.cardFactors m = 1 := by omega
      rcases hΩm' with h0 | h1
      · exfalso
        have : m = 0 ∨ m = 1 := (ArithmeticFunction.cardFactors_eq_zero_iff_eq_zero_or_one).mp h0
        rcases this with hmm | hmm
        · exact hm0 hmm
        · exact hm1 hmm
      · refine ⟨q, m, hq, (ArithmeticFunction.cardFactors_eq_one_iff_prime).mp h1, hm⟩

/-- Specialised to `p + 2` (always `≥ 2`). -/
theorem hasAtMostTwoPrimeFactors_add_two_iff {p : ℕ} :
    HasAtMostTwoPrimeFactors (p + 2) ↔ ArithmeticFunction.cardFactors (p + 2) ≤ 2 :=
  hasAtMostTwoPrimeFactors_iff_cardFactors_le_two_of_two_le (n := p + 2) (by omega)

/-- The set of primes `p` such that `p + 2` has at most two prime factors
(counted with multiplicity). Equivalent to the set in the challenge statement. -/
def chenSetOmega : Set ℕ := {p : ℕ | p.Prime ∧ ArithmeticFunction.cardFactors (p + 2) ≤ 2}

/-- The challenge set, `p` prime with `HasAtMostTwoPrimeFactors (p+2)`. -/
def chenSet : Set ℕ := {p : ℕ | p.Prime ∧ HasAtMostTwoPrimeFactors (p + 2)}

theorem chenSet_eq_chenSetOmega : chenSet = chenSetOmega := by
  ext p
  constructor <;> intro h
  · exact ⟨h.1, (hasAtMostTwoPrimeFactors_add_two_iff (p := p)).mp h.2⟩
  · exact ⟨h.1, (hasAtMostTwoPrimeFactors_add_two_iff (p := p)).mpr h.2⟩

/-- Number of elements of `chenSetOmega` that are `≤ x`. -/
noncomputable def chenCount (x : ℕ) : ℕ := by
  classical
  exact ((Finset.range (x + 1)).filter fun p => p ∈ chenSetOmega).card

/-- If `chenCount` is unbounded above, then `chenSetOmega` is not bounded above. -/
lemma not_bddAbove_chenSetOmega_of_count_unbounded
    (h : ∀ B : ℕ, ∃ x : ℕ, B < chenCount x) : ¬ BddAbove chenSetOmega := by
  rw [not_bddAbove_iff]
  classical
  intro M
  obtain ⟨x, hx⟩ := h (M + 1)
  by_contra hc
  have hle_all : ∀ p ∈ chenSetOmega, p ≤ M := by
    intro p hpS
    by_contra hle_not
    exact hc ⟨p, hpS, lt_of_not_ge hle_not⟩
  have hle : chenCount x ≤ M + 1 := by
    unfold chenCount
    have hsub : (Finset.range (x + 1)).filter (fun p => p ∈ chenSetOmega) ⊆
        Finset.range (M + 1) := by
      intro p hp
      simp only [Finset.mem_filter] at hp
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hle_all p hp.right))
    simpa [Finset.card_range] using Finset.card_le_card hsub
  exact (not_lt_of_ge hle) hx

/-- An unbounded count of Chen-prime candidates forces the challenge set to be
infinite. -/
theorem chen_infinite_of_count_unbounded (h : ∀ B : ℕ, ∃ x : ℕ, B < chenCount x) :
    chenSet.Infinite := by
  have hinfΩ : chenSetOmega.Infinite :=
    Set.infinite_of_not_bddAbove (not_bddAbove_chenSetOmega_of_count_unbounded h)
  exact chenSet_eq_chenSetOmega.symm ▸ hinfΩ


/-- `chenCount` is monotone in `x`. -/
theorem chenCount_mono {x y : ℕ} (hxy : x ≤ y) : chenCount x ≤ chenCount y := by
  classical
  unfold chenCount
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
  constructor
  · omega
  · exact hp.2


/-- Replica of `chenCount` with the counting predicate inlined (no reference to
the package's sets), matching word-for-word the statement of Chen's rate estimate
as it appears in the shared commons
(`Commons.NumberTheory.Chen.chen_rate_estimate`). -/
noncomputable def chenCountInlined (x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter
    (fun p => p.Prime ∧ ArithmeticFunction.cardFactors (p + 2) ≤ 2)).card

/-- `chenCount` and the inlined replica agree. -/
theorem chenCount_eq_chenCountInlined (x : ℕ) :
    chenCount x = chenCountInlined x := by
  classical
  unfold chenCount chenCountInlined
  congr 1
  apply Finset.filter_congr
  intro p hp
  rfl

end Submission
