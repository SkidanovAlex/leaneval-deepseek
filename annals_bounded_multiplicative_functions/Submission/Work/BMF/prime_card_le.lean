import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.primesIn_card_le_pi0

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- Chebyshev-type bound for the number of primes in a short interval `[a, b]` with
`b ≤ 7a/5`: since `b ≤ 2a`, the primes in `[a, b]` are a subset of those in `[a, 2a]`,
and `primesIn_card_le_pi0` bounds the latter by `C · π₀(a) = C · a/log a`. -/
theorem prime_card_le : ∃ C P₀ : ℝ, 0 < C ∧ 0 < P₀ ∧ ∀ a b : ℝ, P₀ ≤ a → a ≤ b → b ≤ 7 * a / 5 →
    ((primesIn a b).card : ℝ) ≤ C * pi0 a := by
  obtain ⟨C, Q, hC, hbound⟩ := primesIn_card_le_pi0
  refine ⟨C, max Q 1, hC, lt_of_lt_of_le zero_lt_one (le_max_right Q 1), ?_⟩
  intro a b hP₀ _hb_le_7 hb
  have hQ : Q ≤ a := le_trans (le_max_left Q 1) hP₀
  have ha1 : (1 : ℝ) ≤ a := le_trans (le_max_right Q 1) hP₀
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hb2a : b ≤ 2 * a := by linarith
  have hsubset : primesIn a b ⊆ primesIn a (2 * a) := by
    intro p hp
    simp only [primesIn, natIcc, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
    exact ⟨⟨hp.1.1, le_trans hp.1.2 (Nat.floor_mono hb2a)⟩, hp.2⟩
  calc ((primesIn a b).card : ℝ)
      ≤ ((primesIn a (2 * a)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsubset
    _ ≤ C * pi0 a := hbound a hQ

end Work.BMF
