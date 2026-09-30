import Submission.Vinogradov.ChallengeDeps

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.NumberTheory.VinogradovMeanValue
open scoped BigOperators

set_option autoImplicit false

namespace Submission.Vinogradov

noncomputable section
open Classical

/-- The pair space of two `s`-tuples with entries in `[1, X]`. -/
abbrev PairSpace (s X : ℕ) : Type :=
  (Fin s → Finset.Icc 1 X) × (Fin s → Finset.Icc 1 X)

/-- The moment-matching condition (for moments of degree up to `k`). -/
abbrev Matches (s k X : ℕ) (xy : PairSpace s X) : Prop :=
  ∀ j ≤ k, (∑ i, (xy.1 i).1 ^ j) = (∑ i, (xy.2 i).1 ^ j)

/-- The count `J` is the cardinal of the matching pairs. -/
lemma J_eq_filter_card (s k X : ℕ) :
    J s k X = ((Finset.univ.filter (Matches s k X)).card : ℝ) := by
  rfl

/-- The number of pairs of `s`-tuples with entries in `[1, X]` is `(X^s)^2`. -/
lemma univ_card (s X : ℕ) :
    (Finset.univ : Finset (PairSpace s X)).card = (X ^ s) ^ 2 := by
  rw [show (X ^ s) ^ 2 = X ^ s * X ^ s by rw [pow_two]]
  simp [Nat.card_Icc]

/-- `J s k X` is a cardinality (a natural number) viewed in `ℝ`, so it is nonnegative. -/
lemma J_nonneg (s k X : ℕ) : 0 ≤ J s k X := by
  rw [J_eq_filter_card]
  exact_mod_cast Nat.zero_le _

/-- Trivial bound: at most all pairs can satisfy the matching condition. -/
lemma J_le_card (s k X : ℕ) : J s k X ≤ ((X ^ s) ^ 2 : ℕ) := by
  rw [J_eq_filter_card]
  have hle : (Finset.univ.filter (Matches s k X)).card ≤
      (Finset.univ : Finset (PairSpace s X)).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  rw [univ_card] at hle
  exact_mod_cast hle

/-- For `s = 0` the empty pair is the only pair. -/
lemma J_eq_one_s0 (k X : ℕ) : J 0 k X = 1 := by
  rw [J_eq_filter_card]
  have hEq : (Finset.univ.filter (Matches 0 k X)) = (Finset.univ : Finset (PairSpace 0 X)) := by
    ext xy
    simp [Matches]
  rw [hEq, Finset.card_univ]
  simp

/-- More equations can only decrease the number of solutions: `J s k` is
antitone in `k`. -/
lemma J_antitone_k {s k k' X : ℕ} (hkk' : k' ≤ k) : J s k X ≤ J s k' X := by
  rw [J_eq_filter_card, J_eq_filter_card]
  have hsub : (Finset.univ.filter (Matches s k X)) ⊆
      (Finset.univ.filter (Matches s k' X)) := by
    intro xy hxy
    rw [Finset.mem_filter] at hxy ⊢
    exact ⟨hxy.1, fun j hj => hxy.2 j (le_trans hj hkk')⟩
  exact_mod_cast Finset.card_le_card hsub

end
end Submission.Vinogradov
