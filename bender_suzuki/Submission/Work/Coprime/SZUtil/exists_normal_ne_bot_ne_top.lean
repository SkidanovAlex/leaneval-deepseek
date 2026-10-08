import Mathlib
import Submission.Work.Solvable.exists_normal_prime_quotient

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# A finite solvable group of non-prime order has a nontrivial proper normal subgroup

If `Q` is a finite solvable group with `Nat.card Q ≠ 1` and `Nat.card Q` not prime, then `Q` admits
a normal subgroup `A` with `A ≠ ⊥` and `A ≠ ⊤`.

The proof uses `Work.Solvable.exists_normal_prime_quotient`: a finite solvable nontrivial group `Q`
has a proper normal subgroup `M` with `Nat.card (Q ⧸ M) = q` for some prime `q`.  Lagrange's
theorem gives `Nat.card Q = Nat.card (Q ⧸ M) * Nat.card M = q * Nat.card M`; since `Nat.card Q` is
not prime we must have `Nat.card M ≠ 1`, i.e. `M ≠ ⊥`.  Finally `M < ⊤` gives `M ≠ ⊤`.
-/

namespace Work.Coprime.SZUtil

theorem exists_normal_ne_bot_ne_top {Q : Type*} [Group Q] [Finite Q]
    (hsol : Group.IsSolvable Q) (h1 : Nat.card Q ≠ 1) (hp : ¬ (Nat.card Q).Prime) :
    ∃ A : Subgroup Q, A.Normal ∧ A ≠ ⊥ ∧ A ≠ ⊤ := by
  have hnt : Nontrivial Q := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    exact h1 (Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩)
  obtain ⟨q, hq, M, hMn, hMlt, hcard⟩ := Work.Solvable.exists_normal_prime_quotient hsol hnt
  refine ⟨M, hMn, ?_, ?_⟩
  · -- `M` is nontrivial, otherwise `Q` would have prime order `q`
    intro hbot
    have hcardM : Nat.card M = 1 := by rw [hbot]; simp
    have hcardQ : Nat.card Q = q := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup M, hcard, hcardM, mul_one]
    rw [hcardQ] at hp
    exact hp hq
  · -- `M` is proper by construction
    exact ne_of_lt hMlt

end Work.Coprime.SZUtil
