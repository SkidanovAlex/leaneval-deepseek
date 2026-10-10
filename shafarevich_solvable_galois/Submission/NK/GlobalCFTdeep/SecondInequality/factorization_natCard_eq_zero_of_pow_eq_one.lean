import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.GlobalCFTdeep.SecondInequality

/-- If every element of a finite nonempty group `Q` satisfies `q ^ n = 1` (i.e. `Q` has exponent
dividing `n`) and `p` is a prime with `p ∤ n`, then the `p`-part of `Nat.card Q` is trivial.  (By
Cauchy's theorem, otherwise `Q` would have an element of order `p`.) -/
theorem factorization_natCard_eq_zero_of_pow_eq_one {Q : Type*} [Group Q] {n : ℕ}
    (hQ : Nat.card Q ≠ 0) {p : ℕ} (hp : p.Prime) (hn : ¬ p ∣ n) (h : ∀ q : Q, q ^ n = 1) :
    (Nat.card Q).factorization p = 0 := by
  by_contra hne
  have hpFact : Fact p.Prime := ⟨hp⟩
  have hfin : Finite Q := Nat.finite_of_card_ne_zero hQ
  obtain ⟨x, hx⟩ :=
    @exists_prime_orderOf_dvd_card' Q _ hfin p hpFact (Nat.dvd_of_factorization_pos hne)
  exact hn (hx ▸ orderOf_dvd_iff_pow_eq_one.mpr (h x))

end NK.GlobalCFTdeep.SecondInequality
