import Mathlib.GroupTheory.Index
import Mathlib.Data.Nat.Prime.Basic
import Submission.NK.LocalTame.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.Ramification

/-- A finite group whose cardinality is a power of a prime `p` is a pro-`p` group in the
finite-quotient sense: every finite index subgroup has `p`-power index. -/
theorem isProP_of_natCard_eq_prime_pow {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (h : ∃ k : ℕ, Nat.card G = p ^ k) : NK.LocalTame.IsProP p G := by
  obtain ⟨k, hk⟩ := h
  intro N _ _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 (hk ▸ N.index_dvd_card)
  exact ⟨j, hj⟩

end NK.Ramification
