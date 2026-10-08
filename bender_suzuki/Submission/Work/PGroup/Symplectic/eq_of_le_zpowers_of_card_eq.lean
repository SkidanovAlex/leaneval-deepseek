import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PGroup.Symplectic

/-- Two subgroups of a common cyclic subgroup `Subgroup.zpowers a` which have the same
(prime) cardinality `p` are equal. -/
theorem eq_of_le_zpowers_of_card_eq {X : Type*} [Group X] [Finite X] {a : X} {p : ℕ}
    (hp : p.Prime) {H K : Subgroup X} (hH : H ≤ Subgroup.zpowers a) (hK : K ≤ Subgroup.zpowers a)
    (hHc : Nat.card ↥H = p) (hKc : Nat.card ↥K = p) : H = K := by
  obtain ⟨n, rfl⟩ := (Subgroup.le_zpowers_iff a H).mp hH
  obtain ⟨m, rfl⟩ := (Subgroup.le_zpowers_iff a K).mp hK
  have h1 : orderOf (a ^ n) = p := by rw [← Nat.card_zpowers]; exact hHc
  have h2 : orderOf (a ^ m) = p := by rw [← Nat.card_zpowers]; exact hKc
  rw [orderOf_pow] at h1 h2
  have e1 : orderOf a = p * Nat.gcd n (orderOf a) := by
    have h := Nat.div_mul_cancel (Nat.gcd_dvd_left (orderOf a) n)
    rw [h1, Nat.gcd_comm] at h
    exact h.symm
  have e2 : orderOf a = p * Nat.gcd m (orderOf a) := by
    have h := Nat.div_mul_cancel (Nat.gcd_dvd_left (orderOf a) m)
    rw [h2, Nat.gcd_comm] at h
    exact h.symm
  have hg : Nat.gcd n (orderOf a) = Nat.gcd m (orderOf a) :=
    Nat.mul_left_cancel hp.pos (by rw [← e1, ← e2])
  rw [← zpow_natCast a n, ← zpow_natCast a m, Subgroup.zpowers_eq_zpowers_iff',
    Int.gcd_natCast_natCast, Int.gcd_natCast_natCast, hg]

end Work.PGroup.Symplectic
