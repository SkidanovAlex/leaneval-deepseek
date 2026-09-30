import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `m`-torsion of `(ZMod (p^e))ˣ` for an odd prime `p`

The number of `m`-th roots of unity modulo an odd prime power `p^e` is at most `m`.

The reason is that `(ZMod (p^e))ˣ` is cyclic for odd `p`
(`ZMod.isCyclic_units_of_prime_pow`), and in a finite cyclic group the number of
solutions of `x ^ m = 1` is `gcd(m, |G|) ≤ m`
(`IsCyclic.card_pow_eq_one_le`).

The hypothesis `p ≠ 2` is essential: for `p = 2` the units of `p^e` are not cyclic (for `e ≥ 3`)
and e.g. `x ^ 2 = 1` has four solutions in `ZMod 8`.
-/

namespace Work.BMF

theorem mtorsion_odd_prime_pow (p e m : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hm : 1 ≤ m) :
    Nat.card (rootsOfUnity m (ZMod (p ^ e))) ≤ m := by
  classical
  have hne : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  have hcyc : IsCyclic (ZMod (p ^ e))ˣ := ZMod.isCyclic_units_of_prime_pow p hp hp2 e
  have h := IsCyclic.card_pow_eq_one_le (α := (ZMod (p ^ e))ˣ) (n := m)
    (Nat.lt_of_lt_of_le Nat.zero_lt_one hm)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simpa only [mem_rootsOfUnity] using h

end Work.BMF
