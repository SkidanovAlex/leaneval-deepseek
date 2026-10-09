import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.CycLevel

/-- **The `q`-part of the order of a non-`q`-th power in a finite cyclic group.**

Let `G` be a finite cyclic group, `q` a prime and `x ∈ G` an element which is *not* a `q`-th power
of an element of `G` (i.e. `x ∉ G^q = range (powMonoidHom q)`).  Then the `q`-part of `orderOf x`
is the *full* `q`-part of the group order: for every `j`, `q ^ j ∣ Nat.card G` implies
`q ^ j ∣ orderOf x`.

Proof sketch: write `G = ⟨g⟩` with `Nat.card G = m` and `x = g ^ k`.  Then `x ∈ G ^ q ↔ q ∣ k`
(here one uses `q ∣ m`, which follows from the hypothesis: if `q ∤ m` then the `q`-th power map is
surjective, so every element is a `q`-th power), while `orderOf x = m / Nat.gcd k m`; since
`q ∣ m`, `q ∣ Nat.gcd k m ↔ q ∣ k`, so the hypothesis says `¬ q ∣ Nat.gcd k m` and hence
`q ^ j ∣ m` implies `q ^ j ∣ m / Nat.gcd k m` for every `j`.
Useful API: `IsCyclic.exists_generator`, `Subgroup.mem_zpowers_iff`, `IsCyclic.iff_exists_zpowers_eq_top`,
`MonoidHom.mem_range`, `Nat.Prime.dvd_of_dvd_pow`, `Nat.factorization`,
`Nat.Prime.pow_dvd_iff_le_factorization`.  Note also `IsCyclic.index_powMonoidHom_range`
(`(Subgroup.range (powMonoidHom k)).index = Nat.gcd k (Nat.card G)`), which is exactly the
computation `q ∣ Nat.gcd k m ↔ q ∣ k` used above and may shorten the proof. -/
theorem cyclic_qpart_orderOf {G : Type*} [CommGroup G] [Finite G] [IsCyclic G]
    (q : ℕ) (hq : q.Prime) (x : G) (hx : x ∉ (powMonoidHom q).range) :
    ∀ j : ℕ, q ^ j ∣ Nat.card G → q ^ j ∣ orderOf x := by
  -- Write `G = ⟨g⟩` with `x = g ^ k`.
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := G)
  have hgpow : ∀ y : G, y ∈ Subgroup.zpowers g := fun y => mem_powers_iff_mem_zpowers.mp (hg y)
  have hgord : orderOf g = Nat.card G := orderOf_eq_card_of_forall_mem_zpowers hgpow
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff x g).mp (hg x)
  -- `q ∣ k` would make `x = (g ^ (k / q)) ^ q` a `q`-th power, contradiction.
  have hqk : ¬ q ∣ k := by
    rintro ⟨a, rfl⟩
    apply hx
    rw [MonoidHom.mem_range]
    exact ⟨g ^ a, by rw [powMonoidHom_apply, ← hk, ← pow_mul, mul_comm]⟩
  intro j hj
  -- `orderOf x = Nat.card G / Nat.gcd (Nat.card G) k`.
  rw [← hk, orderOf_pow, hgord]
  -- `q ∤ Nat.gcd (Nat.card G) k` since the gcd divides `k`.
  have hqgcd : ¬ q ∣ (Nat.card G).gcd k :=
    fun h => hqk (Nat.dvd_trans h (Nat.gcd_dvd_right _ _))
  have hcop : Nat.Coprime (q ^ j) ((Nat.card G).gcd k) :=
    (hq.coprime_iff_not_dvd.mpr hqgcd).pow_left j
  -- `q ^ j ∣ m` and `m = (m / d) * d` with `d = Nat.gcd m k` coprime to `q ^ j`.
  have hdecomp : Nat.card G / (Nat.card G).gcd k * (Nat.card G).gcd k = Nat.card G :=
    Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
  rw [← hdecomp] at hj
  exact hcop.dvd_of_dvd_mul_right hj

end Work.SSGRoute.CycLevel
