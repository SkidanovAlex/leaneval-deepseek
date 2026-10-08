import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.BSLit.BenderFacts2.MyAux

open MulAction

/-- If a subgroup `E` of order a prime `p` acts without fixed points on a finite
`G`-set `Ω`, then `p` divides `|Ω|`.

The proof is the standard orbit-counting argument: since `|E| = p` is prime, `E` is a
`p`-group, and hence `|Ω| ≡ |Ω^E| (mod p)`. As the action is fixed-point-free and `E` is
nontrivial, `Ω^E` is empty, so `p ∣ |Ω|`. -/
theorem prime_dvd_card_of_fixedPointFree {G : Type*} [Group G] [Fintype G]
    {Ω : Type*} [MulAction G Ω] [Fintype Ω] {p : ℕ} (hp : p.Prime) {E : Subgroup G}
    (hE : Nat.card ↥E = p) (hfree : ∀ (x : ↥E) (ω : Ω), x • ω = ω → x = 1) :
    p ∣ Nat.card Ω := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- `E` is a `p`-group (its order is the prime `p`).
  have hpg : IsPGroup p ↥E := IsPGroup.of_card (by rw [hE, pow_one])
  -- `E` is nontrivial, since `|E| = p > 1`.
  have hnt : Nontrivial ↥E := by
    rw [← Finite.one_lt_card_iff_nontrivial, hE]
    exact hp.one_lt
  -- Any point fixed by all of `E` would be fixed by a nontrivial element, contradicting
  -- fixed-point-freeness; hence there are no `E`-fixed points.
  haveI : IsEmpty (fixedPoints ↥E Ω) := ⟨fun ω => by
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥E)
    exact hx (hfree x ω.1 (mem_fixedPoints.mp ω.2 x))⟩
  have hzero : Nat.card (fixedPoints ↥E Ω) = 0 := Nat.card_of_isEmpty
  -- Congruence of the fixed-point count for a `p`-group action.
  have hmod := hpg.card_modEq_card_fixedPoints Ω
  rw [hzero] at hmod
  exact Nat.modEq_zero_iff_dvd.mp hmod

end Work.BSLit.BenderFacts2.MyAux
