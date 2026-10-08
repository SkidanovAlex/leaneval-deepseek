import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV12

/-- If `σ` has order `p ^ k` for a prime `p` and moves a point `χ`, then the orbit of `χ`
under the cyclic subgroup `⟨σ⟩` has at least `p` elements. -/
theorem card_orbit_ge_of_orderOf_prime_pow
    {G X : Type*} [Group G] [MulAction G X] {σ : G} {p k : ℕ}
    (hp : Nat.Prime p) (hσ : orderOf σ = p ^ k)
    (χ : X) (hmoved : σ • χ ≠ χ) :
    p ≤ Nat.card (MulAction.orbit (Subgroup.zpowers σ) χ) := by
  set H : Subgroup G := Subgroup.zpowers σ with hHdef
  set S : Subgroup H := MulAction.stabilizer H χ
  -- `H` is cyclic of order `p ^ k`
  have hHcard : Nat.card H = p ^ k := by
    rw [hHdef, Nat.card_zpowers, hσ]
  -- orbit–stabilizer, in the form of an index
  have hm : Nat.card (MulAction.orbit H χ) = S.index := by
    rw [Subgroup.index_eq_card S]
    exact Nat.card_congr (MulAction.orbitEquivQuotientStabilizer H χ)
  have hprod : Nat.card (MulAction.orbit H χ) * Nat.card S = p ^ k := by
    have := Subgroup.index_mul_card S
    rw [← hm, hHcard] at this
    exact this
  -- the orbit is not a single point, since `σ` moves `χ`
  have hm1 : Nat.card (MulAction.orbit H χ) ≠ 1 := by
    intro h1
    have hsub : Subsingleton (MulAction.orbit H χ) := (Nat.card_eq_one_iff_unique.mp h1).1
    have hmem : (⟨χ, MulAction.mem_orbit_self χ⟩ : MulAction.orbit H χ)
        = ⟨σ • χ, MulAction.mem_orbit χ (⟨σ, Subgroup.mem_zpowers σ⟩ : H)⟩ :=
      @Subsingleton.elim _ hsub _ _
    exact hmoved (Subtype.ext_iff.mp hmem).symm
  -- the orbit size divides `p ^ k`
  have hmdvd : Nat.card (MulAction.orbit H χ) ∣ p ^ k := ⟨Nat.card S, hprod.symm⟩
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp hmdvd
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · exact absurd (by rw [hj, h0, pow_zero]) hm1
    · exact hpos
  calc p = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ j := Nat.pow_le_pow_right hp.pos hj1
    _ = Nat.card (MulAction.orbit H χ) := hj.symm

end Work.ThmF.ChV12
