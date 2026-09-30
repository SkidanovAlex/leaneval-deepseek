import Mathlib
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.HALG

/-- An abelian group of order 12 with `G/2G` of order 2 is cyclic.

Hints for the proof (elementary, no classification needed). `hcard` gives `Finite G` via
`Nat.card_ne_zero`/`Nat.card_pos_iff`. Let `H := (nsmulAddMonoidHom (α := G) 2).range = 2G`; then
`AddSubgroup.index_mul_card H : H.index * Nat.card H = Nat.card G` and
`AddSubgroup.index_eq_card : H.index = Nat.card (G ⧸ H)`, so `Nat.card H = 6`. Cauchy
(`exists_prime_addOrderOf_dvd_card`) gives `a` with `addOrderOf a = 3` and, since
`G ⧸ H ≅ ZMod 2`-ish has exponent 2 (every element of the quotient is killed by 2), `a ∈ H`; Cauchy
in `H` gives `b ∈ H` with `addOrderOf b = 2`; then `c := a + b` has `addOrderOf c = 6`, so
`H = zmultiples c` (its `6` multiples are distinct by the order computation) and `c = 2 • g` for
some `g : G` (definition of `H`); finally `addOrderOf (2 • g) = addOrderOf g / gcd (addOrderOf g) 2`
(equivalently `addOrderOf_smul`/`addOrderOf_nsmul` and `addOrderOf_dvd_iff_nsmul_eq_zero`), together
with `addOrderOf g ∣ 12`, forces `addOrderOf g = 12`, hence `IsAddCyclic G`. -/
theorem addCyclic_of_card_twelve (G : Type) [AddCommGroup G]
    (hcard : Nat.card G = 12)
    (hquot : Nat.card (G ⧸ (nsmulAddMonoidHom (α := G) 2).range) = 2) :
    IsAddCyclic G := by
  -- `G` is finite, because it has 12 elements.
  have hfin : Finite G := (Nat.card_pos_iff.mp (by rw [hcard]; norm_num)).2
  -- `H = 2G`, the range of multiplication by `2`.
  set H : AddSubgroup G := (nsmulAddMonoidHom (α := G) 2).range with hH
  have hidx : H.index = 2 := by
    rw [hH, AddSubgroup.index_eq_card]; exact hquot
  -- Lagrange: `H.index * Nat.card H = Nat.card G`, so `H` has 6 elements.
  have hcardH : Nat.card H = 6 := by
    have h := AddSubgroup.index_mul_card H
    rw [hidx, hcard] at h
    omega
  -- Cauchy in `H`: an element `a` of order 3 and an element `b` of order 2.
  obtain ⟨a, ha⟩ := exists_prime_addOrderOf_dvd_card' (G := H) 3 (by rw [hcardH]; norm_num)
  obtain ⟨b, hb⟩ := exists_prime_addOrderOf_dvd_card' (G := H) 2 (by rw [hcardH]; norm_num)
  -- Coprime orders add: `c = a + b` has order 6 in `H`.
  have hab : addOrderOf (a + b) = 6 := by
    rw [AddCommute.addOrderOf_add_eq_mul_addOrderOf_of_coprime (AddCommute.all a b)
      (by rw [ha, hb]; norm_num), ha, hb]
  -- `c ∈ H = 2G`, so `c = 2 • g` for some `g : G`.
  obtain ⟨g, hg⟩ :=
    AddMonoidHom.mem_range.mp
      (show ((a + b : H) : G) ∈ (nsmulAddMonoidHom (α := G) 2).range from (a + b : H).2)
  simp only [nsmulAddMonoidHom_apply] at hg
  -- Hence `2 • g` has additive order 6.
  have h2g : addOrderOf (2 • g) = 6 := by
    rw [hg, AddSubgroup.addOrderOf_coe]
    exact hab
  -- Arithmetic of orders: `addOrderOf g ∣ 12`, `6 ∣ addOrderOf g`, and `addOrderOf g ≠ 6`.
  have hndvd : addOrderOf g ∣ 12 := by rw [← hcard]; exact addOrderOf_dvd_natCard g
  have h6dvd : 6 ∣ addOrderOf g := by
    have h := addOrderOf_smul_dvd (x := g) 2
    rwa [h2g] at h
  have hne6 : addOrderOf g ≠ 6 := by
    intro h6
    have h6g : 6 • g = 0 := addOrderOf_dvd_iff_nsmul_eq_zero.mp (by rw [h6])
    have h3 : 3 • (2 • g) = 0 := by rw [← mul_nsmul g 2 3, h6g]
    have hdvd3 : addOrderOf (2 • g) ∣ 3 := addOrderOf_dvd_iff_nsmul_eq_zero.mpr h3
    rw [h2g] at hdvd3
    norm_num at hdvd3
  -- Therefore `g` has order 12 = `Nat.card G`, so `G` is cyclic.
  have h12 : addOrderOf g = 12 := by
    have hnle : addOrderOf g ≤ 12 := Nat.le_of_dvd (by norm_num) hndvd
    have hpos : 0 < addOrderOf g := addOrderOf_pos g
    interval_cases addOrderOf g <;> norm_num at *
  exact isAddCyclic_of_addOrderOf_eq_card g (by rw [hcard]; exact h12)

end Work.Pi6.HALG
