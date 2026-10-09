import Mathlib.GroupTheory.SpecificGroups.Cyclic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.GroupTheory.SpecificGroups.Cyclic

/-- For a finite cyclic commutative group `G`, the quotient of `G` by the
image of the `n`-th-power endomorphism has cardinality `gcd n |G|`
(the cokernel of the power map is the gcd-sized group of `n`-th roots of
unity inside `G`). -/
theorem card_quotient_powMonoidHom {G : Type*} [CommGroup G] [Fintype G] [IsCyclic G]
    (n : ℕ) : Nat.card (G ⧸ (powMonoidHom n).range) = Nat.gcd n (Fintype.card G) := by
  let f : G →* G := powMonoidHom n
  change Nat.card (G ⧸ f.range) = Nat.gcd n (Fintype.card G)
  calc
    Nat.card (G ⧸ f.range) = f.range.index := (Subgroup.index_eq_card f.range).symm
    _ = (Nat.card G).gcd n := by
      simpa [f] using (IsCyclic.index_powMonoidHom_range (G := G) n)
    _ = Nat.gcd n (Fintype.card G) := by
      rw [Nat.gcd_comm, Nat.card_eq_fintype_card]

end Commons.GroupTheory.SpecificGroups.Cyclic