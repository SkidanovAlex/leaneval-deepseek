import Mathlib
import Submission.Work.A7REC.Defs

namespace Work.A7REC.Basic

/-- `U ⊓ S = ⊥`: the subgroup `U` of order `3` and the Sylow `2`-subgroup `S` meet trivially.

`U ⊓ S` is a subgroup of `U`, hence its cardinality divides `3`, and a subgroup of the
Sylow `2`-subgroup `S` of order `8`, hence its cardinality divides `8`.  As `3` and `8` are
coprime, `U ⊓ S` is trivial.  (The order `|S| = 8` comes from the dihedral model
`S ≃* DihedralGroup 4`, of order `2 * 4`.) -/
theorem U_inf_S (G : Type*) [Group G] [Finite G] (ctx : Work.A7REC.A7RecCtx G) :
    ctx.U ⊓ (ctx.S : Subgroup G) = ⊥ := by
  apply Subgroup.card_eq_one.mp
  -- |S| = 8, using the dihedral model `S ≃* DihedralGroup 4`.
  have hcardS : Nat.card (ctx.S : Subgroup G) = 8 := by
    obtain ⟨e⟩ := ctx.hSdih
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  -- |U ⊓ S| divides |U| = 3 and |S| = 8.
  have hU : Nat.card ↥(ctx.U ⊓ (ctx.S : Subgroup G)) ∣ Nat.card ↥ctx.U :=
    Subgroup.card_dvd_of_le (α := G) inf_le_left
  have hS : Nat.card ↥(ctx.U ⊓ (ctx.S : Subgroup G)) ∣ Nat.card ↥(ctx.S : Subgroup G) :=
    Subgroup.card_dvd_of_le (α := G) inf_le_right
  rw [ctx.hUcard] at hU
  rw [hcardS] at hS
  -- hence |U ⊓ S| divides gcd 3 8 = 1.
  have hgcd := Nat.dvd_gcd hU hS
  rw [show Nat.gcd 3 8 = 1 from by norm_num] at hgcd
  exact Nat.dvd_one.mp hgcd

end Work.A7REC.Basic
