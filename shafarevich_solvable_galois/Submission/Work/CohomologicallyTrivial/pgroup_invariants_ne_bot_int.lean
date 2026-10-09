import Mathlib
import Submission.Work.CohomologicallyTrivial.pgroup_invariants_ne_bot
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Invariants of a `p`-group representation over `ℤ` killed by `p`

This is the `ℤ`-coefficient form of `pgroup_invariants_ne_bot`: a nonzero `ℤ`-representation `V` of a
finite `p`-group `G` all of whose elements satisfy `p • v = 0` has a nonzero fixed vector.

The point is that such a `V` is *the same thing as* a `ZMod p`-representation: `p • v = 0` for all
`v` exhibits the underlying additive group of `V` as a module over `ZMod p`
(`AddCommGroup.zmodModule`), and because every `V.ρ g` is `ℤ`-linear — hence in particular additive
— it is automatically `ZMod p`-linear (`ZMod.map_smul`).  So `V.V` carries a `ZMod p`-representation
of `G` (`Rep.ofDistribMulAction`), to which `pgroup_invariants_ne_bot` applies verbatim.

## Implementation notes

The `ZMod p`-module structure and the compatible `G`-action are installed as local instances; the
commutation `g • (c • v) = c • (g • v)` of the two scalar actions is exactly `ZMod.map_smul`, the
additivity of `V.ρ g` re-read as `ZMod p`-linearity.
-/

namespace Work.CohomologicallyTrivial

set_option linter.style.haveILetI false

/-- A nonzero `ℤ`-representation of a finite `p`-group on which `p` acts as `0` has a nonzero fixed
vector. -/
theorem pgroup_invariants_ne_bot_int {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Fintype G]
    (hpG : IsPGroup p G) (V : Rep.{0, 0, 0} ℤ G) (hV : ∀ v : V.V, p • v = 0) [Nontrivial V.V] :
    ∃ v : V.V, v ≠ 0 ∧ ∀ g : G, V.ρ g v = v := by
  classical
  -- `V.V` is a module over `ZMod p` because `p • v = 0` for every `v`.
  letI : Module (ZMod p) V.V := AddCommGroup.zmodModule hV
  -- The `G`-action underlying the `ℤ`-representation is a compatible `DistribMulAction`.
  letI : DistribMulAction G V.V :=
    { smul := fun g v => V.ρ g v
      one_smul := fun v => by show V.ρ 1 v = v; rw [map_one]; rfl
      mul_smul := fun g h v => by show V.ρ (g * h) v = V.ρ g (V.ρ h v); rw [map_mul]; rfl
      smul_zero := fun g => by show V.ρ g 0 = 0; exact map_zero _
      smul_add := fun g x y => by
        show V.ρ g (x + y) = V.ρ g x + V.ρ g y
        exact map_add _ x y }
  -- The two scalar actions commute, i.e. every `V.ρ g` is `ZMod p`-linear.
  letI : SMulCommClass G (ZMod p) V.V :=
    ⟨fun g c v => by
      show V.ρ g (c • v) = c • V.ρ g v
      exact ZMod.map_smul (V.ρ g) c v⟩
  -- Apply the `ZMod p` statement to this representation.
  obtain ⟨v, hv, hfix⟩ :=
    pgroup_invariants_ne_bot hpG (Rep.ofDistribMulAction (ZMod p) G V.V) ‹Nontrivial V.V›
  refine ⟨v, hv, ?_⟩
  intro g
  show V.ρ g v = v
  exact hfix g

end Work.CohomologicallyTrivial
