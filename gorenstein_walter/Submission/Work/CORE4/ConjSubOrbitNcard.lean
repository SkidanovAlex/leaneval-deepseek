import Mathlib
import Submission.Work.CORE4.Defs

/-!
# Orbit–stabiliser for the conjugation action of a subgroup

The target `Work.CORE4.ConjSubOrbitNcard` counts the distinct `H`-conjugates `h P h⁻¹`
(`h ∈ H`) of a subgroup `P`: their number is the index in `H` of the stabiliser `H ⊓ N_G(P)`.

The conjugation action of a subgroup `H ≤ G` on the subgroups of `G` is obtained by pulling the
pointwise action of the group `MulAut G` of automorphisms of `G` on `Subgroup G`
(`f • P = P.map f`) back along the conjugation homomorphism `MulAut.conj : G →* MulAut G`
restricted to `H`:

`MulAction.compHom (Subgroup G) (MulAut.conj.comp H.subtype)`.

With this action, `h • P` is *definitionally* `Work.GW2.conjSub h P` (`rfl`), which makes the two
identifications needed for orbit–stabiliser — the orbit is the set of conjugates, the stabiliser
is `H ⊓ N_G(P)` — `rfl`-level, leaving `MulAction.index_stabilizer` and the definition of
`Subgroup.relIndex` as the only content.

The action is registered **locally only** (`attribute [local instance]`): Mathlib does not provide
a global `MulAction ↥H (Subgroup G)`, and registering one globally could interfere with the
pointwise actions of subquotients that other files rely on.
-/

open scoped Pointwise

namespace Work.CORE4

/-- **The conjugation action of a subgroup `H ≤ G` on the subgroups of `G`**: `h • P = h P h⁻¹`.

This is the pointwise action of `MulAut G` on `Subgroup G` (`f • P = P.map f`) pulled back along
the conjugation homomorphism `MulAut.conj : G →* MulAut G` restricted to `H`; hence `h • P` is
definitionally `Work.GW2.conjSub h P`. -/
@[instance_reducible] def conjSubMulAction {G : Type} [Group G] (H : Subgroup G) :
    MulAction H (Subgroup G) :=
  MulAction.compHom (Subgroup G) ((MulAut.conj : G →* MulAut G).comp H.subtype)

attribute [local instance] conjSubMulAction

/-- Under the conjugation action `conjSubMulAction`, `h • P` is `Work.GW2.conjSub h P`. -/
theorem conjSubMulAction_smul {G : Type} [Group G] (H P : Subgroup G) (h : H) :
    h • P = Work.GW2.conjSub (h : G) P := rfl

/-- The `H`-orbit of `P` under the conjugation action is the set of its `H`-conjugates. -/
theorem orbit_conjSubMulAction {G : Type} [Group G] (H P : Subgroup G) :
    MulAction.orbit H P
      = {X : Subgroup G | ∃ h : G, h ∈ H ∧ X = Work.GW2.conjSub h P} := by
  ext X
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨(h : G), h.2, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨⟨h, hh⟩, rfl⟩

/-- The stabiliser of `P` under the conjugation action is `H ⊓ N_G(P)`, viewed inside `H`. -/
theorem stabilizer_conjSubMulAction {G : Type} [Group G] (H P : Subgroup G) :
    MulAction.stabilizer H P
      = (H ⊓ Subgroup.normalizer (P : Set G)).subgroupOf H := by
  ext x
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
    Subgroup.mem_normalizer_iff_map_conj_eq]
  constructor
  · intro h
    exact ⟨x.2, h⟩
  · rintro ⟨-, h⟩
    exact h

/-- Orbit–stabiliser for the conjugation action of a subgroup `H ≤ G` on the subgroups of `G`:
the number of distinct `H`-conjugates `h P h⁻¹` (`h ∈ H`) of a subgroup `P` equals the index in
`H` of the stabiliser `H ⊓ N_G(P)`.  Here `Work.GW2.conjSub g P` is `P.map (MulAut.conj g)`
(defined in `Submission/Work/CORE4/Defs.lean`) and `Subgroup.relIndex K H = (K.subgroupOf H).index`
is the index of `K` in `H`. -/
theorem ConjSubOrbitNcard {G : Type} [Group G] [Finite G] (H P : Subgroup G) :
    {X : Subgroup G | ∃ h : G, h ∈ H ∧ X = Work.GW2.conjSub h P}.ncard
      = (H ⊓ Subgroup.normalizer (P : Set G)).relIndex H := by
  rw [← orbit_conjSubMulAction H P, ← MulAction.index_stabilizer H P,
    stabilizer_conjSubMulAction H P]
  rfl

end Work.CORE4
