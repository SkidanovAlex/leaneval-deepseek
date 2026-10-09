/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Exactness of the abelianization functor at the middle term

For a normal subgroup `N` of a group `G` the diagram of abelianizations

  `Ab(N) --→ Ab(G) --→ Ab(G/N)`

is exact at `Ab(G)`: the image of the map induced by the inclusion `N ↪ G` is precisely
the kernel of the map induced by the quotient `G ↠ G/N`.

Concretely, `Ab(G) ≅ G ⧸ [G,G]`, and the two subgroups of `Ab(G)` occurring here are the
images under the canonical projection `G ↠ G ⧸ [G,G]` of

* `N` (the range of the map induced by `N ↪ G`), and
* the preimage of `[G/N, G/N]` in `G` (the kernel of `Ab(G) → Ab(G/N)`),

and that preimage is `[G,G] ⊔ N` because `[G/N, G/N]` is the image of `[G,G]` under the
quotient map.  Since `[G,G]` is the kernel of `G ↠ Ab(G)`, the two images agree.

The two auxiliary lemmas `abelianization_range_lift` and `abelianization_ker_lift` are the
value-level description of the maps `Ab(G) →* A` (for `A` abelian) induced by a homomorphism
`G →* A`: on `Ab(G)` the range and kernel of `Abelianization.lift φ` are the image and the
image-of-the-kernel of `φ`.
-/
import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.Reconstruct

open Abelianization

/-- The range of `Abelianization.lift φ` is the range of `φ`.

This is the value-level form of the fact that `Abelianization.of : G →* Abelianization G` is
surjective: for an abelian target `A`, the map `Ab(G) →* A` induced by `φ : G →* A` has the
same range as `φ`. -/
theorem abelianization_range_lift {G : Type*} [Group G] {A : Type*} [CommGroup A]
    (φ : G →* A) : (Abelianization.lift φ).range = φ.range := by
  have h1 : φ = (Abelianization.lift φ).comp Abelianization.of := by
    ext g
    simp
  have h2 : (Abelianization.of : G →* Abelianization G).range = ⊤ :=
    MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective (commutator G))
  rw [show (Abelianization.lift φ).range = Subgroup.map (Abelianization.lift φ) ⊤ from
    MonoidHom.range_eq_map _]
  conv_rhs => rw [h1, MonoidHom.range_comp, h2]

/-- The kernel of `Abelianization.lift φ` is the image in `Ab(G)` of the kernel of `φ`.

This is `QuotientGroup.ker_lift` for the quotient `G ⧸ [G,G]` (which is `Ab(G)`) together with
the fact that any homomorphism to an abelian group kills `[G,G]`. -/
theorem abelianization_ker_lift {G : Type*} [Group G] {A : Type*} [CommGroup A]
    (φ : G →* A) : (Abelianization.lift φ).ker = Subgroup.map Abelianization.of φ.ker := by
  change (QuotientGroup.lift (commutator G) φ
    (fun _ h => MonoidHom.mem_ker.2 (Abelianization.commutator_subset_ker φ h))).ker = _
  rw [QuotientGroup.ker_lift]
  rfl

/-- The range of `Abelianization.map f` is the image in `Ab(G)` of the range of `f`. -/
theorem abelianization_range_map {G H : Type*} [Group G] [Group H] (f : G →* H) :
    (Abelianization.map f).range = Subgroup.map Abelianization.of f.range := by
  change (Abelianization.lift (Abelianization.of.comp f)).range = _
  rw [abelianization_range_lift, MonoidHom.range_comp]

/-- The kernel of `Abelianization.map f` is the image in `Ab(G)` of the preimage under `f` of
the commutator subgroup of `H`. -/
theorem abelianization_ker_map {G H : Type*} [Group G] [Group H] (f : G →* H) :
    (Abelianization.map f).ker =
      Subgroup.map Abelianization.of (Subgroup.comap f (commutator H)) := by
  change (Abelianization.lift (Abelianization.of.comp f)).ker = _
  rw [abelianization_ker_lift, ← MonoidHom.comap_ker, Abelianization.ker_of]

/-- **Exactness of abelianization at the middle term.**  For a normal subgroup `N` of a group
`G`, the image of `Ab(N) → Ab(G)` (induced by the inclusion `N ↪ G`) is the kernel of
`Ab(G) → Ab(G/N)` (induced by the quotient `G ↠ G/N`). -/
theorem abelianization_range_inclusion_eq_ker_quotient {G : Type*} [Group G] (N : Subgroup G)
    [N.Normal] :
    (Abelianization.map N.subtype).range = (Abelianization.map (QuotientGroup.mk' N)).ker := by
  rw [abelianization_range_map, abelianization_ker_map, Subgroup.range_subtype]
  -- `[G/N, G/N]` is the image of `[G,G]` under the quotient map.
  have hcomm : commutator (G ⧸ N) = (commutator G).map (QuotientGroup.mk' N) := by
    rw [commutator_def (G ⧸ N), commutator_def G, Subgroup.map_commutator,
      ← MonoidHom.range_eq_map, QuotientGroup.range_mk']
  -- The preimage of `[G/N, G/N]` is `[G,G] ⊔ N`.
  rw [hcomm, Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.map_sup]
  -- `[G,G]` dies in `Ab(G)`.
  have hbot : Subgroup.map Abelianization.of (commutator G) = ⊥ :=
    (Subgroup.map_eq_bot_iff (commutator G)).mpr (le_of_eq (Abelianization.ker_of G).symm)
  rw [hbot, bot_sup_eq]

end NK.Reconstruct
