import Mathlib
import Submission.Work.PGroup.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The rank of a finite `p`-group equals the rank of its Frattini quotient

For a finite group `H` the Frattini subgroup `Φ(H)` is exactly the set of "non-generating"
elements: a subset of `H` generates `H` if and only if its image generates `H ⧸ Φ(H)`
(`frattini_nongenerating`, valid because a finite group has a coatomic subgroup lattice).
Consequently the minimal number of generators is unchanged by passing to the Frattini quotient:

`Group.rank H = Group.rank (H ⧸ frattini H)`.

This is the general form of the classical Burnside basis theorem statement
`d(P) = dim_{𝔽_p}(P / Φ(P))` for a finite `p`-group `P`, and it is the lemma requested here.

The `p`-group hypothesis in the requested statement is not needed: only finiteness is.
-/

set_option linter.unusedVariables false

noncomputable section

namespace Work.PGroup

/-- **Burnside's basis theorem (rank form), general finite group version.**
For a finite group `H`, the minimal number of generators of `H` and of its Frattini quotient
`H ⧸ Φ(H)` coincide.

Proof: `Φ(H)` consists of non-generators, so `K ⊔ Φ(H) = ⊤` forces `K = ⊤`
(`frattini_nongenerating`, using that `Subgroup H` is coatomic for finite `H`).  Hence a finite
subset generates `H` iff its image generates `H ⧸ Φ(H)`, and the two ranks agree. -/
theorem rank_eq_rank_quotient_frattini {H : Type*} [Group H] [Finite H] :
    Group.rank H = Group.rank (H ⧸ frattini H) := by
  classical
  refine le_antisymm ?_ ?_
  · -- `rank H ≤ rank (H ⧸ Φ(H))`: lift a generating finset of the quotient.
    obtain ⟨S, hScard, hSgen⟩ := Group.rank_spec (H ⧸ frattini H)
    choose g hg using fun x : H ⧸ frattini H => QuotientGroup.mk'_surjective (frattini H) x
    have hTS : (S : Set (H ⧸ frattini H)) =
        (QuotientGroup.mk' (frattini H)) '' ((S.image g : Finset H) : Set H) := by
      ext x
      constructor
      · intro hx
        exact ⟨g x, Finset.mem_image.mpr ⟨x, hx, rfl⟩, hg x⟩
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
        rw [hg z]
        exact hz
    have hmap : Subgroup.map (QuotientGroup.mk' (frattini H))
        (Subgroup.closure ((S.image g : Finset H) : Set H)) = ⊤ := by
      rw [MonoidHom.map_closure, ← hTS]
      exact hSgen
    have hsup : Subgroup.closure ((S.image g : Finset H) : Set H) ⊔ frattini H = ⊤ := by
      have h := QuotientGroup.comap_map_mk' (frattini H)
        (Subgroup.closure ((S.image g : Finset H) : Set H))
      rw [hmap, Subgroup.comap_top] at h
      exact (sup_comm _ _).trans h.symm
    have hTgen : Subgroup.closure ((S.image g : Finset H) : Set H) = ⊤ :=
      frattini_nongenerating hsup
    calc Group.rank H ≤ (S.image g).card := Group.rank_le hTgen
      _ ≤ S.card := Finset.card_image_le
      _ = Group.rank (H ⧸ frattini H) := hScard
  · -- `rank (H ⧸ Φ(H)) ≤ rank H`: the quotient map is surjective.
    exact Group.rank_le_of_surjective (QuotientGroup.mk' (frattini H))
      (QuotientGroup.mk'_surjective (frattini H))

/-- For a finite `p`-group `P ≤ G`, the minimal number of generators of `P` equals the minimal
number of generators of `P ⧸ Φ(P)`.  (Burnside's basis theorem.) -/
theorem rank_eq_rank_frattini {G : Type*} [Group G] {p : ℕ} (P : Subgroup G) [Finite P]
    (hP : IsPGroup p P) : Group.rank P = Group.rank (P ⧸ frattini P) :=
  rank_eq_rank_quotient_frattini (H := ↥P)

end Work.PGroup
