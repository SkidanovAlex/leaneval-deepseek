import Mathlib.FieldTheory.IsSepClosed
import Mathlib.Data.SetLike.Fintype
import Submission.NK.LocalAnabelian.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical

namespace NK.LocalAnabelian

noncomputable section

/-! ## Unconditional properties of the tower rank predicate -/

/-- A finite group has bounded `ℓ`-tower rank: there are only finitely many subgroups.
In particular `HasUnboundedTowerRank ℓ G` forces `G` to be infinite. -/
theorem not_hasUnboundedTowerRank_of_finite {G : Type*} [Group G] [Finite G]
    (ℓ : ℕ) : ¬ HasUnboundedTowerRank ℓ G := by
  intro h
  obtain ⟨V, -, -, hV⟩ := h (Nat.card (Subgroup G))
  have hle : numIndexSubgroups ℓ V ≤ Nat.card (Subgroup G) := by
    unfold numIndexSubgroups
    exact Nat.card_le_card_of_injective
      (fun H : {H : Subgroup ↥V // H.index = ℓ} => Subgroup.map V.subtype H.1)
      (fun H1 H2 h => Subtype.ext (Subgroup.map_injective V.subtype_injective h))
  omega

/-! ## The local input: the residue characteristic -/

/-- **The local input of the residue-characteristic detection.**  For `κ` a `p`-adic
field, `p` is the unique prime `ℓ` for which the absolute Galois group `Gal(K'/κ)`
has unbounded `ℓ`-tower rank.  This is the group-theoretic form of Ivanov's Lemma
3.12 and is exactly the input needed to recover the residue characteristic. -/
structure ResidueCharInput (p : ℕ) (κ K' : Type*) [Field κ] [Field K'] [Algebra κ K']
    [IsSepClosure κ K'] : Prop where
  hp : p.Prime
  detects : ResidueCharDetectedBy p (Gal(K'/κ))

/-- **The residue characteristic is an invariant of the absolute Galois group.**
If `κ` and `λ` are `p`- (resp. `q`-)adic fields with the corresponding detection
inputs, then any isomorphism of their absolute Galois groups forces `p = q`.

Note that only a group isomorphism is needed, not a homeomorphism: the `ℓ`-tower
rank predicate is an invariant of the abstract group
(`hasUnboundedTowerRank_congr`). -/
theorem residueChar_eq_of_mulEquiv {κ κ' K' L' : Type*} [Field κ] [Field κ'] [Field K']
    [Field L'] [Algebra κ K'] [Algebra κ' L'] [IsSepClosure κ K'] [IsSepClosure κ' L']
    {p q : ℕ} (h : ResidueCharInput p κ K') (h' : ResidueCharInput q κ' L')
    (ϕ : Gal(K'/κ) ≃* Gal(L'/κ')) : p = q :=
  residueCharDetectedBy_unique ϕ h.hp h'.hp h.detects h'.detects

/-- The same statement in the form in which it is consumed: the pair
`(residue characteristic, absolute degree)` of a `p`-adic field is an invariant of
its absolute Galois group.  See `NK.LocalAnabelian.PadicGaloisInputs` for the
degree part. -/
theorem residueCharDetectedBy_iff_of_mulEquiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) {p : ℕ} (h : ResidueCharDetectedBy p G) :
    ResidueCharDetectedBy p H := by
  intro ℓ hℓ
  rw [← hasUnboundedTowerRank_congr_iff e ℓ, h ℓ hℓ]

end

end NK.LocalAnabelian
