import Submission.NK.LocalReciprocity.All

/-!
# Local class field theory for `p`-adic fields: the corrected Artin reciprocity datum

This is the entry file of the `NK.LocalCFT` chapter.  It isolates the *canonical local Artin
reciprocity datum* for a field `F` with a Galois extension `F'` (in the application `F = κ` a
`p`-adic field and `F' = κ̄` a separable closure), in the form in which the rest of this chapter
and the downstream developments (`NK.LocalReciprocity.Invariants`, `NK.LocalInputs`) consume
it.

## What the datum says

Local class field theory says that for `F` a local field there is a canonical homomorphism
(the *local Artin map*)

`artin : Fˣ →* Gal(F^{ab}/F)`,    `F^{ab} = NK.LocalReciprocity.maxAbelianSubext F F'`,

whose composite with the restriction `Gal(F^{ab}/F) →* Gal(L/F)` to a finite abelian Galois
subextension `L ≤ F^{ab}` is surjective with kernel `N_{L/F} Lˣ` — the reciprocity isomorphism
`Fˣ ⧸ N_{L/F} Lˣ ≃* Gal(L/F)` — and whose norm groups are *cofinal* among the finite-index
subgroups of `Fˣ` (the existence theorem: every finite abelian extension of `F` is a subextension
of `F^{ab}` and every finite quotient of `Fˣ` occurs).

`ArtinReciprocity F F'` packages exactly this.

## Why the target is `Gal(F^{ab}/F)` and not `Gal(F'/F)`

The sibling area `Submission/Work/LocalReciprocity/` states the same datum with `artin` landing in
the *absolute* Galois group `Gal(F'/F)`
(`NK.LocalReciprocity.LocalReciprocityDatum.artin : Fˣ →* Gal(F'/F)`, and hence
`NK.LocalReciprocity.LubinTateInput F F'`).  That formulation is **empty** as soon as `F` has a
nonabelian nilpotent Galois quotient — in particular for every `p`-adic field `κ`:

* the image `A = artin(Fˣ)` is a *commutative* subgroup of `G_F = Gal(F'/F)` (it is the image of
  the abelian group `Fˣ`);
* let `M ≤ F'` be a finite Galois subextension whose Galois group `Q := Gal(M/F)` is nilpotent and
  nonabelian, and let `L := M^{[Q,Q]}` be the fixed field of the commutator subgroup.  Then `L/F` is
  a finite *abelian* Galois extension, so the level condition applied at `L` says that the image of
  `A` in `Gal(L/F) = Q^{ab} = Q/⁅Q,Q⁆` is everything; denoting by `ρ : Gal(F'/F) →* Q` the
  restriction (surjective because `F'/F` is Galois and `M/F` is normal), the image
  `B := ρ(A) ≤ Q` is a commutative subgroup with `B ⊔ ⁅Q,Q⁆ = ⊤`;
* `Q = B · ⁅Q,Q⁆` with `B` commutative forces `⁅Q,Q⁆ = ⁅⁅Q,Q⁆,Q⁆`
  (`NK.LocalCFT.NilpotentObstruction.commutator_eq_commutator_commutator`), and for a *nilpotent*
  `Q` the lower central series terminates, so `⁅Q,Q⁆ = ⊥` and `Q` is commutative
  (`NK.LocalCFT.NilpotentObstruction.isMulCommutative_of_abelian_sup_commutator_eq_top`) —
  contradiction;

* `G_κ` for a `p`-adic field `κ` has nonabelian finite `p`-quotients (the maximal pro-`p` quotient
  of `G_κ` is a Demushkin group of rank `≥ 2`, Neukirch–Schmidt–Wingberg (7.5.11)), so no such `A`
  exists and `LocalReciprocityDatum κ κ̄` is unsatisfiable.  This is
  `NK.LocalCFT.NilpotentObstruction.not_nonempty_localReciprocityDatum_of_galoisQuotient`, with
  the existence of the nonabelian nilpotent quotient as an explicit hypothesis (it is not
  formalised: for `κ = ℚ_2` the splitting field of `X⁴ - 2` has Galois group `D₄`, nilpotent and
  nonabelian, which is the standard example).

Here is a concrete discussion of the two points in the sibling formulation that made this
invisible: `isLevelIso` only constrains the *kernel* of the level maps, which really pins down only
the abelianised Artin map `Fˣ →* G_F^{ab}`; the field `artin` of the structure then asks for an
arbitrary lift of that map to `G_F`, and such a lift is *extra structure that does not exist*.  The
corrected datum below asks for the map into `G_F^{ab}`, which is the actual content of local
reciprocity and *is* satisfiable.  See `README.md` for the full discussion and for the conditional
formal refutation
(`NK.LocalCFT.NilpotentObstruction.not_nonempty_localReciprocityDatum_of_galoisQuotient`).

## Main definitions

* `NK.LocalCFT.AbsGal F F' = Gal(F'/F)` (notation only);
* `NK.LocalCFT.AbGal F F' = Gal(F^{ab}/F) = Gal(maxAbelianSubext F F'/F)`;
* `NK.LocalCFT.levelRestrict L : Gal(F^{ab}/F) →* Gal(L/F)` for a finite normal level;
* `NK.LocalCFT.ArtinReciprocity F F'` — the canonical reciprocity datum;
* `NK.LocalCFT.ArtinReciprocity.artinLevelHom`,
  `NK.LocalCFT.ArtinReciprocity.artinLevelMulEquiv` — the reciprocity isomorphism
  `Fˣ ⧸ N_{L/F} Lˣ ≃* Gal(L/F)` at a finite abelian level.
-/

open scoped Classical

namespace NK.LocalCFT

universe u v

variable {F : Type u} {F' : Type v} [Field F] [Field F'] [Algebra F F']

/-- The absolute Galois group `G_F = Gal(F'/F)`. -/
abbrev AbsGal (F : Type u) (F' : Type v) [Field F] [Field F'] [Algebra F F'] :=
  F' ≃ₐ[F] F'

/-- The abelianised absolute Galois group `G_F^{ab} = Gal(F^{ab}/F)`, realised as the Galois group
of the maximal abelian subextension `F^{ab}` of `F'/F`
(`NK.LocalReciprocity.maxAbelianSubext`, the fixed field of the commutator subgroup). -/
abbrev AbGal (F : Type u) (F' : Type v) [Field F] [Field F'] [Algebra F F'] [IsGalois F F'] :=
  (NK.LocalReciprocity.maxAbelianSubext F F' ≃ₐ[F] NK.LocalReciprocity.maxAbelianSubext F F')

section Levels

variable [IsGalois F F']

/-- **Restriction of an element of `Gal(F^{ab}/F)` to a normal level.**  For
`L : IntermediateField F F^{ab}` with `L/F` normal this is the canonical group homomorphism
`Gal(F^{ab}/F) →* Gal(L/F)`. -/
noncomputable def levelRestrict (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [Normal F L] : AbGal F F' →* (↥L ≃ₐ[F] ↥L) :=
  AlgEquiv.restrictNormalHom (F := F) (K₁ := NK.LocalReciprocity.maxAbelianSubext F F') ↥L

/-- The value of the restricted element at a point of the level. -/
theorem levelRestrict_apply (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [Normal F L] (σ : AbGal F F') (x : ↥L) :
    ((levelRestrict L σ) x : NK.LocalReciprocity.maxAbelianSubext F F') = σ x := by
  rw [levelRestrict, AlgEquiv.restrictNormalHom, MonoidHom.mk'_apply]
  exact AlgEquiv.restrictNormal_commutes σ ↥L x

/-- **Restriction between two levels of `F^{ab}`.**  For `L₂ ≤ L₁` normal levels of `F^{ab}`, this
is the canonical group homomorphism `Gal(L₁/F) →* Gal(L₂/F)`. -/
noncomputable def levelRestrictLe {L₁ L₂ : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F')}
    (h : L₂ ≤ L₁) [Normal F L₁] [Normal F L₂] :
    (↥L₁ ≃ₐ[F] ↥L₁) →* (↥L₂ ≃ₐ[F] ↥L₂) := by
  letI : Algebra ↥L₂ ↥L₁ := RingHom.toAlgebra (Subsemiring.inclusion h)
  haveI : IsScalarTower F ↥L₂ ↥L₁ := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  exact AlgEquiv.restrictNormalHom (F := F) (K₁ := ↥L₁) ↥L₂

end Levels

/-- **The canonical Artin reciprocity datum of local class field theory** for a field `F` with a
Galois extension `F'` (in applications `F'` is a separable closure of `F`).

* `artin` is the canonical Artin map `Fˣ →* Gal(F^{ab}/F)`;
* `isLevelIso` says that at every finite abelian Galois level `L ≤ F^{ab}` (i.e. every finite
  extension `L/F` inside `F^{ab}` which is normal, finite and abelian over `F`) the composite
  `Fˣ →* Gal(L/F)` is surjective with kernel the norm group `N_{L/F} Lˣ`;
* `cofinal` is the *existence theorem*: the norm groups of the finite abelian levels are cofinal
  among the finite-index subgroups of `Fˣ`.

This is the satisfiable form of the reciprocity datum; see the module docstring for why the
sibling formulation with `Gal(F'/F)` in place of `Gal(F^{ab}/F)` is empty for `p`-adic fields. -/
structure ArtinReciprocity (F : Type u) (F' : Type v) [Field F] [Field F'] [Algebra F F']
    [IsGalois F F'] where
  /-- the Artin map `Fˣ →* Gal(F^{ab}/F)`. -/
  artin : Fˣ →* AbGal F F'
  /-- at every finite abelian level the Artin map induces the reciprocity isomorphism. -/
  isLevelIso : ∀ (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
      [FiniteDimensional F L] [Normal F L] (_ : ∀ σ τ : L ≃ₐ[F] L, σ * τ = τ * σ),
      Function.Surjective ((levelRestrict L).comp artin) ∧
        MonoidHom.ker ((levelRestrict L).comp artin) = NK.LocalReciprocity.normGroup F ↥L
  /-- the existence theorem: the norm groups of the finite abelian levels are cofinal among the
  finite-index subgroups of `Fˣ`. -/
  cofinal : ∀ M : Subgroup Fˣ, M.FiniteIndex →
      ∃ (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
        (_ : FiniteDimensional F L) (_ : Normal F L)
        (_ : ∀ σ τ : L ≃ₐ[F] L, σ * τ = τ * σ),
        NK.LocalReciprocity.normGroup F ↥L ≤ M

/-- **The Lubin–Tate / existence input, in its corrected (satisfiable) form**: the existence of the
canonical local Artin reciprocity datum for `F` with `F'`.

This is the replacement for the sibling area's `NK.LocalReciprocity.LubinTateInput F F'`, which is
a statement about a map `Fˣ →* Gal(F'/F)` landing in the *absolute* Galois group and is
*unsatisfiable* as soon as `G_F` has a nonabelian nilpotent quotient — in particular for every
`p`-adic field; see `NK.LocalCFT.NilpotentObstruction.not_nonempty_localReciprocityDatum_of_galoisQuotient`
and `README.md`. -/
def LubinTateInput (F : Type u) (F' : Type v) [Field F] [Field F'] [Algebra F F']
    [IsGalois F F'] : Prop :=
  Nonempty (ArtinReciprocity F F')

/-- The corrected Lubin–Tate input provides the canonical reciprocity datum. -/
theorem nonempty_artinReciprocity_of_lubinTateInput {F : Type u} {F' : Type v} [Field F]
    [Field F'] [Algebra F F'] [IsGalois F F'] (h : LubinTateInput F F') :
    Nonempty (ArtinReciprocity F F') := h

namespace ArtinReciprocity

variable [IsGalois F F'] (D : ArtinReciprocity F F')

section LevelIso

variable (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
  [FiniteDimensional F L] [Normal F L]
  (hcomm : ∀ σ τ : L ≃ₐ[F] L, σ * τ = τ * σ)

/-- **The Artin map at a finite abelian level**, `Fˣ ⧸ N_{L/F} Lˣ →* Gal(L/F)`: the map induced by
`artin` on the quotient by the norm group. -/
noncomputable def artinLevelHom : (Fˣ ⧸ NK.LocalReciprocity.normGroup F ↥L) →* (↥L ≃ₐ[F] ↥L) :=
  QuotientGroup.lift (NK.LocalReciprocity.normGroup F ↥L) ((levelRestrict L).comp D.artin)
    (by rw [(D.isLevelIso L hcomm).2])

/-- The Artin map at a level is induced by `artin` on representatives. -/
theorem artinLevelHom_mk (x : Fˣ) :
    D.artinLevelHom L hcomm (QuotientGroup.mk x) = (levelRestrict L) (D.artin x) :=
  QuotientGroup.lift_mk' _ _ x

theorem artinLevelHom_surjective : Function.Surjective (D.artinLevelHom L hcomm) := by
  intro g
  obtain ⟨x, hx⟩ := (D.isLevelIso L hcomm).1 g
  exact ⟨QuotientGroup.mk x, by rw [artinLevelHom_mk]; exact hx⟩

theorem artinLevelHom_injective : Function.Injective (D.artinLevelHom L hcomm) := by
  intro a b hab
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective (s := NK.LocalReciprocity.normGroup F ↥L) a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective (s := NK.LocalReciprocity.normGroup F ↥L) b
  rw [artinLevelHom_mk, artinLevelHom_mk] at hab
  have hmem : x * y⁻¹ ∈ MonoidHom.ker ((levelRestrict L).comp D.artin) := by
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, map_mul, map_inv, hab, mul_inv_cancel]
  rw [(D.isLevelIso L hcomm).2] at hmem
  exact (QuotientGroup.eq).mpr (by simpa [mul_comm] using inv_mem hmem)

/-- **The reciprocity isomorphism at a finite abelian level**: `Fˣ ⧸ N_{L/F} Lˣ ≃* Gal(L/F)`. -/
noncomputable def artinLevelMulEquiv :
    (Fˣ ⧸ NK.LocalReciprocity.normGroup F ↥L) ≃* (↥L ≃ₐ[F] ↥L) :=
  MulEquiv.ofBijective (D.artinLevelHom L hcomm)
    ⟨D.artinLevelHom_injective L hcomm, D.artinLevelHom_surjective L hcomm⟩

/-- The reciprocity isomorphism at a level is the map induced by the Artin map. -/
theorem artinLevelMulEquiv_mk (x : Fˣ) :
    ((D.artinLevelMulEquiv L hcomm) (QuotientGroup.mk x) : ↥L ≃ₐ[F] ↥L) =
      (levelRestrict L) (D.artin x) :=
  D.artinLevelHom_mk L hcomm x

include D hcomm in
/-- The norm group of a finite abelian level is the kernel of the Artin map, and in particular
finite index in `Fˣ`. -/
theorem finiteIndex_normGroup :
    (NK.LocalReciprocity.normGroup F ↥L).FiniteIndex := by
  have h := (D.isLevelIso L hcomm).2
  rw [← h]
  exact Subgroup.finiteIndex_ker _

end LevelIso

end ArtinReciprocity

end NK.LocalCFT
