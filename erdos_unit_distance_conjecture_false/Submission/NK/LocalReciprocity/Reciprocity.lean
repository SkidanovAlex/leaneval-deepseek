import Submission.NK.LocalReciprocity.Prelude
import Submission.NK.LocalReciprocity.NormGroup

/-!
# The reciprocity datum of local class field theory

The *finite* form of local class field theory available in the commons
(`Commons.NumberTheory.NumberField.Completion.exists_mulEquiv_artinMap_of_commute`) is the weak
statement "there exists a surjection `κˣ →* Gal(L/κ)` with kernel `N(Lˣ)`".  Such a statement
does not compose: two Artin maps produced by it differ by an automorphism of `Gal(L/κ)`, so there
is no canonical way to compare the maps of different levels, and hence no canonical map at the
infinite level.

The mathematical input that is missing is the *canonical*, restriction-compatible family of
reciprocity isomorphisms.  This file packages it as a single object: since the maps of a
compatible family are exactly the composites of one homomorphism `Fˣ →* Gal(F'/F)` with the
restriction maps `Gal(F'/F) →* Gal(L/F)`, a canonical family is the same thing as a single
homomorphism

`artin : Fˣ →* Gal(F'/F)`

whose restriction to every finite abelian Galois subextension `L` of `F'` is surjective with kernel
`N_{L/F} Lˣ`.  Restriction-compatibility is then automatic.  We call such an object a
`LocalReciprocityDatum`.

In the concrete setting `F = Q.adicCompletion K` the datum can be constructed unconditionally on
the subfamily of *unramified* extensions: this is `NK.LocalReciprocity.artinUnramified`
(together with `NK.LocalReciprocity.localRestrict_artinUnramified`, which shows that those
unramified Artin maps are the restrictions of one another, i.e. compatible).  Constructing the
datum on all finite abelian extensions is the existence theorem of local class field theory /
Lubin–Tate; it is stated as the explicit input in `NK.LocalReciprocity.LubinTateInput`.

The level condition for `L` is stated for `L : IntermediateField F F'` carrying
`FiniteDimensional F L` and `Normal F L` together with commutativity of `Gal(L/F)`; in applications
`Normal` comes from `IsGalois` (`IsGalois.to_normal`).
-/

open scoped Classical

namespace NK.LocalReciprocity

universe u v

noncomputable section

variable {F : Type u} {F' : Type v} [Field F] [Field F'] [Algebra F F']

/-- **The reciprocity datum of local class field theory** for a local field `F` with separable
closure `F'`: a group homomorphism from `Fˣ` to the absolute Galois group which induces the
reciprocity isomorphism `Fˣ ⧸ N_{L/F} Lˣ ≃* Gal(L/F)` on every finite abelian Galois subextension
`L` of `F'`, and whose norm groups are cofinal among the finite-index subgroups of `Fˣ` (the
existence theorem: every finite quotient of `Fˣ` is a Galois group of a finite abelian extension).

* `artin` is the canonical Artin map (in the unramified case the one constructed in
  `NK.LocalReciprocity.artinUnramified`);
* `isLevelIso` is the reciprocity isomorphism on each finite abelian level;
* `cofinal` is the surjectivity/existence half of the main theorem of local class field theory.

Because the level maps are all obtained from the single map `artin` by restriction, they are
automatically compatible with the restriction maps. -/
structure LocalReciprocityDatum (F : Type u) (F' : Type v) [Field F] [Field F'] [Algebra F F'] where
  /-- the Artin map `Fˣ →* Gal(F'/F)`. -/
  artin : Fˣ →* (F' ≃ₐ[F] F')
  /-- on every finite abelian Galois subextension, `artin` induces the reciprocity isomorphism
  with the norm group as kernel. -/
  isLevelIso : ∀ (L : IntermediateField F F') [FiniteDimensional F L] [Normal F L]
      (_ : ∀ σ τ : L ≃ₐ[F] L, σ * τ = τ * σ),
      Function.Surjective ((AlgEquiv.restrictNormalHom (F := F) (K₁ := F') L).comp artin) ∧
      MonoidHom.ker ((AlgEquiv.restrictNormalHom (F := F) (K₁ := F') L).comp artin) =
        normGroup F L
  /-- the existence theorem: the norm groups of the finite **abelian** levels are cofinal among
  the finite-index subgroups of `Fˣ`.  (The restriction to abelian levels is essential: only those
  levels are related to `artin` by `isLevelIso`, so it is only their norm groups that the Artin map
  sees.  Equivalently, this axiom says that the Artin map is surjective onto every finite quotient
  of `Fˣ` and that its kernel is trivial on the completion.) -/
  cofinal : ∀ M : Subgroup Fˣ, M.FiniteIndex →
      ∃ (L : IntermediateField F F') (_ : FiniteDimensional F L) (_ : Normal F L)
        (_ : ∀ σ τ : L ≃ₐ[F] L, σ * τ = τ * σ), normGroup F L ≤ M

namespace LocalReciprocityDatum

variable (D : LocalReciprocityDatum F F')
  (L : IntermediateField F F') [FiniteDimensional F L] [Normal F L]
  (hcomm : ∀ σ τ : L ≃ₐ[F] L, σ * τ = τ * σ)

include D hcomm

/-- **The Artin map at a finite abelian level**, `Fˣ ⧸ N_{L/F} Lˣ →* Gal(L/F)`: the map induced by
`artin` on the quotient by the norm group. -/
def artinLevelHom : (Fˣ ⧸ normGroup F L) →* (L ≃ₐ[F] L) :=
  QuotientGroup.lift (normGroup F L)
    ((AlgEquiv.restrictNormalHom (F := F) (K₁ := F') L).comp D.artin)
    (by rw [(D.isLevelIso L hcomm).2])

/-- The Artin map at a level is induced by `artin` on representatives. -/
theorem artinLevelHom_mk (x : Fˣ) :
    D.artinLevelHom L hcomm (QuotientGroup.mk x) =
      (AlgEquiv.restrictNormalHom (F := F) (K₁ := F') L) (D.artin x) :=
  QuotientGroup.lift_mk' (normGroup F L) _ x

theorem artinLevelHom_surjective : Function.Surjective (D.artinLevelHom L hcomm) := by
  intro g
  obtain ⟨x, hx⟩ := (D.isLevelIso L hcomm).1 g
  refine ⟨QuotientGroup.mk x, ?_⟩
  rw [artinLevelHom_mk]
  simpa using hx

theorem artinLevelHom_injective : Function.Injective (D.artinLevelHom L hcomm) := by
  intro a b hab
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  rw [artinLevelHom_mk, artinLevelHom_mk] at hab
  have hab' : ((AlgEquiv.restrictNormalHom (F := F) (K₁ := F') L) (D.artin x)) *
      ((AlgEquiv.restrictNormalHom (F := F) (K₁ := F') L) (D.artin y))⁻¹ = 1 := by
    rw [hab, mul_inv_cancel]
  have hmem : x * y⁻¹ ∈ MonoidHom.ker
      ((AlgEquiv.restrictNormalHom (F := F) (K₁ := F') L).comp D.artin) := by
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    exact hab'
  rw [(D.isLevelIso L hcomm).2] at hmem
  refine (QuotientGroup.eq).mpr ?_
  have hinv : (x * y⁻¹)⁻¹ ∈ normGroup F L := inv_mem hmem
  rwa [mul_inv_rev, inv_inv, mul_comm] at hinv

/-- **The canonical reciprocity isomorphism at a finite abelian level**:
`Fˣ ⧸ N_{L/F} Lˣ ≃* Gal(L/F)`.  This is the reciprocity isomorphism of local class field theory,
in the *canonical* (restriction-compatible) form provided by the datum. -/
def artinLevelMulEquiv : (Fˣ ⧸ normGroup F L) ≃* (L ≃ₐ[F] L) :=
  MulEquiv.ofBijective _ ⟨D.artinLevelHom_injective L hcomm, D.artinLevelHom_surjective L hcomm⟩

/-- The Artin isomorphism is the map induced by the Artin map of the datum. -/
theorem artinLevelMulEquiv_mk (x : Fˣ) :
    ((D.artinLevelMulEquiv L hcomm) (QuotientGroup.mk x) : L ≃ₐ[F] L) =
      (AlgEquiv.restrictNormalHom (F := F) (K₁ := F') L) (D.artin x) :=
  D.artinLevelHom_mk L hcomm x

end LocalReciprocityDatum

section MaxAbelian

variable [IsGalois F F']

/-- **The maximal abelian subextension** of `F'` over `F`: the fixed field of the commutator
subgroup of `Gal(F'/F)`.  Its Galois group `Gal(F^{ab}/F)` is the abelianised absolute Galois
group `G_F^{ab}` appearing in the infinite-level reciprocity theorem. -/
def maxAbelianSubext (F : Type u) (F' : Type v) [Field F] [Field F'] [Algebra F F'] :
    IntermediateField F F' :=
  IntermediateField.fixedField (commutator (F' ≃ₐ[F] F'))

end MaxAbelian

end

end NK.LocalReciprocity
