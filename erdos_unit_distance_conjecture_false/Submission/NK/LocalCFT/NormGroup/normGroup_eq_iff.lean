import Mathlib
import Submission.NK.LocalCFT.Basic

/-!
# The norm group determines the abelian level

Let `F' / F` be a Galois extension, `A = F^{ab} = NK.LocalReciprocity.maxAbelianSubext F F'`
its maximal abelian subextension, and let `D : NK.LocalCFT.ArtinReciprocity F F'` be the
canonical local Artin reciprocity datum: the Artin map `artin : Fˣ →* Gal(F^{ab}/F)` whose
composite with the restriction `Gal(F^{ab}/F) →* Gal(L/F)` to a finite abelian level `L ≤ F^{ab}`
is surjective with kernel `N_{L/F} Lˣ`.

This file proves that the resulting map

`L ↦ NK.LocalReciprocity.normGroup F L`,   `L ≤ F^{ab}` finite abelian,

is **injective**: the norm group of a finite abelian level determines the level
(`NK.LocalCFT.NormGroup.normGroup_eq_iff`, the requested lemma), and it is as such part of the
Galois correspondence of local class field theory — it is what lets one pass between finite
abelian extensions of `F` inside `F^{ab}` and finite-index subgroups of `Fˣ`.  The companion
`normGroup_eq_iff_le_iff` gives the order-theoretic half of the same statement
(`N(L₁) ≤ N(L₂) ↔ L₂ ≤ L₁`).

## Route

Everything rests on the identification of the norm group at a level `L` with the preimage under
the Artin map of the *fixing subgroup* of `L`:

* `normGroup_eq_iff_comap_fixingSubgroup`: `N_{L/F} Lˣ = L.fixingSubgroup.comap artin`
  (this is the kernel condition of the reciprocity datum, transported along
  `IntermediateField.restrictNormalHom_ker`);
* `normGroup_eq_iff_index_eq_finrank`: consequently
  `(N_{L/F} Lˣ).index = [L : F]`, via the level reciprocity isomorphism
  `Fˣ ⧸ N_{L/F} Lˣ ≃* Gal(L/F)` of `NK.LocalCFT.ArtinReciprocity.artinLevelMulEquiv` and
  `IsGalois.card_aut_eq_finrank`;
* `normGroup_eq_iff_sup_eq_inf`: `N_{L₁L₂/F}(L₁L₂)ˣ = N_{L₁/F} L₁ˣ ∩ N_{L₂/F} L₂ˣ`
  (the second class-formation axiom), from `IntermediateField.fixingSubgroup_sup` and the fact
  that `comap` preserves infima.

Given `N(L₁) = N(L₂)`, the third formula gives `N(L₁ ⊔ L₂) = N(L₁)`, so the index formula gives
`[L₁ ⊔ L₂ : F] = [L₁ : F]`, whence `L₁ = L₁ ⊔ L₂` and, symmetrically, `L₂ = L₁ ⊔ L₂`.
The same comparison of indices with `N(L₁) ≤ N(L₂)` in place of equality gives
`N(L₁) ≤ N(L₂) ↔ L₂ ≤ L₁`.

Note that the composites `L₁ ⊔ L₂` are automatically finite (`FiniteDimensional`) and normal over
`F` (`IntermediateField.normal_sup`), and that `Gal(K/F)` is commutative for every normal level
`K ≤ F^{ab}` (`normGroup_eq_iff_commutative_gal`: it is a quotient of the commutative group
`Gal(F^{ab}/F)`), so all the levels that occur satisfy the hypotheses of the reciprocity datum —
in particular the requested hypotheses `h₁`, `h₂` on `Gal(Lᵢ/F)` are not needed.
-/

set_option linter.unusedVariables false

namespace NK.LocalCFT.NormGroup

open scoped IntermediateField

universe u v

variable {F : Type u} {F' : Type v} [Field F] [Field F'] [Algebra F F'] [IsGalois F F']

/-- **Galois groups of levels of `F^{ab}` are commutative.**  Any finite normal level
`L ≤ F^{ab}` of the maximal abelian subextension has `Gal(L/F)` commutative: it is a quotient of
the commutative group `Gal(F^{ab}/F)` (`NK.LocalReciprocity.commutative_gal_maxAbelianSubext`),
the quotient map being the restriction `AlgEquiv.restrictNormalHom`.

This is what makes the reciprocity datum applicable at every finite normal level of `F^{ab}`. -/
theorem normGroup_eq_iff_commutative_gal
    (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F')) [Normal F L] :
    ∀ σ τ : ↥L ≃ₐ[F] ↥L, σ * τ = τ * σ := by
  have hAB : ∀ σ τ : ↥(NK.LocalReciprocity.maxAbelianSubext F F') ≃ₐ[F]
      ↥(NK.LocalReciprocity.maxAbelianSubext F F'), σ * τ = τ * σ :=
    NK.LocalReciprocity.commutative_gal_maxAbelianSubext
  intro σ τ
  obtain ⟨σ', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := F)
    (K₁ := ↥L) (E := ↥(NK.LocalReciprocity.maxAbelianSubext F F')) σ
  obtain ⟨τ', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := F)
    (K₁ := ↥L) (E := ↥(NK.LocalReciprocity.maxAbelianSubext F F')) τ
  rw [← map_mul, ← map_mul, hAB]

/-- A finite normal level of `F^{ab}` is a finite **Galois** extension of `F`: it is normal over
`F` by hypothesis, and separable because `F^{ab}/F` is (it is a subextension of the Galois
extension `F'/F`). -/
instance instIsGaloisLevelOfMaxAbelian
    (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F')) [Normal F L] :
    IsGalois F L :=
  isGalois_iff.mpr
    ⟨Algebra.IsSeparable.of_algHom F (↥(NK.LocalReciprocity.maxAbelianSubext F F'))
      (IntermediateField.val L), inferInstance⟩

/-- **The norm group as a preimage of the fixing subgroup.**  For a finite normal level `L` of
`F^{ab}`, the norm group `N_{L/F} Lˣ` is the preimage under the Artin map `artin` of the subgroup
`Gal(F^{ab}/L) = L.fixingSubgroup` of `Gal(F^{ab}/F)`.

Indeed, the reciprocity datum says that `N_{L/F} Lˣ` is the kernel of
`Gal(F^{ab}/F) → Gal(L/F) → artin`, i.e. the preimage of the kernel of the restriction, which is
`L.fixingSubgroup` by `IntermediateField.restrictNormalHom_ker`. -/
theorem normGroup_eq_iff_comap_fixingSubgroup (D : NK.LocalCFT.ArtinReciprocity F F')
    (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F L] [Normal F L] :
    NK.LocalReciprocity.normGroup F ↥L = L.fixingSubgroup.comap D.artin := by
  rw [← (D.isLevelIso L (normGroup_eq_iff_commutative_gal L)).2, NK.LocalCFT.levelRestrict,
    ← MonoidHom.comap_ker, IntermediateField.restrictNormalHom_ker]

/-- **The index of the norm group is the degree of the level.**  For a finite normal level `L` of
`F^{ab}` the index `[Fˣ : N_{L/F} Lˣ]` equals `[L : F]`.

This is immediate from the level reciprocity isomorphism
`NK.LocalCFT.ArtinReciprocity.artinLevelMulEquiv : Fˣ ⧸ N_{L/F} Lˣ ≃* Gal(L/F)` together with
`|Gal(L/F)| = [L : F]` for a finite Galois extension. -/
theorem normGroup_eq_iff_index_eq_finrank (D : NK.LocalCFT.ArtinReciprocity F F')
    (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F L] [Normal F L] :
    (NK.LocalReciprocity.normGroup F ↥L).index = Module.finrank F L := by
  rw [Subgroup.index_eq_card, ← IsGalois.card_aut_eq_finrank F ↥L]
  exact Nat.card_congr (D.artinLevelMulEquiv L (normGroup_eq_iff_commutative_gal L)).toEquiv

/-- **The compositum of two levels has norm group the intersection of the norm groups** (the
second class-formation axiom, for levels of `F^{ab}`): for finite normal levels `L₁, L₂ ≤ F^{ab}`,

  `N_{L₁L₂/F}(L₁L₂)ˣ = N_{L₁/F} L₁ˣ ⊓ N_{L₂/F} L₂ˣ`.

Since `L₁ ⊔ L₂` is again finite and normal over `F`, this follows from
`normGroup_eq_iff_comap_fixingSubgroup` applied to the three levels,
`IntermediateField.fixingSubgroup_sup` and `Subgroup.comap_inf`. -/
theorem normGroup_eq_iff_sup_eq_inf (D : NK.LocalCFT.ArtinReciprocity F F')
    (L₁ L₂ : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F L₁] [Normal F L₁] [FiniteDimensional F L₂] [Normal F L₂] :
    NK.LocalReciprocity.normGroup F ↥(L₁ ⊔ L₂) =
      NK.LocalReciprocity.normGroup F ↥L₁ ⊓ NK.LocalReciprocity.normGroup F ↥L₂ := by
  rw [normGroup_eq_iff_comap_fixingSubgroup D (L₁ ⊔ L₂),
    normGroup_eq_iff_comap_fixingSubgroup D L₁,
    normGroup_eq_iff_comap_fixingSubgroup D L₂,
    IntermediateField.fixingSubgroup_sup, Subgroup.comap_inf]

theorem normGroup_eq_iff {F : Type u} {F' : Type v} [Field F] [Field F'] [Algebra F F']
    [IsGalois F F'] (D : NK.LocalCFT.ArtinReciprocity F F')
    (L₁ L₂ : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F L₁] [Normal F L₁] [FiniteDimensional F L₂] [Normal F L₂]
    (h₁ : ∀ σ τ : ↥L₁ ≃ₐ[F] ↥L₁, σ * τ = τ * σ)
    (h₂ : ∀ σ τ : ↥L₂ ≃ₐ[F] ↥L₂, σ * τ = τ * σ) :
    NK.LocalReciprocity.normGroup F ↥L₁ = NK.LocalReciprocity.normGroup F ↥L₂ ↔ L₁ = L₂ := by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  -- Both levels are contained in the finite normal level `L₁ ⊔ L₂`, whose norm group is the
  -- intersection of the two norm groups, hence equal to `N(L₁)` (and to `N(L₂)`).
  have hK : NK.LocalReciprocity.normGroup F ↥(L₁ ⊔ L₂) =
      NK.LocalReciprocity.normGroup F ↥L₁ := by
    rw [normGroup_eq_iff_sup_eq_inf D L₁ L₂, h, inf_idem]
  -- Comparing indices of equal subgroups gives `[L₁ ⊔ L₂ : F] = [L₁ : F]`.
  have hfin : Module.finrank F ↥L₁ = Module.finrank F ↥(L₁ ⊔ L₂) := by
    rw [← normGroup_eq_iff_index_eq_finrank D L₁,
      ← normGroup_eq_iff_index_eq_finrank D (L₁ ⊔ L₂), hK]
  have h₁' : L₁ = L₁ ⊔ L₂ :=
    IntermediateField.eq_of_le_of_finrank_le le_sup_left (le_of_eq hfin.symm)
  -- The same argument on the other side.
  have hK₂ : NK.LocalReciprocity.normGroup F ↥(L₁ ⊔ L₂) =
      NK.LocalReciprocity.normGroup F ↥L₂ := by
    rw [normGroup_eq_iff_sup_eq_inf D L₁ L₂, h, inf_idem]
  have hfin₂ : Module.finrank F ↥L₂ = Module.finrank F ↥(L₁ ⊔ L₂) := by
    rw [← normGroup_eq_iff_index_eq_finrank D L₂,
      ← normGroup_eq_iff_index_eq_finrank D (L₁ ⊔ L₂), hK₂]
  have h₂' : L₂ = L₁ ⊔ L₂ :=
    IntermediateField.eq_of_le_of_finrank_le le_sup_right (le_of_eq hfin₂.symm)
  exact h₁'.trans h₂'.symm

/-- **The norm group map is antitone** — the order-theoretic companion of
`NK.LocalCFT.NormGroup.normGroup_eq_iff`: for finite normal levels `L₁, L₂ ≤ F^{ab}`,

  `N_{L₁/F} L₁ˣ ≤ N_{L₂/F} L₂ˣ ↔ L₂ ≤ L₁`.

The forward direction repeats the argument of `normGroup_eq_iff` with `N(L₁) ≤ N(L₂)` in place of
equality (`N(L₁ ⊔ L₂) = N(L₁) ⊓ N(L₂) = N(L₁)`), the converse is
`NK.LocalCFT.NormGroup.normGroup_eq_iff_comap_fixingSubgroup` plus anti-monotonicity of the
fixing subgroup. -/
theorem normGroup_eq_iff_le_iff (D : NK.LocalCFT.ArtinReciprocity F F')
    (L₁ L₂ : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F L₁] [Normal F L₁] [FiniteDimensional F L₂] [Normal F L₂] :
    NK.LocalReciprocity.normGroup F ↥L₁ ≤ NK.LocalReciprocity.normGroup F ↥L₂ ↔ L₂ ≤ L₁ := by
  constructor
  · intro h
    have hK : NK.LocalReciprocity.normGroup F ↥(L₁ ⊔ L₂) =
        NK.LocalReciprocity.normGroup F ↥L₁ := by
      rw [normGroup_eq_iff_sup_eq_inf D L₁ L₂, inf_eq_left.mpr h]
    have hfin : Module.finrank F ↥L₁ = Module.finrank F ↥(L₁ ⊔ L₂) := by
      rw [← normGroup_eq_iff_index_eq_finrank D L₁,
        ← normGroup_eq_iff_index_eq_finrank D (L₁ ⊔ L₂), hK]
    have h₁' : L₁ = L₁ ⊔ L₂ :=
      IntermediateField.eq_of_le_of_finrank_le le_sup_left (le_of_eq hfin.symm)
    exact h₁' ▸ le_sup_right
  · intro h
    rw [normGroup_eq_iff_comap_fixingSubgroup D L₁,
      normGroup_eq_iff_comap_fixingSubgroup D L₂]
    refine Subgroup.comap_mono fun σ hσ => ?_
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
    exact fun x hx => hσ x (h hx)

end NK.LocalCFT.NormGroup
