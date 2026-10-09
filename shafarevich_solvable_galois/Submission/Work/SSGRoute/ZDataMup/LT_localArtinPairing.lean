import Mathlib
import Submission.Work.SSGRoute.LT_LocalCFTUmbrella
import Submission.Work.SSGRoute.localKummerReciprocity
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local Artin pairing: first pieces

This file collects the pieces of the *local Kummer–Artin pairing* at a level-`K` local group
`H_A = decomp k A ⊓ K.fixingSubgroup` that are purely local (Galois-theoretic + local class field
theory), with no global input:

* `LT_maxAbelian_fixingSubgroup_le_ker`: a locally constant character
  `χ : Gal(F'/F) →* Multiplicative (ZMod p)` kills `Gal(F'/F^{ab}) = (maxAbelianSubext F F').fixingSubgroup`.
  This is what lets one *evaluate* `χ` on the abelianised absolute Galois group, hence on the image of
  the local Artin map `D.artin : Fˣ →* AbGal F F'`.

The proof is: `χ` has open kernel, hence closed kernel; its image is abelian, so the (abstract)
commutator subgroup lies in the kernel, and since the kernel is closed it contains the *closure* of
the commutator, i.e. `Gal(F'/F^{ab})` (the fixing subgroup of `maxAbelianSubext`, which is the fixed
field of the commutator subgroup).
-/

namespace Work.SSGRoute.ZDataMup

open scoped commutatorElement

/-- **A locally constant abelian character kills the absolute Galois group of the maximal abelian
subextension.**  For a Galois extension `F'/F`, a locally constant character `χ` of `Gal(F'/F)`
with values in an abelian group is trivial on `Gal(F'/F^{ab})`.

Concretely: the (abstract) commutator subgroup `⁅⊤,⊤⁆` lies in `χ.ker` because the target is
abelian; `χ.ker` is open (local constancy) hence closed; so it contains the closure of the commutator
subgroup, and the fixing subgroup of `maxAbelianSubext F F' = fixedField (commutator Gal(F'/F))` is
that closure (as `maxAbelianSubext` is the fixed field of a closed subgroup). -/
theorem LT_maxAbelian_fixingSubgroup_le_ker {F F' : Type} [Field F] [Field F'] [Algebra F F']
    [IsGalois F F'] (p : ℕ) [Fact p.Prime] (χ : ↥(Work.SSGRoute.lcHoms p (F' ≃ₐ[F] F'))) :
    (NK.LocalReciprocity.maxAbelianSubext F F').fixingSubgroup ≤ (χ.1).ker := by
  -- the commutator subgroup lies in the kernel
  have hcomm : commutator (F' ≃ₐ[F] F') ≤ (χ.1).ker := by
    rw [commutator_def]
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker]
    show χ.1 ⁅a, b⁆ = 1
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_cancel_comm]
    exact mul_inv_cancel _
  -- the kernel is open, hence closed
  have hopen : IsOpen (((χ.1).ker : Subgroup (F' ≃ₐ[F] F')) : Set (F' ≃ₐ[F] F')) :=
    (IsLocallyConstant.iff_isOpen_fiber).mp χ.2 1
  have hclosed : IsClosed (((χ.1).ker : Subgroup (F' ≃ₐ[F] F')) : Set (F' ≃ₐ[F] F')) :=
    Subgroup.isClosed_of_isOpen (χ.1).ker hopen
  -- the fixed field of the kernel lies in `F^{ab}`, since its Galois group is the abelian image of `χ`
  have hle : (IntermediateField.fixedField (χ.1).ker) ≤
      NK.LocalReciprocity.maxAbelianSubext F F' := by
    rw [NK.LocalReciprocity.maxAbelianSubext]
    exact IntermediateField.fixedField_antitone hcomm
  -- `fixingSubgroup` is antitone and inverts `fixedField` on closed subgroups
  have hfix : (IntermediateField.fixedField (χ.1).ker).fixingSubgroup = (χ.1).ker :=
    InfiniteGalois.fixingSubgroup_fixedField (⟨(χ.1).ker, hclosed⟩ : ClosedSubgroup (F' ≃ₐ[F] F'))
  calc (NK.LocalReciprocity.maxAbelianSubext F F').fixingSubgroup
      ≤ (IntermediateField.fixedField (χ.1).ker).fixingSubgroup :=
        IntermediateField.fixingSubgroup_antitone hle
    _ = (χ.1).ker := hfix

/-- **Non-degeneracy of the local Artin pairing in its second variable (local Kummer duality).**

Let `D : NK.LocalReciprocity.LocalReciprocityDatum F F'` be a local reciprocity datum, i.e. an
Artin map `D.artin : Fˣ →* Gal(F'/F)` which is surjective with kernel the norm group at every
finite normal abelian subextension `L ≤ F'`.  Then a locally constant character
`χ : Gal(F'/F) →* Multiplicative (ZMod p)` which is trivial on the image of `D.artin` is trivial.

Equivalently: `rec(κˣ)` is *dense* (indeed, meets every finite abelian quotient surjectively), so a
continuous character vanishing on the image of the local Artin map vanishes identically.  This is
the local input of the first-variable non-degeneracy of the form `F_A(x,y) = x(rec(a_y))`: if
`F_A(x, ·) = 0` then the character `x` kills `rec(κˣ)`, hence `x = 0`.

The proof is: the (open, hence closed) kernel of `χ` cuts out a finite normal `L ≤ F'` on which `χ`
descends to an *injective* character `χ_L` of `Gal(L/F)`; injectivity into an abelian group makes
`Gal(L/F)` commutative, so `D.isLevelIso` applies and `(restrictNormalHom L) ∘ D.artin` is
surjective onto `Gal(L/F)`; evaluating `χ_L` at a preimage of an arbitrary `σ|_L` gives
`χ σ = χ (D.artin a) = 1`. -/
theorem LT_localReciprocity_kills_of_artin {F F' : Type} [Field F] [Field F'] [Algebra F F']
    [IsGalois F F'] (D : NK.LocalReciprocity.LocalReciprocityDatum F F') (p : ℕ) [Fact p.Prime]
    (χ : ↥(Work.SSGRoute.lcHoms p (F' ≃ₐ[F] F')))
    (h : ∀ a : Fˣ, χ.1 (D.artin a) = 1) : χ.1 = 1 := by
  classical
  -- the kernel of `χ` is open, hence closed
  have hopen : IsOpen (((χ.1).ker : Subgroup (F' ≃ₐ[F] F')) : Set (F' ≃ₐ[F] F')) :=
    (IsLocallyConstant.iff_isOpen_fiber).mp χ.2 1
  have hclosed : IsClosed (((χ.1).ker : Subgroup (F' ≃ₐ[F] F')) : Set (F' ≃ₐ[F] F')) :=
    Subgroup.isClosed_of_isOpen (χ.1).ker hopen
  -- the finite Galois level cut out by `χ`
  let L : IntermediateField F F' := IntermediateField.fixedField (χ.1).ker
  have hLfix : L.fixingSubgroup = (χ.1).ker :=
    InfiniteGalois.fixingSubgroup_fixedField (⟨(χ.1).ker, hclosed⟩ : ClosedSubgroup (F' ≃ₐ[F] F'))
  haveI hfin : FiniteDimensional F L := by
    have hLop : IsOpen (L.fixingSubgroup : Set (F' ≃ₐ[F] F')) := by rw [hLfix]; exact hopen
    exact (InfiniteGalois.isOpen_iff_finite L).mp hLop
  haveI hnorm : Normal F L := by
    haveI : L.fixingSubgroup.Normal := by rw [hLfix]; infer_instance
    exact (InfiniteGalois.normal_iff_isGalois L).mp inferInstance |>.to_normal
  have hsurjρ : Function.Surjective (AlgEquiv.restrictNormalHom (F := F) (K₁ := F') L) :=
    AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := ↥L) (E := F')
  have hkerρ : (AlgEquiv.restrictNormalHom (F := F) (K₁ := F') L).ker ≤ (χ.1).ker := by
    rw [IntermediateField.restrictNormalHom_ker]; exact le_of_eq hLfix
  -- the descent of `χ` to `Gal(L/F)`
  set χL : (↥L ≃ₐ[F] ↥L) →* Multiplicative (ZMod p) :=
    (MonoidHom.liftOfRightInverse (AlgEquiv.restrictNormalHom (F := F) (K₁ := F') L)
      (Function.surjInv hsurjρ) (Function.surjInv_eq hsurjρ)) ⟨χ.1, hkerρ⟩ with hχL
  have hχL_apply : ∀ σ : F' ≃ₐ[F] F',
      χL (AlgEquiv.restrictNormalHom (F := F) (K₁ := F') L σ) = χ.1 σ := fun σ =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨χ.1, hkerρ⟩ σ
  -- `χL` is injective, so `Gal(L/F)` embeds in an abelian group
  have hχL_inj : Function.Injective χL := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    obtain ⟨x, hx⟩ := hsurjρ σ
    have hx1 : x ∈ (χ.1).ker := by
      rw [MonoidHom.mem_ker, ← hχL_apply x, hx, hσ]
    have hxρ : x ∈ (AlgEquiv.restrictNormalHom (F := F) (K₁ := F') L).ker := by
      rw [IntermediateField.restrictNormalHom_ker, hLfix]; exact hx1
    rw [← hx, MonoidHom.mem_ker.mp hxρ]
  have hcomm : ∀ σ τ : ↥L ≃ₐ[F] ↥L, σ * τ = τ * σ := by
    intro σ τ
    refine hχL_inj ?_
    rw [map_mul, map_mul, mul_comm]
  -- the local reciprocity isomorphism at the level `L`
  obtain ⟨hsurjL, -⟩ := D.isLevelIso L hcomm
  have hσ1 : ∀ σ : F' ≃ₐ[F] F', χ.1 σ = 1 := by
    intro σ
    obtain ⟨a, ha⟩ := hsurjL (AlgEquiv.restrictNormalHom (F := F) (K₁ := F') L σ)
    have h1 : χ.1 σ = χL (AlgEquiv.restrictNormalHom (F := F) (K₁ := F') L σ) :=
      (hχL_apply σ).symm
    rw [h1, ← ha, MonoidHom.comp_apply, hχL_apply, h a]
  exact MonoidHom.ext hσ1

end Work.SSGRoute.ZDataMup
