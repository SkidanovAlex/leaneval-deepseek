import Mathlib
import Submission.NK.GlobalCFTdeep.FundamentalClassReduction
import Submission.NK.GlobalCFT.Cohomology
import Submission.NK.GlobalCFT.NormGroup.Basic
import Submission.NK.GlobalCFTdeep.CoCore.Reciprocity
import Submission.NK.GlobalCFT.Reciprocity
import Submission.NK.NUV2.ArtinBridge.index_eq_card_abelianization_of_fundamentalClassElement
import Submission.NK.NUV2.ArtinBridge.exists_ellPowerLevel_normClassSubgroup_le
import Submission.NK.GlobalCFTdeep.normClassSubgroup_index_ne_zero
import Submission.Commons.NumberTheory.NumberField.numberField_of_intermediateField

/-!
# The norm limitation theorem and the descent step of Takagi's existence theorem

The target of this file is `NK.NUV2.ArtinBridge.normLimitation`, the `Descent` step of the
existence theorem of global class field theory (Milne, *Class Field Theory*, Lemma 9.4):

if a subgroup `N ≤ C_K` contains the norms of `N_{L/K₁}C_L` for a tower `K ⊆ K₁ ⊆ L` with `K₁/K`
abelian Galois and `L/K₁` Galois, then `N` contains the norm group `N_{M/K}C_M` of a finite
**abelian** extension `M/K`.

This is the classical **Norm Limitation Theorem** (Milne, *CFT*, Theorem 4.8): the norm group of a
finite extension is that of its maximal abelian subextension.

## The route

* `normClassSubgroup_le_of_le_comap`: the hypothesis is `N_{L/K}C_L ≤ N`, by the transitivity of
  the norm `N_{L/K} = N_{K₁/K} ∘ N_{L/K₁}` on idèle class groups.
* `galoisClosureNormLe`: every finite extension `L/K` of number fields lies in a finite Galois
  extension `L̃/K` with `N_{L̃/K}C_{L̃} ≤ N_{L/K}C_L` — the Galois closure.
* `exists_abelian_normClassSubgroup_le_of_isGalois`: for a finite **Galois** extension `L̃/K`, the
  fixed field `M` of the commutator subgroup of `Gal(L̃/K)` is abelian Galois over `K` and has
  `N_{M/K}C_M = N_{L̃/K}C_{L̃}`.  The two norms have the same index — `|Gal(L̃/K)ᵃᵇ|`, by the norm
  index theorem derived from the fundamental class `hFC` — and the tower inclusion
  `N_{L̃/K}C_{L̃} ≤ N_{M/K}C_M` upgrades to an equality.

Nothing here is circular: only the *norm index theorem* `[C_K : N_{L/K}C_L] = |Gal(L/K)ᵃᵇ|` for
Galois `L/K` is used, which is available unconditionally from `hFC` in
`NK.NUV2.ArtinBridge.index_eq_card_abelianization_of_fundamentalClassElement`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField IsMulCommutative

noncomputable section

namespace NK.NUV2.ArtinBridge

open NK.GlobalCFT

/-! ## Transitivity of the norm, in descent form -/

/-- **Transitivity of the norm on norm subgroups, in descent form.**  If a subgroup `N` of the
idèle class group of `K` contains the norms of `N_{L/K₁}C_L` in the sense that
`N_{L/K₁}C_L ≤ N.comap (N_{K₁/K})`, then `N` contains the norm subgroup `N_{L/K}C_L`, because
`N_{L/K}C_L = N_{K₁/K}(N_{L/K₁}C_L)` by the transitivity of the norm. -/
theorem normClassSubgroup_le_of_le_comap {K K₁ L : Type} [Field K] [NumberField K] [Field K₁]
    [NumberField K₁] [Field L] [NumberField L] [Algebra K K₁] [FiniteDimensional K K₁]
    [Algebra K₁ L] [FiniteDimensional K₁ L] [Algebra K L] [IsScalarTower K K₁ L]
    [FiniteDimensional K L] (N : Subgroup (IdeleClassGroup K)) :
    Idele.normClassSubgroup K₁ L ≤ N.comap (IdeleClassGroup.normClassHom K K₁) →
    Idele.normClassSubgroup K L ≤ N := by
  intro hN
  suffices h : Idele.normClassSubgroup K L =
      (Idele.normClassSubgroup K₁ L).map (IdeleClassGroup.normClassHom K K₁) by
    rw [h]
    exact Subgroup.map_le_iff_le_comap.mpr hN
  have hcomp : (IdeleClassGroup.normClassHom K K₁).comp
      (IdeleClassGroup.normClassHom K₁ L) = IdeleClassGroup.normClassHom K L :=
    MonoidHom.ext fun q => NormGroup.globalCFT_normClassHom_trans q
  calc Idele.normClassSubgroup K L
      = (IdeleClassGroup.normClassHom K L).range :=
        Idele.normClassSubgroup_eq_range (K := K) (L := L)
    _ = ((IdeleClassGroup.normClassHom K K₁).comp
            (IdeleClassGroup.normClassHom K₁ L)).range := by rw [hcomp]
    _ = (IdeleClassGroup.normClassHom K₁ L).range.map
            (IdeleClassGroup.normClassHom K K₁) := MonoidHom.range_comp _ _
    _ = (Idele.normClassSubgroup K₁ L).map (IdeleClassGroup.normClassHom K K₁) := by
        rw [← Idele.normClassSubgroup_eq_range (K := K₁) (L := L)]

/-! ## The Galois closure -/

/-- **Galois closure with a norm-group bound.**  Every finite extension `L/K` of number fields is
contained in a finite Galois extension `M/K` whose norm subgroup is contained in that of `L`:
take for `M` the Galois closure `NK.GlobalCFTdeep.galoisClosure K L` of `L/K`, which is finite
Galois over `K` and contains `L`, so that `N_{M/K}C_M ≤ N_{L/K}C_L` by the tower monotonicity of
the norm subgroups. -/
theorem galoisClosureNormLe {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] :
    ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : Algebra K M) (_ : FiniteDimensional K M)
      (_ : IsGalois K M),
      Idele.normClassSubgroup K M ≤ Idele.normClassSubgroup K L := by
  haveI : FiniteDimensional L (NK.GlobalCFTdeep.galoisClosure K L) :=
    Module.Finite.right K L _
  haveI : NumberField (NK.GlobalCFTdeep.galoisClosure K L) :=
    NumberField.of_module_finite K (NK.GlobalCFTdeep.galoisClosure K L)
  haveI : IsGalois K (NK.GlobalCFTdeep.galoisClosure K L) :=
    Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  exact ⟨NK.GlobalCFTdeep.galoisClosure K L, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, Idele.normClassSubgroup_le_of_tower⟩

/-! ## The norm limitation theorem for a Galois extension -/

/-- **Norm limitation for a finite Galois extension.**  For a finite Galois extension `L/K` of
number fields there is an abelian Galois subextension `M ⊆ L` whose norm subgroup equals that of
`L`, namely the fixed field of the commutator subgroup of `Gal(L/K)`: the norm subgroups of `L`
and of `M` both have index `|Gal(L/K)ᵃᵇ|` in `C_K`, and the tower inclusion goes the right way.

The index computation `[C_K : N_{L'/K}C_{L'}] = |Gal(L'/K)ᵃᵇ|` is the norm index theorem, available
from the fundamental class `hFC`. -/
theorem exists_abelian_normClassSubgroup_le_of_isGalois
    (hFC : NK.GlobalCFTdeep.FundamentalClassElement)
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    ∃ (M : IntermediateField K L), IsGalois K ↥M ∧ IsMulCommutative (↥M ≃ₐ[K] ↥M) ∧
      Idele.normClassSubgroup K ↥M ≤ Idele.normClassSubgroup K L := by
  -- The maximal abelian subextension: the fixed field of the commutator subgroup.
  let H : Subgroup (L ≃ₐ[K] L) := commutator (L ≃ₐ[K] L)
  haveI : H.Normal := Subgroup.commutator_normal (⊤ : Subgroup (L ≃ₐ[K] L)) ⊤
  let M : IntermediateField K L := IntermediateField.fixedField H
  haveI : IsGalois K ↥M := IsGalois.of_fixedField_normal_subgroup H
  haveI : FiniteDimensional K ↥M := IntermediateField.finiteDimensional_left M
  haveI : NumberField ↥M := Commons.NumberTheory.NumberField.numberField_of_intermediateField M
  -- The index formula at both fields.
  have hidxL : (Idele.normClassSubgroup K L).index = Nat.card (Abelianization (L ≃ₐ[K] L)) :=
    index_eq_card_abelianization_of_fundamentalClassElement hFC
  have hidxM : (Idele.normClassSubgroup K ↥M).index =
      Nat.card (Abelianization (↥M ≃ₐ[K] ↥M)) :=
    index_eq_card_abelianization_of_fundamentalClassElement hFC
  -- `Gal(M/K)` is the abelianisation of `Gal(L/K)`.
  have eG : (↥M ≃ₐ[K] ↥M) ≃* Abelianization (L ≃ₐ[K] L) :=
    (IsGalois.normalAutEquivQuotient (K := K) (L := L) H).symm
  have hcard : Nat.card (↥M ≃ₐ[K] ↥M) = Nat.card (Abelianization (L ≃ₐ[K] L)) :=
    Nat.card_congr eG.toEquiv
  haveI : IsMulCommutative (↥M ≃ₐ[K] ↥M) :=
    IsMulCommutative.of_comm fun a b => eG.injective (by rw [map_mul, map_mul, mul_comm])
  have hcardAb : Nat.card (Abelianization (↥M ≃ₐ[K] ↥M)) = Nat.card (↥M ≃ₐ[K] ↥M) :=
    (Nat.card_congr (Abelianization.equivOfComm (H := ↥M ≃ₐ[K] ↥M)).toEquiv).symm
  have hidxEq : (Idele.normClassSubgroup K L).index = (Idele.normClassSubgroup K ↥M).index := by
    rw [hidxL, hidxM, hcardAb, hcard]
  -- The tower inclusion and the equality of indices force equality of the norm subgroups.
  have htower : Idele.normClassSubgroup K L ≤ Idele.normClassSubgroup K ↥M :=
    Idele.normClassSubgroup_le_of_tower
  have hne : (Idele.normClassSubgroup K ↥M).index ≠ 0 :=
    NK.GlobalCFTdeep.normClassSubgroup_index_ne_zero
  refine ⟨M, inferInstance, inferInstance, ?_⟩
  rw [← subgroup_eq_of_le_of_index_eq htower hidxEq hne]

/-! ## The descent step of Takagi's existence theorem -/

/-- **Norm limitation / the descent step of the existence theorem.**  Let `K ⊆ K₁ ⊆ L` be a tower
of number fields with `K₁/K` abelian Galois and `L/K₁` Galois, and let `N ≤ C_K` be a subgroup
containing the norms of `N_{L/K₁}C_L` in the sense that
`N_{L/K₁}C_L ≤ N.comap (N_{K₁/K})`.  Then `N` contains the norm group of a finite abelian
extension `M/K`.

This is Milne, *CFT*, Lemma 9.4 together with the Norm Limitation Theorem (Milne, *CFT*, Theorem
4.8): the hypothesis says `N_{L/K}C_L ≤ N`; passing to a Galois closure and then to the maximal
abelian subextension replaces the extension `L/K` by an abelian one without enlarging the norm
group. -/
theorem normLimitation (hFC : NK.GlobalCFTdeep.FundamentalClassElement) :
    ∀ (K K₁ L : Type) [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Field L]
      [NumberField L] [Algebra K K₁] [FiniteDimensional K K₁] [Algebra K₁ L] [FiniteDimensional K₁ L]
      [IsGalois K K₁] [IsMulCommutative (K₁ ≃ₐ[K] K₁)]
      [IsGalois K₁ L] [IsMulCommutative (L ≃ₐ[K₁] L)]
      (N : Subgroup (NK.GlobalCFT.IdeleClassGroup K)),
      NK.GlobalCFT.Idele.normClassSubgroup K₁ L ≤
        N.comap (NK.GlobalCFT.IdeleClassGroup.normClassHom K K₁) →
      ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : Algebra K M)
        (_ : FiniteDimensional K M) (_ : IsGalois K M) (_ : IsMulCommutative (M ≃ₐ[K] M)),
        NK.GlobalCFT.Idele.normClassSubgroup K M ≤ N := by
  intro K K₁ L _ _ _ _ _ _ _ _ _ _ _ _ _ _ N hN
  -- The `K`-algebra structure on `L` coming from the tower `K ⊆ K₁ ⊆ L`.
  letI : Algebra K L := RingHom.toAlgebra ((algebraMap K₁ L).comp (algebraMap K K₁))
  haveI : IsScalarTower K K₁ L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : FiniteDimensional K L := FiniteDimensional.trans K K₁ L
  -- Step 1: the hypothesis says that `N` contains the norms from `L`.
  have hNL : Idele.normClassSubgroup K L ≤ N := normClassSubgroup_le_of_le_comap N hN
  -- Step 2: replace `L` by its Galois closure over `K`.
  obtain ⟨L', hFieldL', hNFL', hAlgL', hFDL', hGalL', hleL'⟩ := galoisClosureNormLe (K := K) (L := L)
  letI : Field L' := hFieldL'
  letI : NumberField L' := hNFL'
  letI : Algebra K L' := hAlgL'
  letI : FiniteDimensional K L' := hFDL'
  letI : IsGalois K L' := hGalL'
  -- Step 3: take the maximal abelian subextension of the Galois closure.
  obtain ⟨M, hGalM, hCommM, hleM⟩ :=
    exists_abelian_normClassSubgroup_le_of_isGalois hFC (K := K) (L := L')
  refine ⟨↥M, inferInstance, inferInstance, inferInstance, inferInstance, hGalM, hCommM, ?_⟩
  exact le_trans hleM (le_trans hleL' hNL)

end NK.NUV2.ArtinBridge

end
