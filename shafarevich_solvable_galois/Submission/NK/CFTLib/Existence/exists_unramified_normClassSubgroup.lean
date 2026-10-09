import Mathlib
import Submission.NK.CFTLib.ArtinIdeal
import Submission.NK.GlobalCFT.NormGroup
import Submission.NK.CFTLib.Existence.exists_unramified_normClassSubgroup_of_kummer
import Submission.NK.CFTLib.Existence.cyclotomicExtension_galois_cyclic
import Submission.NK.CFTLib.Existence.index_comap_normClassHom_eq_prime
import Submission.NK.CFTLib.Existence.map_normIdeleHom_integralIdeles_le
import Submission.NK.NUV2.ArtinBridge.isOpen_comap_normClassHom
import Submission.NK.CFTLib.Existence.exists_galois_normClassSubgroup_eq_of_cyclotomic_descent_deg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The existence theorem at prime index (`K` arbitrary)

Every open finite-index subgroup `V ≤ C_K` of index `p` containing the image of the integral idèles
is the norm class subgroup of an everywhere unramified Galois extension of degree `p`.

The proof splits into the Kummer case (a primitive `p`-th root of unity in `K`) and the general case:
if `ζ_p ∉ K` one passes to `K' = K(ζ_p)` (of degree prime to `p`), applies the Kummer case to the
pullback `V.comap (N_{K'/K})`, and descends along `K'/K` with
`NK.CFTLib.Existence.exists_galois_normClassSubgroup_eq_of_cyclotomic_descent_deg`.

The arithmetic input is Hilbert reciprocity in the "one place omitted" form
(`NK.CFTLib.Existence.HasseNormOnePlace`), used only through the unramifiedness statement.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped NumberField RestrictedProduct IsMulCommutative
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.Existence

open NK.GlobalCFT

/-- **The idèles of `K'` which are local units at every finite place lie in the pullback of `V`
along the norm**, whenever `V` contains the image of the integral idèles of `K`. -/
theorem integralIdeles_map_le_comap_normClassHom
    {K : Type} [Field K] [NumberField K] {K' : Type} [Field K'] [NumberField K']
    [Algebra K K'] [FiniteDimensional K K']
    (V : Subgroup (IdeleClassGroup K))
    (hray : (Idele.integralIdeles K).map (IdeleClassGroup.mk K) ≤ V) :
    (Idele.integralIdeles K').map (IdeleClassGroup.mk K') ≤
      V.comap (IdeleClassGroup.normClassHom K K') := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  rw [Subgroup.mem_comap, IdeleClassGroup.normClassHom_mk]
  exact hray (Subgroup.mem_map.mpr
    ⟨Idele.normIdeleHom K K' y, map_normIdeleHom_integralIdeles_le (K := K) (K' := K') ⟨y, hy, rfl⟩, rfl⟩)

/-- **The existence theorem at prime index**, for an arbitrary number field `K`.

The hypothesis `hgap` is Hilbert reciprocity in the "one place omitted" form
(`NK.CFTLib.Existence.HasseNormOnePlace`); it is a theorem of the workspace
(`NK.CFTLib.IdeleHasse.badSet_not_singleton`, in flight). -/
theorem exists_unramified_normClassSubgroup
    (hARL : NK.CFTLib.ArtinReciprocityIdeal) (hFC : NK.GlobalCFTdeep.FundamentalClassElement)
    (hgap : HasseNormOnePlace)
    {K : Type} [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]
    (V : Subgroup (IdeleClassGroup K)) (hV : V.FiniteIndex)
    (hopen : IsOpen (V : Set (IdeleClassGroup K))) (hidx : V.index = p)
    (hray : (Idele.integralIdeles K).map (IdeleClassGroup.mk K) ≤ V) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (_ : FiniteDimensional K L),
      IsGalois K L ∧ Idele.normClassSubgroup K L = V ∧ Module.finrank K L = p ∧
      differentIdeal (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) = ⊤ ∧
      IsUnramifiedAtInfinitePlaces K L := by
  classical
  by_cases h : ∃ ζ : K, IsPrimitiveRoot ζ p
  · obtain ⟨ζ, hζ⟩ := h
    exact exists_unramified_normClassSubgroup_of_kummer (K := K) hARL hFC p hζ V hV hopen hidx
      hray hgap
  · -- `p ≠ 2`, since `-1` is a primitive square root of unity in any number field
    have hp2 : p ≠ 2 := by
      intro hp
      exact h ⟨-1, hp ▸ IsPrimitiveRoot.neg_one (R := K) 0 (by norm_num)⟩
    obtain ⟨K', hFK', hNK', hAK', hfdK', ζ, hζ, hgalK', hcommK', hcycK', hcop⟩ :=
      exists_cyclotomicExtension_galois_isCyclic K p h
    letI : Field K' := hFK'
    letI : NumberField K' := hNK'
    letI : Algebra K K' := hAK'
    letI : FiniteDimensional K K' := hfdK'
    haveI : IsGalois K K' := hgalK'
    haveI : IsMulCommutative (K' ≃ₐ[K] K') := hcommK'
    haveI : IsCyclic (K' ≃ₐ[K] K') := hcycK'
    -- the pullback `V' = V.comap (N_{K'/K})`
    have hidxK' : (Idele.normClassSubgroup K K').index = Module.finrank K K' :=
      NK.GlobalCFT.index_normClassSubgroup_eq_finrank
        (NK.GlobalCFTdeep.artinReciprocity_of_fundamentalClassElement hFC)
    have hcop' : ¬ p ∣ (Idele.normClassSubgroup K K').index := by
      rw [hidxK']; exact hcop
    have hV'index : (V.comap (IdeleClassGroup.normClassHom K K')).index = p :=
      index_comap_normClassHom_eq_prime (K := K) (K' := K') p V hidx hcop'
    have hV'fin : (V.comap (IdeleClassGroup.normClassHom K K')).FiniteIndex :=
      Subgroup.finiteIndex_iff.mpr (by rw [hV'index]; exact (Fact.out : p.Prime).ne_zero)
    have hV'open : IsOpen ((V.comap (IdeleClassGroup.normClassHom K K') :
        Subgroup (IdeleClassGroup K')) : Set (IdeleClassGroup K')) :=
      NK.NUV2.ArtinBridge.isOpen_comap_normClassHom K K' V hopen
    have hray' := integralIdeles_map_le_comap_normClassHom (K := K) (K' := K') V hray
    -- the Kummer case over `K'`
    obtain ⟨M, hFM, hNM, hAM, hfdM, hgalM, hnormM, hdegM, -, -⟩ :=
      exists_unramified_normClassSubgroup_of_kummer (K := K') hARL hFC p hζ
        (V.comap (IdeleClassGroup.normClassHom K K')) hV'fin hV'open hV'index hray' hgap
    letI : Field M := hFM
    letI : NumberField M := hNM
    letI : Algebra K' M := hAM
    letI : FiniteDimensional K' M := hfdM
    haveI : IsGalois K' M := hgalM
    -- descend to `K`
    obtain ⟨L, hFL, hNL, hAL, hfdL, hgalL, hnormL, hdegL⟩ :=
      exists_galois_normClassSubgroup_eq_of_cyclotomic_descent_deg (K := K) (K' := K')
        hARL hFC hcop hp2 hζ V hidx hnormM hdegM
    letI : Field L := hFL
    letI : NumberField L := hNL
    letI : Algebra K L := hAL
    letI : FiniteDimensional K L := hfdL
    haveI : IsGalois K L := hgalL
    have hrayL : (Idele.integralIdeles K).map (IdeleClassGroup.mk K) ≤
        Idele.normClassSubgroup K L := by
      rw [hnormL]; exact hray
    obtain ⟨hdiffL, hinfL⟩ :=
      isUnramified_of_normClassSubgroup_le_integralIdeles_safe (K := K) (L := L) p hdegL hgap hrayL
    exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance,
      hgalL, hnormL, hdegL, hdiffL, hinfL⟩

end NK.CFTLib.Existence
