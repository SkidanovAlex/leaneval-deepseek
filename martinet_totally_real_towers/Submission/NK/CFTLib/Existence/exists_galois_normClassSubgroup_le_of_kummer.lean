import Mathlib
import Submission.NK.CFTLib.ArtinIdeal
import Submission.NK.CFTLib.Existence.index_kummerE_sup_principal
import Submission.NK.NUV2.ArtinBridge.exists_kummerField_kummerE_le_normImage
import Submission.NK.GlobalCFT.ClassFormation
import Submission.NK.GlobalCFTdeep.FundamentalClassReduction
import Submission.NK.NUV2.ArtinBridge.kummerE_le_of_open_le
import Submission.NK.NUV2.ArtinBridge.exists_finset_forall_localUnits_imp_mem
import Submission.NK.GlobalCFTdeep.Herbrand.top_eq_principal_sup_TIdeles
import Submission.NK.GlobalCFTdeep.SecondInequality.exists_finset_place_idealClassMap
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.Defs
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.exists_goodS
import Submission.NK.GlobalCFT.NormGroup.Basic
import Submission.NK.GlobalCFTdeep.Herbrand.SIdeles

/-!
# The key case of the existence theorem (Milne, *CFT*, 9.3)

Over a number field `K` containing a primitive `p`-th root of unity, every open finite-index
subgroup `V ≤ C_K` of index `p` contains the norm class subgroup `N_{L/K}C_L` of a finite abelian
extension `L/K`.

The proof is Milne's: choose a finite set `S` of places containing the archimedean places, the
places above `p`, the places witnessing the openness of the given subgroup, and enough places to
generate the class group; take `L = K(U(S)^{1/p})`, the Kummer field of the `S`-units.  Then
`[L : K] = p^{|S|}`, the abelian index formula gives `[C_K : N_{L/K}C_L] = [L : K] = p^{|S|}`,
the idèlic index computation gives `[C_K : Kˣ·E_S/Kˣ] = p^{|S|}` as well, and Milne's local
input `E_S ≤ N_{L/K}𝕀_L` forces the two index-`p^{|S|}` subgroups to coincide.  Since
`E_S ≤ U` (the preimage of the given subgroup `V`) the norm group is contained in `V`.

## Provenance of the two inputs

This is the proof of `NK.NUV2.ArtinBridge.kummerKeyCase`, with its single use of the
*unconditional* abelian norm index theorem `NK.CFTLib.Existence.index_eq_finrank_of_isAbelian`
(which is `sorry`-tainted through `…fundamentalClassElement_of_arl`) replaced by the
*conditional* form

`NK.GlobalCFT.index_normClassSubgroup_eq_finrank
   (NK.GlobalCFTdeep.artinReciprocity_of_fundamentalClassElement hFC)`,

i.e. the reciprocity isomorphism supplied by the hypothesis `hFC`.  The hypothesis `hARL`
(Lang's ideal-theoretic reciprocity law) is carried but not needed: `hFC` alone produces the
Artin reciprocity isomorphism.

Everything else used here is sorry-free: the congruence subgroups
(`NK.NUV2.ArtinBridge.exists_finset_forall_localUnits_imp_mem`), the places generating the class
group (`…exists_finset_place_idealClassMap`), the places above `p`
(`…KummerCase.finite_setOf_prime_mem_ringOfIntegers`), `𝕀_K = Kˣ·𝕀_{K,S}`
(`NK.GlobalCFTdeep.Herbrand.top_eq_principal_sup_TIdeles`), the Kummer field and Milne's local
input (`NK.NUV2.ArtinBridge.exists_kummerField_kummerE_le_normImage`), the idèlic index count
(`NK.CFTLib.Existence.index_kummerE_sup_principal`,
`NK.NUV2.ArtinBridge.kummerE_le_of_open_le`) and the elementary group-theoretic step
`subgroup_eq_of_le_of_index_eq` (proved below).

Note that no hypothesis `integralIdeles ≤ V` is needed: the power condition `𝕀_K^p ≤ U` follows
from `V.index = p` alone.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct IsMulCommutative
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.Existence

open NK.GlobalCFT

/-- **A subgroup with the same index as a containing subgroup is equal to it.**  If `H ≤ K` and
`[G : H] = [G : K] ≠ 0`, then `H = K`. -/
private theorem subgroup_eq_of_le_of_index_eq {G : Type*} [Group G] {H K : Subgroup G} (h : H ≤ K)
    (hidx : H.index = K.index) (hne : H.index ≠ 0) : H = K := by
  have hrel : H.relIndex K = 1 := by
    have hmul := Subgroup.relIndex_mul_index h
    rw [hidx] at hmul
    have hKpos : 0 < K.index := by rw [← hidx]; exact Nat.pos_of_ne_zero hne
    exact Nat.eq_of_mul_eq_mul_right hKpos (by rw [hmul, one_mul])
  have htop : H.subgroupOf K = ⊤ := by
    rw [← Subgroup.index_eq_one, ← Subgroup.relIndex]
    exact hrel
  exact le_antisymm h (Subgroup.subgroupOf_eq_top.mp htop)

theorem exists_galois_normClassSubgroup_le_of_kummer
    (hARL : NK.CFTLib.ArtinReciprocityIdeal) (hFC : NK.GlobalCFTdeep.FundamentalClassElement)
    {K : Type} [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p)
    (V : Subgroup (NK.GlobalCFT.IdeleClassGroup K)) (hV : V.FiniteIndex)
    (hopen : IsOpen (V : Set (NK.GlobalCFT.IdeleClassGroup K))) (hidx : V.index = p) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (_ : FiniteDimensional K L),
      IsGalois K L ∧ IsMulCommutative (L ≃ₐ[K] L) ∧
        NK.GlobalCFT.Idele.normClassSubgroup K L ≤ V := by
  classical
  have hp : p.Prime := Fact.out (p := p.Prime)
  -- ### the preimage `U` of `V` in the idèle group
  let U : Subgroup 𝕀[K] := V.comap (IdeleClassGroup.mk K)
  have hUmk : Subgroup.map (IdeleClassGroup.mk K) U = V :=
    Subgroup.map_comap_eq_self (fun x _ => IdeleClassGroup.mk_surjective K x)
  have hUopen : IsOpen (U : Set 𝕀[K]) := by
    have hcont : Continuous (IdeleClassGroup.mk K) := QuotientGroup.continuous_mk
    exact hopen.preimage hcont
  -- ### a finite set of places giving a congruence subgroup inside `U`
  obtain ⟨F₀, hF₀⟩ := NK.NUV2.ArtinBridge.exists_finset_forall_localUnits_imp_mem (K := K) U hUopen
  -- ### a finite set of places whose idèles generate the class group
  obtain ⟨S₁, hS₁inf, hS₁gen⟩ :=
    NK.GlobalCFTdeep.SecondInequality.exists_finset_place_idealClassMap (K := K)
  -- ### the places above `p`
  have hBfin : {q : HeightOneSpectrum (𝓞 K) | (p : 𝓞 K) ∈ q.asIdeal}.Finite :=
    NK.GlobalCFTdeep.SecondInequality.KummerCase.finite_setOf_prime_mem_ringOfIntegers (K := K) hp
  let B : Finset (Place K) := hBfin.toFinset.image Place.ofFinite
  let S : Finset (Place K) := F₀ ∪ S₁ ∪ B
  have hF₀S : F₀ ⊆ S := fun x hx => Finset.mem_union_left _ (Finset.mem_union_left _ hx)
  have hSinf : ∀ w : InfinitePlace K, Place.ofInfinite w ∈ S := fun w =>
    Finset.mem_union_left B
      (Finset.mem_union_right F₀ (hS₁inf (Place.ofInfinite w) (Place.isInfinite_ofInfinite w)))
  have hS₀S : S₁ ⊆ S := fun x hx => Finset.mem_union_left _ (Finset.mem_union_right _ hx)
  have hSp : ∀ q : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ q.asIdeal → Place.ofFinite q ∈ S :=
    fun q hq => Finset.mem_union_right (F₀ ∪ S₁)
      (Finset.mem_image_of_mem _ (hBfin.mem_toFinset.mpr hq))
  -- ### `𝕀_K = Kˣ · 𝕀_{K,S}`
  have hSgen : (⊤ : Subgroup 𝕀[K]) =
      NK.GlobalCFT.Idele.principalSubgroup K ⊔ NK.GlobalCFTdeep.TIdeles (S : Set (Place K)) :=
    NK.GlobalCFTdeep.Herbrand.top_eq_principal_sup_TIdeles (S : Set (Place K)) (by
      intro c
      obtain ⟨u, hu, huc⟩ := hS₁gen c
      exact ⟨u, NK.GlobalCFTdeep.SecondInequality.TIdeles_mono hS₀S hu, huc⟩)
  -- ### the Kummer field of the `S`-units, and Milne's local input
  obtain ⟨L, hFL, hNL, hAL, hfdL, hGalL, hcommL, hfrL, hLE⟩ :=
    NK.NUV2.ArtinBridge.exists_kummerField_kummerE_le_normImage (K := K) hp hζ S hSinf hSp
  refine ⟨L, hFL, hNL, hAL, hfdL, hGalL, hcommL, ?_⟩
  letI : Field L := hFL
  letI : NumberField L := hNL
  letI : Algebra K L := hAL
  letI : FiniteDimensional K L := hfdL
  letI : IsGalois K L := hGalL
  letI : IsMulCommutative (L ≃ₐ[K] L) := hcommL
  -- ### `𝕀_K^p ≤ U`
  have hpow : ∀ x : 𝕀[K], x ^ p ∈ U := by
    intro x
    show IdeleClassGroup.mk K (x ^ p) ∈ V
    have hm : IdeleClassGroup.mk K (x ^ p) = (IdeleClassGroup.mk K x) ^ p := map_pow _ x p
    rw [hm]
    have := Subgroup.pow_index_mem V (IdeleClassGroup.mk K x)
    rwa [hidx] at this
  -- ### `E_S ≤ U`
  have hE : NK.GlobalCFTdeep.SecondInequality.KummerCase.kummerE (K := K) p S ∅ ≤ U :=
    NK.NUV2.ArtinBridge.kummerE_le_of_open_le S F₀ U hF₀ hF₀S hpow
  -- ### the principal idèles are in `U`
  have hP : NK.GlobalCFT.Idele.principalSubgroup K ≤ U := by
    intro x hx
    show IdeleClassGroup.mk K x ∈ V
    have hker : (IdeleClassGroup.mk K).ker = NK.GlobalCFT.Idele.principalSubgroup K := by
      show (QuotientGroup.mk' (NK.GlobalCFT.Idele.principalSubgroup K)).ker =
        NK.GlobalCFT.Idele.principalSubgroup K
      rw [QuotientGroup.ker_mk']
    have hx1 : IdeleClassGroup.mk K x = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      exact hx
    rw [hx1]
    exact V.one_mem
  -- ### `Kˣ · E_S ≤ V`
  have hSBV : Subgroup.map (IdeleClassGroup.mk K)
      (NK.GlobalCFT.Idele.principalSubgroup K ⊔
        NK.GlobalCFTdeep.SecondInequality.KummerCase.kummerE (K := K) p S ∅) ≤ V := by
    rw [← hUmk]
    exact Subgroup.map_mono (sup_le hP hE)
  -- ### `Kˣ · E_S ≤ N_{L/K} C_L`
  have hSBN : Subgroup.map (IdeleClassGroup.mk K)
      (NK.GlobalCFT.Idele.principalSubgroup K ⊔
        NK.GlobalCFTdeep.SecondInequality.KummerCase.kummerE (K := K) p S ∅) ≤
      NK.GlobalCFT.Idele.normClassSubgroup K L := by
    rw [NK.GlobalCFT.Idele.normClassSubgroup]
    rw [Subgroup.map_le_iff_le_comap]
    intro x hx
    obtain ⟨a, ha, e, he, rfl⟩ := Subgroup.mem_sup.mp hx
    have hker : (IdeleClassGroup.mk K).ker = NK.GlobalCFT.Idele.principalSubgroup K := by
      show (QuotientGroup.mk' (NK.GlobalCFT.Idele.principalSubgroup K)).ker =
        NK.GlobalCFT.Idele.principalSubgroup K
      rw [QuotientGroup.ker_mk']
    have ha1 : IdeleClassGroup.mk K a = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      exact ha
    change IdeleClassGroup.mk K (a * e) ∈ Subgroup.map (IdeleClassGroup.mk K)
      (NK.GlobalCFT.Idele.normImage K L)
    rw [map_mul, ha1, one_mul]
    exact Subgroup.mem_map_of_mem _ (hLE he)
  -- ### the two index computations
  have hidxE : (Subgroup.map (IdeleClassGroup.mk K)
      (NK.GlobalCFT.Idele.principalSubgroup K ⊔
        NK.GlobalCFTdeep.SecondInequality.KummerCase.kummerE (K := K) p S ∅)).index =
      p ^ S.card :=
    NK.CFTLib.Existence.index_kummerE_sup_principal K p hζ S hSinf hSp hSgen
  -- the abelian norm index theorem, in its *conditional* form: it is
  -- `index_normClassSubgroup_eq_finrank` composed with the reciprocity law produced by `hFC`.
  have hidxN : (NK.GlobalCFT.Idele.normClassSubgroup K L).index = p ^ S.card := by
    rw [NK.GlobalCFT.index_normClassSubgroup_eq_finrank
      (NK.GlobalCFTdeep.artinReciprocity_of_fundamentalClassElement hFC (K := K) (L := L)), hfrL]
  -- ### equality of the two index-`p^{|S|}` subgroups
  have heq : NK.GlobalCFT.Idele.normClassSubgroup K L =
      Subgroup.map (IdeleClassGroup.mk K)
        (NK.GlobalCFT.Idele.principalSubgroup K ⊔
          NK.GlobalCFTdeep.SecondInequality.KummerCase.kummerE (K := K) p S ∅) :=
    (subgroup_eq_of_le_of_index_eq hSBN (by rw [hidxE, hidxN])
      (by rw [hidxE]; exact pow_ne_zero _ hp.ne_zero)).symm
  rw [heq]
  exact hSBV

end NK.CFTLib.Existence
