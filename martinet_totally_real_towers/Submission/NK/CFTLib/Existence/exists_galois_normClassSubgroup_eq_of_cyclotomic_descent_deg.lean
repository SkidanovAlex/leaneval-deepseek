import Mathlib
import Submission.NK.CFTLib.Existence.exists_intermediateField_normClassSubgroup_eq_of_index_prime
import Submission.NK.NUV2.ArtinBridge.index_eq_card_abelianization_of_fundamentalClassElement
import Submission.NK.GlobalCFT.NormGroup.Basic
import Submission.NK.GlobalCFT.ClassFormation
import Submission.NK.CFTLib.Existence.index_normClassSubgroup_galoisClosure_le
import Submission.NK.GlobalCFTdeep.normClassSubgroup_index_ne_zero

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace NK.CFTLib.Existence

open scoped IsMulCommutative
open NK.GlobalCFT

/-! **The descent step of the existence theorem (Milne, *CFT*, 9.4), degree only.**

Let `K' / K` be a finite abelian (indeed cyclic) extension of number fields of degree `d` with
`p ∤ d` (`p` an odd prime) and `ζ_p ∈ K'`.  Let `M / K'` be Galois of degree `p` whose norm class
subgroup is the pullback `V.comap (N_{K'/K})` of a subgroup `V ≤ C_K` of index `p`.  Then `V` is the
norm class subgroup of a *finite Galois* extension `L / K` of degree `p`.

No unramifiedness is asked for or assumed anywhere (the unramifiedness of `L/K` is a separate
statement, `NK.CFTLib.Existence.isUnramified_of_normClassSubgroup_le_integralIdeles`, which is proved
elsewhere and is used by the caller).  Do NOT route through
`exists_galois_unramified_of_abelian_normClassSubgroup_eq`: it needs unramifiedness of an intermediate
field.  Use the *already proved*
`NK.CFTLib.Existence.exists_intermediateField_normClassSubgroup_eq_of_index_prime` instead (step 6
below).

## Route (Milne 9.4, the "count" variant, avoiding the norm limitation theorem)

Write `d = [K' : K]`.  The sibling variant
`NK.CFTLib.Existence.exists_galois_normClassSubgroup_eq_of_kummer_by_count` is this statement with
an additional unramifiedness conclusion; it is not used here (it needs the conductor theorem
`isUnramified_of_normClassSubgroup_le_integralIdeles`, which is proved elsewhere and is used by the
caller).  The plan of the present route is also recorded in
`Submission/Work/CFTLib/Existence/KummerCountNotes.lean` §3 and
`Submission/Work/CFTLib/Existence/DescentV3Notes.lean`.

1. **The anchor.**  `N_{M/K}C_M = N_{K'/K}(N_{M/K'}C_M) = N_{K'/K}(V.comap N_{K'/K}) = V ⊓ N_{K'/K}C_{K'}`
   (transitivity of the norm, `NK.GlobalCFT.NormGroup.globalCFT_normClassHom_trans`, plus `hM`);
   call this subgroup `W`.  It has index `p·d` in `C_K`: `V ⊔ N_{K'/K}C_{K'} = C_K` because
   `[C_K : V ⊔ N_{K'}]` divides both `[C_K : V] = p` and `[C_K : N_{K'}] = d`, which are coprime
   (`hcop`), and `[C_K : N_{K'/K}C_{K'}] = d` is reciprocity from `hFC`
   (`NK.GlobalCFTdeep.index_eq_finrank_of_isCyclic`, `[K' : K]` cyclic).
2. **The count.**  For the Galois closure `Ω := galoisClosure K M` of `M` over `K`, the Kummer count
   `NK.CFTLib.Existence.index_normClassSubgroup_galoisClosure_le` gives
   `[C_K : N_{Ω/K}C_Ω] ≤ p·d`; with `hFC`
   (`NK.NUV2.ArtinBridge.index_eq_card_abelianization_of_fundamentalClassElement`) one has
   `[C_K : N_{Ω/K}C_Ω] = |Gal(Ω/K)ᵃᵇ|`, while `M ⊆ Ω` gives `N_{Ω/K}C_Ω ≤ W`, so the two indices
   are equal and `N_{Ω/K}C_Ω = W`.
3. **The maximal abelian subextension.**  `G := Gal(Ω/K)` is finite (Ω/K is finite Galois), so its
   commutator subgroup `C := [G,G]` is normal, the fixed field `A := Ω^C` is Galois over `K` with
   ∆commutative Galois group `G/C`, and `[A : K] = |Gᵃᵇ| = p·d`.
4. `N_{A/K}C_A = N_{Ω/K}C_Ω = W`: `⊆` is the tower property (`A ⊆ Ω`), and the two indices agree
   because `[C_K : N_{A/K}C_A] = |Gal(A/K)ᵃᵇ| = [A : K] = p·d` (the Galois group of `A/K` is
   commutative, so the index formula from `hFC` is just the degree).
5. `W ≤ V`: `W = V ⊓ N_{K'/K}C_{K'}`.
6. **The correspondence.**  `exists_intermediateField_normClassSubgroup_eq_of_index_prime` applied to
   the commutative Galois extension `A/K` and the index-`p` subgroup `V ⊇ N_{A/K}C_A` produces an
   intermediate field `L ⊆ A` with `L/K` Galois, `[L : K] = p` and `N_{L/K}C_L = V`. -/

/-- The index of an intersection of subgroups whose indices are a prime `p` and an integer `d` not
divisible by `p`. -/
private theorem index_inf_eq_mul_of_not_dvd {G : Type*} [CommGroup G] {p d : ℕ} [Fact p.Prime]
    {V W : Subgroup G} (hV : V.index = p) (hW : W.index = d) (hcop : ¬ p ∣ d) :
    (V ⊓ W).index = p * d := by
  have hp : p.Prime := Fact.out
  have htop : V ⊔ W = ⊤ := by
    have h1 : (V ⊔ W).index ∣ p := by rw [← hV]; exact Subgroup.index_dvd_of_le le_sup_left
    have h2 : (V ⊔ W).index ∣ d := by rw [← hW]; exact Subgroup.index_dvd_of_le le_sup_right
    rcases hp.eq_one_or_self_of_dvd _ h1 with h | h
    · exact Subgroup.index_eq_one.mp h
    · exact absurd (h ▸ h2) hcop
  have hrel : (V ⊓ W).relIndex V = d := by
    rw [Subgroup.inf_relIndex_left V W]
    have h : W.relIndex (V ⊔ W) = W.relIndex V := Subgroup.relIndex_sup_right V W
    rw [← h, htop, Subgroup.relIndex_top_right, hW]
  have hmul : (V ⊓ W).relIndex V * V.index = (V ⊓ W).index :=
    Subgroup.relIndex_mul_index inf_le_left
  rw [hrel, hV] at hmul
  rw [hmul.symm, mul_comm]

/-- A subgroup of finite index is determined by a subgroup containing it with the same index. -/
private theorem eq_of_le_of_index_eq' {G : Type*} [Group G] {A B : Subgroup G} (h : A ≤ B)
    (hidx : A.index = B.index) (hne : B.index ≠ 0) : A = B := by
  have h1 : A.relIndex B * B.index = B.index := by rw [Subgroup.relIndex_mul_index h, hidx]
  have hrel : A.relIndex B = 1 :=
    Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hne) (by rw [one_mul]; exact h1)
  exact le_antisymm h (Subgroup.relIndex_eq_one.mp hrel)

/-- Commutativity transports along a multiplicative equivalence. -/
private theorem isMulCommutative_of_mulEquiv' {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : IsMulCommutative A) : IsMulCommutative B := by
  haveI := h
  refine IsMulCommutative.of_comm (fun a b => ?_)
  obtain ⟨x, rfl⟩ := e.surjective a
  obtain ⟨y, rfl⟩ := e.surjective b
  rw [← map_mul, ← map_mul, mul_comm']

theorem exists_galois_normClassSubgroup_eq_of_cyclotomic_descent_deg
    (hARL : NK.CFTLib.ArtinReciprocityIdeal) (hFC : NK.GlobalCFTdeep.FundamentalClassElement)
    {K : Type} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
    {K' : Type} [Field K'] [NumberField K'] [Algebra K K'] [FiniteDimensional K K']
    [IsGalois K K'] [IsMulCommutative (K' ≃ₐ[K] K')] [IsCyclic (K' ≃ₐ[K] K')]
    (hcop : ¬ p ∣ Module.finrank K K') (hp2 : p ≠ 2)
    {ζ : K'} (hζ : IsPrimitiveRoot ζ p)
    (V : Subgroup (NK.GlobalCFT.IdeleClassGroup K)) (hidx : V.index = p)
    {M : Type} [Field M] [NumberField M] [Algebra K' M] [FiniteDimensional K' M] [IsGalois K' M]
    (hM : NK.GlobalCFT.Idele.normClassSubgroup K' M =
      V.comap (NK.GlobalCFT.IdeleClassGroup.normClassHom K K'))
    (hMdeg : Module.finrank K' M = p) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (_ : FiniteDimensional K L),
      IsGalois K L ∧ NK.GlobalCFT.Idele.normClassSubgroup K L = V ∧ Module.finrank K L = p := by
  classical
  -- ## the `K`-algebra structure on `M` induced by `K ⊆ K' ⊆ M`
  letI : Algebra K M := ((algebraMap K' M).comp (algebraMap K K')).toAlgebra
  haveI hST : IsScalarTower K K' M := IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI hFDM : FiniteDimensional K M := FiniteDimensional.trans K K' M
  -- ## 1. the norm class subgroup of `K'/K` has index `[K' : K]`, by reciprocity from `hFC`
  have hidxK' : (NK.GlobalCFT.Idele.normClassSubgroup K K').index = Module.finrank K K' :=
    NK.GlobalCFTdeep.index_eq_finrank_of_isCyclic (K := K) (L := K')
  have hcop' : ¬ p ∣ (NK.GlobalCFT.Idele.normClassSubgroup K K').index := by
    rw [hidxK']; exact hcop
  -- ## the anchor `W = V ⊓ N_{K'/K}C_{K'}`
  have hnormM : NK.GlobalCFT.Idele.normClassSubgroup K M =
      V ⊓ NK.GlobalCFT.Idele.normClassSubgroup K K' := by
    have hcomp : NK.GlobalCFT.IdeleClassGroup.normClassHom K M =
        (NK.GlobalCFT.IdeleClassGroup.normClassHom K K').comp
          (NK.GlobalCFT.IdeleClassGroup.normClassHom K' M) :=
      MonoidHom.ext fun q => (NK.GlobalCFT.NormGroup.globalCFT_normClassHom_trans q).symm
    rw [NK.GlobalCFT.Idele.normClassSubgroup_eq_range (K := K) (L := M),
      hcomp, MonoidHom.range_comp,
      ← NK.GlobalCFT.Idele.normClassSubgroup_eq_range (K := K') (L := M), hM,
      Subgroup.map_comap_eq,
      NK.GlobalCFT.Idele.normClassSubgroup_eq_range (K := K) (L := K')]
    exact inf_comm _ _
  have hidxH : (V ⊓ NK.GlobalCFT.Idele.normClassSubgroup K K').index =
      p * Module.finrank K K' :=
    index_inf_eq_mul_of_not_dvd (p := p) (d := Module.finrank K K') hidx hidxK' hcop
  -- ## 2. the Galois closure `Ω := galoisClosure K M` of `M` over `K`
  haveI hFinN : FiniteDimensional K (NK.GlobalCFTdeep.galoisClosure K M) :=
    normalClosure.is_finiteDimensional K M (AlgebraicClosure M)
  haveI hNFN : NumberField (NK.GlobalCFTdeep.galoisClosure K M) :=
    NumberField.of_module_finite K (NK.GlobalCFTdeep.galoisClosure K M)
  haveI hNormN : Normal K (NK.GlobalCFTdeep.galoisClosure K M) :=
    normalClosure.normal K M (AlgebraicClosure M)
  haveI hGalN : IsGalois K (NK.GlobalCFTdeep.galoisClosure K M) :=
    Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  -- ## the Kummer count
  have hcount : (NK.GlobalCFT.Idele.normClassSubgroup K
      (NK.GlobalCFTdeep.galoisClosure K M)).index ≤ p * Module.finrank K K' :=
    index_normClassSubgroup_galoisClosure_le (K := K) (K' := K') (M := M) hFC hζ hMdeg
  have hleNM : NK.GlobalCFT.Idele.normClassSubgroup K (NK.GlobalCFTdeep.galoisClosure K M) ≤
      NK.GlobalCFT.Idele.normClassSubgroup K M :=
    NK.GlobalCFT.Idele.normClassSubgroup_le_of_tower (K := K) (L := M)
      (M := NK.GlobalCFTdeep.galoisClosure K M)
  have hleNH : NK.GlobalCFT.Idele.normClassSubgroup K (NK.GlobalCFTdeep.galoisClosure K M) ≤
      V ⊓ NK.GlobalCFT.Idele.normClassSubgroup K K' := by
    rw [← hnormM]; exact hleNM
  have hge : p * Module.finrank K K' ≤
      (NK.GlobalCFT.Idele.normClassSubgroup K
        (NK.GlobalCFTdeep.galoisClosure K M)).index := by
    haveI : (NK.GlobalCFT.Idele.normClassSubgroup K
        (NK.GlobalCFTdeep.galoisClosure K M)).FiniteIndex :=
      Subgroup.finiteIndex_iff.mpr
        (NK.GlobalCFTdeep.normClassSubgroup_index_ne_zero (K := K)
          (L := NK.GlobalCFTdeep.galoisClosure K M))
    rw [← hidxH]
    exact Subgroup.index_antitone hleNH
  have hidxN : (NK.GlobalCFT.Idele.normClassSubgroup K
      (NK.GlobalCFTdeep.galoisClosure K M)).index = p * Module.finrank K K' :=
    le_antisymm hcount hge
  have hneH : (V ⊓ NK.GlobalCFT.Idele.normClassSubgroup K K').index ≠ 0 := by
    rw [hidxH]
    exact Nat.mul_ne_zero (Fact.out : p.Prime).ne_zero
      (Module.finrank_pos (R := K) (M := K')).ne'
  have hEqNH : NK.GlobalCFT.Idele.normClassSubgroup K (NK.GlobalCFTdeep.galoisClosure K M) =
      V ⊓ NK.GlobalCFT.Idele.normClassSubgroup K K' :=
    eq_of_le_of_index_eq' hleNH (by rw [hidxN, hidxH]) hneH
  -- ## the abelianisation of `Gal(Ω/K)` has order `p · [K' : K]`
  have hcardAb : Nat.card (Abelianization
      (NK.GlobalCFTdeep.galoisClosure K M ≃ₐ[K] (NK.GlobalCFTdeep.galoisClosure K M))) =
      p * Module.finrank K K' := by
    rw [← hidxN, NK.NUV2.ArtinBridge.index_eq_card_abelianization_of_fundamentalClassElement hFC]
  -- ## 3. the commutator subgroup `C := [G,G]` of `G := Gal(Ω/K)` and the fixed field `A := Ω^C`
  set G := NK.GlobalCFTdeep.galoisClosure K M ≃ₐ[K] NK.GlobalCFTdeep.galoisClosure K M
  set C : Subgroup G := ⁅(⊤ : Subgroup G), ⊤⁆ with hC
  haveI hCnorm : C.Normal := Subgroup.commutator_normal ⊤ ⊤
  let A : IntermediateField K (NK.GlobalCFTdeep.galoisClosure K M) :=
    IntermediateField.fixedField C
  have hAgal : IsGalois K ↥A := IsGalois.of_fixedField_normal_subgroup C
  haveI : IsGalois K ↥A := hAgal
  have hquotCard : Nat.card (G ⧸ C) = p * Module.finrank K K' := by
    rw [← Subgroup.index_eq_card C, hC]
    exact hcardAb
  have hcardA : Nat.card (↥A ≃ₐ[K] ↥A) = p * Module.finrank K K' :=
    (Nat.card_congr (IsGalois.normalAutEquivQuotient C).toEquiv).symm.trans hquotCard
  have hAcomm : IsMulCommutative (↥A ≃ₐ[K] ↥A) := by
    haveI hQuot : IsMulCommutative (G ⧸ C) :=
      (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := C)).mpr le_rfl
    exact isMulCommutative_of_mulEquiv' (IsGalois.normalAutEquivQuotient C) hQuot
  haveI : IsMulCommutative (↥A ≃ₐ[K] ↥A) := hAcomm
  have hAdeg : Module.finrank K ↥A = p * Module.finrank K K' := by
    rw [← IsGalois.card_aut_eq_finrank K ↥A]
    exact hcardA
  -- ## 4. `N_{A/K}C_A = N_{Ω/K}C_Ω = W`
  have hidxA : (NK.GlobalCFT.Idele.normClassSubgroup K ↥A).index =
      Nat.card (↥A ≃ₐ[K] ↥A) := by
    rw [NK.NUV2.ArtinBridge.index_eq_card_abelianization_of_fundamentalClassElement hFC
      (K := K) (L := ↥A)]
    exact (Nat.card_congr (Abelianization.equivOfComm (H := (↥A ≃ₐ[K] ↥A))).toEquiv).symm
  have hNA : NK.GlobalCFT.Idele.normClassSubgroup K ↥A =
      NK.GlobalCFT.Idele.normClassSubgroup K (NK.GlobalCFTdeep.galoisClosure K M) := by
    have hle : NK.GlobalCFT.Idele.normClassSubgroup K (NK.GlobalCFTdeep.galoisClosure K M) ≤
        NK.GlobalCFT.Idele.normClassSubgroup K ↥A :=
      NK.GlobalCFT.Idele.normClassSubgroup_le_of_tower (K := K) (L := ↥A)
        (M := NK.GlobalCFTdeep.galoisClosure K M)
    have hidxeq : (NK.GlobalCFT.Idele.normClassSubgroup K
          (NK.GlobalCFTdeep.galoisClosure K M)).index =
        (NK.GlobalCFT.Idele.normClassSubgroup K ↥A).index := by
      rw [hidxN, hidxA, hcardA]
    have hne : (NK.GlobalCFT.Idele.normClassSubgroup K ↥A).index ≠ 0 := by
      rw [hidxA, hcardA]
      exact Nat.mul_ne_zero (Fact.out : p.Prime).ne_zero
        (Module.finrank_pos (R := K) (M := K')).ne'
    exact (eq_of_le_of_index_eq' hle hidxeq hne).symm
  -- ## 5. `N_{A/K}C_A ≤ V`
  have hleV : NK.GlobalCFT.Idele.normClassSubgroup K ↥A ≤ V := by
    rw [hNA]; exact le_trans hleNH inf_le_left
  -- ## 6. the index-`p` correspondence for the commutative Galois extension `A/K`
  obtain ⟨E, hEgal, hEnorm, hEdeg⟩ :=
    exists_intermediateField_normClassSubgroup_eq_of_index_prime hARL hFC (K := K) (L := ↥A)
      V hidx hleV
  exact ⟨↥E, inferInstance, inferInstance, inferInstance, inferInstance, hEgal, hEnorm, hEdeg⟩

end NK.CFTLib.Existence
