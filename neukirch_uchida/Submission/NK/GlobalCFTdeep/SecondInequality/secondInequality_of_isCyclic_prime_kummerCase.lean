import Mathlib
import Submission.NK.GlobalCFTdeep.SecondInequality.finrank_kummerAdjoin
import Submission.NK.GlobalCFTdeep.SecondInequality.frobeniusGenerateTop_of_notMem
import Submission.NK.GlobalCFTdeep.SecondInequality.pow_mem_normGroup_adicCompletion
import Submission.NK.GlobalCFTdeep.SecondInequality.finrank_eq_one_of_le_normImage
import Submission.NK.GlobalCFTdeep.SecondInequality.index_sup_mul_index_inf
import Submission.NK.GlobalCFTdeep.Herbrand.CyclicHerbrandQuotient
import Submission.NK.GlobalCFTdeep.Herbrand.finrank_tUnits
import Submission.NK.GlobalCFTdeep.Herbrand.top_eq_principal_sup_TIdeles
import Submission.NK.LocalReciprocity.index_normGroup_eq_finrank
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.Defs
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.exists_goodS
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.exists_kummerT_core
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.index_kummerE_tIdeles
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.index_sup_kummerE
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.prod_localPow_eq_pow
import Submission.NK.GlobalCFTdeep.SecondInequality.tUnits_index_powSubgroup

/-!
# The Kummer case of the second inequality (Milne, *Class Field Theory*, VII §6)

For `L/K` cyclic of prime degree `p` with `ζ_p ∈ K` we prove
`[C_K : N_{L/K} C_L] ≤ [L : K] = p`.

The proof is the assembly of Milne's chapter VII §6, with the mathematical content in the
files of `Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase`:

* `exists_goodS` — the choice of the finite set `S` of places (Milne's conditions (a)–(d));
* `exists_kummerT_core` — the choice of the Frobenius basis `T` together with Milne 6.2, 6.4, 6.7;
* `index_kummerE_tIdeles` — the index of Milne's subgroup `E` inside `𝕀_{K,S∪T}` (Milne 6.6);
* `prod_localPow_eq_pow` — the local computation `∏_{v∈S}[K_vˣ : K_v^{×p}] = p^{2|S|}` (Milne 6.6
  and 6.8, using the product formula);
* `index_sup_kummerE` — the final index computation `[𝕀_K : Kˣ·E] = p` (Milne 6.5–6.7).
-/

open scoped NumberField RestrictedProduct IsMulCommutative
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep.SecondInequality

open NK.GlobalCFT

/-- In the Kummer case there is a Kummer generator: `L = K(α)` with `α ^ p = a ∈ K^×`.

This is Mathlib's `exists_root_adjoin_eq_top_of_isCyclic` (`FieldTheory.KummerExtension`), with
`a ≠ 0` extracted from the fact that `[L : K] = p > 1`. -/
theorem kummerGenerator_exists {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    {p : ℕ} (hp : p.Prime) (hcard : Nat.card (L ≃ₐ[K] L) = p) {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    ∃ (a : K) (_ha : a ≠ 0) (α : L), α ^ p = algebraMap K L a ∧
      IntermediateField.adjoin K {α} = ⊤ := by
  have hq : Module.finrank K L = p := by rw [← IsGalois.card_aut_eq_finrank K L, hcard]
  obtain ⟨α, hα, hadj⟩ := exists_root_adjoin_eq_top_of_isCyclic K L
    (hK := ⟨ζ, by rw [hq]; exact (mem_primitiveRoots hp.pos).mpr hζ⟩)
  rw [hq] at hα
  obtain ⟨a, ha'⟩ := hα
  have ha0 : a ≠ 0 := by
    intro h0
    have hα0 : α = 0 := by
      have h : α ^ p = 0 := by rw [← ha', h0, map_zero]
      exact (pow_eq_zero_iff hp.ne_zero).mp h
    have hbot : Module.finrank K ↥(⊥ : IntermediateField K L) = 1 :=
      IntermediateField.finrank_bot
    have htop : Module.finrank K ↥(⊤ : IntermediateField K L) = Module.finrank K L :=
      (IntermediateField.topEquiv (F := K) (E := L)).toLinearEquiv.finrank_eq
    have h : (⊥ : IntermediateField K L) = ⊤ := by
      rw [← hadj, hα0]
      simp
    rw [h] at hbot
    have hfin1 : Module.finrank K L = 1 := by rw [← htop, hbot]
    exact absurd (hq ▸ hfin1 : p = 1) hp.ne_one
  exact ⟨a, ha0, α, ha'.symm, hadj⟩

/-- The index of the norm class subgroup equals the index of `Kˣ·N 𝕀_L` inside `𝕀_K`. -/
theorem index_normClassSubgroup_eq_index_sup_normImage {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] :
    (Idele.normClassSubgroup K L).index =
      (Idele.principalSubgroup K ⊔ Idele.normImage K L).index := by
  rw [show Idele.normClassSubgroup K L =
      (Idele.normImage K L).map (IdeleClassGroup.mk K) from rfl]
  rw [Subgroup.index_map]
  rw [show (IdeleClassGroup.mk K).ker = Idele.principalSubgroup K from QuotientGroup.ker_mk' _]
  rw [show (IdeleClassGroup.mk K).range = ⊤ from
    MonoidHom.range_eq_top.mpr (IdeleClassGroup.mk_surjective K)]
  rw [Subgroup.index_top, mul_one, sup_comm]

/-- **The second inequality of global class field theory in the Kummer case**: for `L/K` cyclic of
prime degree `p` with `μ_p ⊆ K` (witnessed by `ζ`), `[C_K : N_{L/K}C_L] ≤ [L : K] = p`.

This is Milne, *Class Field Theory*, Chapter VII §6. -/
theorem secondInequality_of_isCyclic_prime_kummerCase {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)] {p : ℕ} (hp : p.Prime) (hcard : Nat.card (L ≃ₐ[K] L) = p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    (NK.GlobalCFT.Idele.normClassSubgroup K L).index ≤ Module.finrank K L := by
  have hq : Module.finrank K L = p := by rw [← IsGalois.card_aut_eq_finrank K L, hcard]
  obtain ⟨a, ha, α, hα, hadj⟩ := kummerGenerator_exists hp hcard hζ
  obtain ⟨S, hSinf, hSp, hSram, haS, hSgen⟩ := KummerCase.exists_goodS (K := K) (L := L) hp ha
  obtain ⟨T, hTS, hTcard, hTsplit, hTnorm, hTinter⟩ :=
    KummerCase.exists_kummerT_core (K := K) (L := L) hp hcard hζ ha hα hadj S hSinf hSp hSram haS hSgen
  classical
  set Sp : Finset (Place K) := T.map (KummerCase.placeOfFiniteEmb K) with hSpdef
  have hSpcard : Sp.card = T.card := by rw [hSpdef]; simp
  have hST : S.card = Sp.card + 1 := by rw [hSpcard]; omega
  -- disjointness of `S` and `Sp`
  have hdisj : Disjoint S Sp := by
    rw [hSpdef]
    refine Finset.disjoint_left.mpr fun v hvS hvT => ?_
    obtain ⟨q, hqT, rfl⟩ := Finset.mem_map.mp hvT
    exact hTS q hqT hvS
  have hcard_union : (S ∪ Sp).card = S.card + Sp.card := Finset.card_union_of_disjoint hdisj
  -- the numerator: `[𝕀_{S∪T} : E] = p ^ (2|S|)`
  have hnum : ((KummerCase.kummerE (K := K) p S Sp).subgroupOf
      (TIdeles ((S : Set (Place K)) ∪ (Sp : Set (Place K))))).index = p ^ (2 * S.card) := by
    rw [show (Sp : Set (Place K)) = (T.map (KummerCase.placeOfFiniteEmb K) : Finset (Place K)) from by
      rw [hSpdef]]
    rw [KummerCase.index_kummerE_tIdeles p S Sp]
    exact KummerCase.prod_localPow_eq_pow hp hζ S hSinf hSp
  -- the denominator: `[U(S∪T) : U(S∪T)^p] = p ^ (2|S| - 1)`
  have hden : ((Subgroup.map (powMonoidHom p)
        (TUnits (L := K) ((S : Set (Place K)) ∪ (Sp : Set (Place K))))).subgroupOf
      (TUnits (L := K) ((S : Set (Place K)) ∪ (Sp : Set (Place K))))).index
      = p ^ (2 * S.card - 1) := by
    have hinf' : ∀ w : Place K, w.IsInfinite → w ∈ S ∪ Sp := by
      intro w hw
      obtain ⟨w', rfl⟩ := Place.isInfinite_iff.mp hw
      exact Finset.mem_union_left _ (hSinf w')
    have h := tUnits_index_powSubgroup (K := K) p hp hζ (S ∪ Sp) hinf'
    rw [Finset.coe_union] at h
    have hnat : Nat.card (↥(S ∪ Sp : Finset (Place K))) = 2 * S.card - 1 := by
      rw [show Nat.card (↥(S ∪ Sp : Finset (Place K))) = (S ∪ Sp).card from by
            rw [Nat.card_eq_fintype_card, Fintype.card_coe],
        hcard_union, hSpcard]
      omega
    rw [h, hnat]
  -- the identification `Kˣ ∩ E = U(S∪T)^p` (Milne 6.7)
  have hinter : Idele.principalSubgroup K ⊓ KummerCase.kummerE (K := K) p S Sp =
      KummerCase.tUnitsPowIdele (K := K) p ((S : Set (Place K)) ∪ (Sp : Set (Place K))) := by
    rw [show (Sp : Set (Place K)) = (T.map (KummerCase.placeOfFiniteEmb K) : Finset (Place K)) from by
      rw [hSpdef]]
    exact hTinter
  -- the final index computation
  have hfinal : (Idele.principalSubgroup K ⊔ KummerCase.kummerE (K := K) p S Sp).index = p :=
    KummerCase.index_sup_kummerE hp S Sp hST hnum hden hinter hSgen
  -- the norm class subgroup sits inside `Kˣ · E`
  have hle : Idele.principalSubgroup K ⊔ KummerCase.kummerE (K := K) p S Sp ≤
      Idele.principalSubgroup K ⊔ Idele.normImage K L :=
    sup_le_sup_left hTnorm _
  have hfin : (Idele.principalSubgroup K ⊔ KummerCase.kummerE (K := K) p S Sp).FiniteIndex := by
    rw [Subgroup.finiteIndex_iff, hfinal]
    exact hp.ne_zero
  calc (Idele.normClassSubgroup K L).index
      = (Idele.principalSubgroup K ⊔ Idele.normImage K L).index :=
        index_normClassSubgroup_eq_index_sup_normImage
    _ ≤ (Idele.principalSubgroup K ⊔ KummerCase.kummerE (K := K) p S Sp).index :=
        Subgroup.index_antitone hle
    _ = p := hfinal
    _ = Module.finrank K L := hq.symm

end NK.GlobalCFTdeep.SecondInequality
