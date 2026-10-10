import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.index_kummerE_tIdeles
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.principal_inf_kummerE_eq_tUnitsPow
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.prod_localPow_eq_pow
import Submission.NK.GlobalCFTdeep.SecondInequality.tUnits_index_powSubgroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `[C_K : Kˣ·E_S] = p^{|S|}`

For `K` a number field containing a primitive `p`-th root of unity `ζ`, and `S` a finite set of
places of `K` containing all the archimedean places and all the places above `p`, with
`𝕀_K = Kˣ · 𝕀_{K,S}`, the index in the idèle class group `C_K` of the image of `Kˣ · E_S` is
`p^{|S|}`:

  `[C_K : (Kˣ · E_S)/Kˣ] = [𝕀_K : Kˣ · E_S] = p^{|S|}`,

where `E_S = ∏_{v ∈ S} K_v^{×p} · ∏_{v ∉ S} U_v` (`KummerCase.kummerE p S ∅`).

This is the index count used in the Kummer case of the existence theorem: the numerator
`[𝕀_{K,S} : E_S] = p^{2|S|}` is `index_kummerE_tIdeles` + `prod_localPow_eq_pow`, the denominator
`[U(S) : U(S)^p] = p^{|S|}` is `tUnits_index_powSubgroup`, and Milne's Lemma 6.7
(`principal_inf_kummerE_eq_tUnitsPow`) identifies `Kˣ ∩ E_S = U(S)^p`.  The modular index identity
of `index_sup_kummerE` then divides the two.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

namespace NK.CFTLib.Existence

open NK.GlobalCFT NK.GlobalCFTdeep NK.GlobalCFTdeep.SecondInequality

theorem index_kummerE_sup_principal (K : Type) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (S : Finset (NK.GlobalCFT.Place K))
    (hSinf : ∀ w : NumberField.InfinitePlace K, NK.GlobalCFT.Place.ofInfinite w ∈ S)
    (hSp : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (p : NumberField.RingOfIntegers K) ∈ q.asIdeal → NK.GlobalCFT.Place.ofFinite q ∈ S)
    (hgen : (⊤ : Subgroup (NK.GlobalCFT.Idele K)) =
      NK.GlobalCFT.Idele.principalSubgroup K ⊔ NK.GlobalCFTdeep.TIdeles (S : Set (NK.GlobalCFT.Place K))) :
    (Subgroup.map (NK.GlobalCFT.IdeleClassGroup.mk K)
      (NK.GlobalCFT.Idele.principalSubgroup K ⊔
        NK.GlobalCFTdeep.SecondInequality.KummerCase.kummerE p S ∅)).index = p ^ S.card := by
  classical
  have hp : p.Prime := Fact.out
  -- ### Vocabulary
  let P : Subgroup (Idele K) := Idele.principalSubgroup K
  let E : Subgroup (Idele K) := KummerCase.kummerE (K := K) p S ∅
  let U : Subgroup (Idele K) := TIdeles (S : Set (Place K))
  let θ : Kˣ →* Idele K := Idele.principalIdele K
  let TU : Subgroup Kˣ := TUnits (L := K) (S : Set (Place K))
  let PU : Subgroup Kˣ := Subgroup.map (powMonoidHom p) TU
  -- ### The index of the image under the quotient map `𝕀 K →* C K`
  have hker : (IdeleClassGroup.mk K).ker = P := by
    show (QuotientGroup.mk' (Idele.principalSubgroup K)).ker = Idele.principalSubgroup K
    rw [QuotientGroup.ker_mk']
  have hmap : (Subgroup.map (IdeleClassGroup.mk K) (P ⊔ E)).index = (P ⊔ E).index := by
    rw [Subgroup.index_map, hker,
      MonoidHom.range_eq_top.mpr (IdeleClassGroup.mk_surjective K), Subgroup.index_top, mul_one,
      sup_eq_left.mpr le_sup_left]
  -- ### The numerator `[𝕀_{K,S} : E] = p ^ (2 |S|)`
  have hnum : E.relIndex U = p ^ (2 * S.card) := by
    have h := KummerCase.index_kummerE_tIdeles (K := K) p S (∅ : Finset (Place K))
    rw [Finset.coe_empty, Set.union_empty] at h
    change ((KummerCase.kummerE (K := K) p S ∅).subgroupOf
      (TIdeles (S : Set (Place K)))).index = p ^ (2 * S.card)
    rw [h]
    exact KummerCase.prod_localPow_eq_pow hp hζ S hSinf hSp
  -- ### The denominator `[U(S) : U(S)^p] = p ^ |S|`
  have hden : PU.relIndex TU = p ^ S.card := by
    have hinf : ∀ w : Place K, w.IsInfinite → w ∈ S := by
      intro w hw
      obtain ⟨w', rfl⟩ := Place.isInfinite_iff.mp hw
      exact hSinf w'
    have h := tUnits_index_powSubgroup (K := K) p hp hζ S hinf
    change ((Subgroup.map (powMonoidHom p) (TUnits (L := K) (S : Set (Place K)))).subgroupOf
      (TUnits (L := K) (S : Set (Place K)))).index = p ^ S.card
    rw [h]
    simp
  -- ### Milne 6.7: `Kˣ ∩ E = U(S)^p`
  have hinter : P ⊓ E = Subgroup.map θ PU := by
    have h := KummerCase.principal_inf_kummerE_eq_tUnitsPow (K := K) hp hζ S hSinf hSp hgen
      (∅ : Finset (HeightOneSpectrum (𝓞 K)))
      (fun q hq => by simp at hq)
      (fun x _ => ⟨1, fun q hq => by simp at hq⟩)
    rw [Finset.map_empty, Finset.coe_empty, Set.union_empty] at h
    exact h
  -- ### `E ≤ U` and `P ⊔ U = ⊤`
  have hEU : E ≤ U := by
    intro x hx
    have hx' := KummerCase.mem_kummerE.mp hx
    rw [mem_TIdeles]
    intro v hv
    exact hx'.2 v (by simpa using hv) (by simp)
  have hUP : P ⊔ U = ⊤ := hgen.symm
  have htop : (P ⊔ E) ⊔ U = ⊤ := by
    rw [sup_assoc, sup_eq_right.mpr hEU, hUP]
  -- ### `P ⊓ U = θ(U(S))`
  have hθinj : Function.Injective θ := NK.GlobalCFT.Ideles.globalCFT_principalIdele_injective
  have hM : P ⊓ U = Subgroup.map θ TU := (Subgroup.map_comap_eq θ U).symm
  have hPU_le_TU : PU ≤ TU := by
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact Subgroup.pow_mem TU hy p
  have hPUsub : Subgroup.map θ PU ≤ U :=
    (Subgroup.map_mono hPU_le_TU).trans ((le_of_eq hM.symm).trans inf_le_right)
  have hEinfM : E ⊓ (P ⊓ U) = Subgroup.map θ PU := by
    rw [← inf_assoc, inf_comm E P, hinter, inf_of_le_left hPUsub]
  -- ### The modular index identity
  have hmod : (E ⊔ (P ⊓ U)).relIndex U * (E ⊓ (P ⊓ U)).relIndex (P ⊓ U) = E.relIndex U := by
    have hPU_le_U : P ⊓ U ≤ U := inf_le_right
    have key2 : E.relIndex (E ⊔ (P ⊓ U)) = (E ⊓ (P ⊓ U)).relIndex (P ⊓ U) := by
      rw [Subgroup.relIndex_sup_left, Subgroup.inf_relIndex_right]
    calc (E ⊔ (P ⊓ U)).relIndex U * (E ⊓ (P ⊓ U)).relIndex (P ⊓ U)
        = (E ⊔ (P ⊓ U)).relIndex U * E.relIndex (E ⊔ (P ⊓ U)) := by rw [key2]
      _ = E.relIndex (E ⊔ (P ⊓ U)) * (E ⊔ (P ⊓ U)).relIndex U := by rw [mul_comm]
      _ = E.relIndex U :=
          Subgroup.relIndex_mul_relIndex E (E ⊔ (P ⊓ U)) U le_sup_left (sup_le hEU hPU_le_U)
  rw [hEinfM, hM] at hmod
  rw [Subgroup.relIndex_map_map_of_injective (f := θ) PU TU hθinj] at hmod
  rw [hden, hnum] at hmod
  have harith : p ^ (2 * S.card) = p ^ S.card * p ^ S.card := by
    rw [show 2 * S.card = S.card + S.card by ring, pow_add]
  have hX : (E ⊔ Subgroup.map θ TU).relIndex U = p ^ S.card := by
    rw [harith] at hmod
    exact Nat.mul_right_cancel (pow_pos hp.pos S.card) hmod
  -- ### Assemble
  have hidx : (P ⊔ E).index = (P ⊔ E).relIndex U := by
    rw [← Subgroup.relIndex_top_right (H := P ⊔ E), ← htop, Subgroup.relIndex_sup_left]
  have hrelU : (P ⊔ E).relIndex U = (E ⊔ (P ⊓ U)).relIndex U := by
    rw [← Subgroup.inf_relIndex_right (H := P ⊔ E) (K := U)]
    congr 1
    rw [sup_comm P E, sup_inf_assoc_of_le P hEU]
  have hmain : (P ⊔ E).index = p ^ S.card := by
    rw [hidx, hrelU, hM]
    exact hX
  calc (Subgroup.map (IdeleClassGroup.mk K) (P ⊔ E)).index = (P ⊔ E).index := hmap
    _ = p ^ S.card := hmain

end NK.CFTLib.Existence
