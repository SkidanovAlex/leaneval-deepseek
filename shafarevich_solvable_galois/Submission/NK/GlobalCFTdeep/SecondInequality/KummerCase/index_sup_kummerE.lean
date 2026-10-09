import Mathlib
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.Defs
import Submission.NK.GlobalCFTdeep.SecondInequality.index_sup_mul_index_inf
import Submission.NK.GlobalCFT.Ideles.globalCFT_principalIdele_injective
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.GlobalCFTdeep.SecondInequality.KummerCase

open NK.GlobalCFT

theorem index_sup_kummerE {K : Type} [Field K] [NumberField K] {p : ℕ} (hp : p.Prime)
    (S T : Finset (NK.GlobalCFT.Place K)) (hST : S.card = T.card + 1)
    (hnum : ((KummerCase.kummerE (K := K) p S T).subgroupOf (NK.GlobalCFTdeep.TIdeles ((S : Set (NK.GlobalCFT.Place K)) ∪ (T : Set (NK.GlobalCFT.Place K))))).index = p ^ (2 * S.card))
    (hden : ((Subgroup.map (powMonoidHom p) (NK.GlobalCFTdeep.TUnits (L := K) ((S : Set (NK.GlobalCFT.Place K)) ∪ (T : Set (NK.GlobalCFT.Place K))))).subgroupOf
      (NK.GlobalCFTdeep.TUnits (L := K) ((S : Set (NK.GlobalCFT.Place K)) ∪ (T : Set (NK.GlobalCFT.Place K))))).index = p ^ (2 * S.card - 1))
    (hinter : NK.GlobalCFT.Idele.principalSubgroup K ⊓ KummerCase.kummerE (K := K) p S T = KummerCase.tUnitsPowIdele (K := K) p ((S : Set (NK.GlobalCFT.Place K)) ∪ (T : Set (NK.GlobalCFT.Place K))))
    (hSgen : (⊤ : Subgroup (NK.GlobalCFT.Idele K)) = NK.GlobalCFT.Idele.principalSubgroup K ⊔ NK.GlobalCFTdeep.TIdeles (S : Set (NK.GlobalCFT.Place K))) :
    (NK.GlobalCFT.Idele.principalSubgroup K ⊔ KummerCase.kummerE (K := K) p S T).index = p := by
  classical
  -- ### Vocabulary
  -- `Tset` is the place set `S ∪ T`, `E` Milne's subgroup, `U` the `(S∪T)`-idèles,
  -- `P` the principal idèles, `TU` the `(S∪T)`-units.
  let Tset : Set (NK.GlobalCFT.Place K) :=
    (S : Set (NK.GlobalCFT.Place K)) ∪ (T : Set (NK.GlobalCFT.Place K))
  let E : Subgroup (NK.GlobalCFT.Idele K) := kummerE (K := K) p S T
  let U : Subgroup (NK.GlobalCFT.Idele K) := TIdeles Tset
  let P : Subgroup (NK.GlobalCFT.Idele K) := Idele.principalSubgroup K
  let θ : Kˣ →* NK.GlobalCFT.Idele K := Idele.principalIdele K
  let TU : Subgroup Kˣ := TUnits (L := K) Tset
  let PU : Subgroup Kˣ := Subgroup.map (powMonoidHom p) TU
  have hnum' : E.relIndex U = p ^ (2 * S.card) := hnum
  have hden' : PU.relIndex TU = p ^ (2 * S.card - 1) := hden
  have hinter' : P ⊓ E = Subgroup.map θ PU := hinter
  have hSgen' : (⊤ : Subgroup (NK.GlobalCFT.Idele K)) = P ⊔ TIdeles (S : Set (NK.GlobalCFT.Place K)) :=
    hSgen
  -- ### `E ≤ U`
  have hEU : E ≤ U := by
    intro x hx
    have hx' := mem_kummerE.mp hx
    show ∀ w : NK.GlobalCFT.Place K, w ∉ Tset → x w ∈ Place.localUnits K w
    intro w hw
    rw [Set.mem_union, not_or] at hw
    exact hx'.2 w (by simpa using hw.1) (by simpa using hw.2)
  -- ### `P ⊔ U = ⊤`, from the hypothesis `⊤ = P ⊔ 𝕀_{K,S}` and `𝕀_{K,S} ≤ 𝕀_{K,S∪T}`
  have hSS : TIdeles (S : Set (NK.GlobalCFT.Place K)) ≤ U := by
    intro x hx
    show ∀ w : NK.GlobalCFT.Place K, w ∉ Tset → x w ∈ Place.localUnits K w
    intro w hw
    exact hx w (fun h => hw (Or.inl h))
  have hUP : P ⊔ U = ⊤ := by
    refine le_antisymm le_top ?_
    rw [hSgen']
    exact sup_le le_sup_left (hSS.trans le_sup_right)
  have htop : (P ⊔ E) ⊔ U = ⊤ := by
    rw [sup_assoc, sup_eq_right.mpr hEU, hUP]
  -- ### The two descriptions of `P ⊓ U` and `E ⊓ (P ⊓ U)`
  have hθinj : Function.Injective θ :=
    NK.GlobalCFT.Ideles.globalCFT_principalIdele_injective
  have hM : P ⊓ U = Subgroup.map θ TU :=
    (Subgroup.map_comap_eq θ (TIdeles Tset)).symm
  have hPU_le_TU : PU ≤ TU := by
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact Subgroup.pow_mem TU hy p
  have hPUsub : Subgroup.map θ PU ≤ U :=
    (Subgroup.map_mono hPU_le_TU).trans ((le_of_eq hM.symm).trans inf_le_right)
  have hEinfM : E ⊓ (P ⊓ U) = Subgroup.map θ PU := by
    show E ⊓ (P ⊓ U) = Subgroup.map θ PU
    rw [← inf_assoc, inf_comm E P, hinter', inf_of_le_left hPUsub]
  -- ### The modular index identity, in relative-index form
  have hmod : (E ⊔ (P ⊓ U)).relIndex U * (E ⊓ (P ⊓ U)).relIndex (P ⊓ U) = E.relIndex U := by
    have hPU_le_U : P ⊓ U ≤ U := inf_le_right
    have key2 : E.relIndex (E ⊔ (P ⊓ U)) = (E ⊓ (P ⊓ U)).relIndex (P ⊓ U) := by
      rw [Subgroup.relIndex_sup_left, Subgroup.inf_relIndex_right]
    calc (E ⊔ (P ⊓ U)).relIndex U * (E ⊓ (P ⊓ U)).relIndex (P ⊓ U)
        = (E ⊔ (P ⊓ U)).relIndex U * E.relIndex (E ⊔ (P ⊓ U)) := by rw [key2]
      _ = E.relIndex (E ⊔ (P ⊓ U)) * (E ⊔ (P ⊓ U)).relIndex U := by rw [mul_comm]
      _ = E.relIndex U :=
          Subgroup.relIndex_mul_relIndex E (E ⊔ (P ⊓ U)) U le_sup_left (sup_le hEU hPU_le_U)
  -- ### Evaluate the two factors
  rw [hEinfM, hM] at hmod
  rw [Subgroup.relIndex_map_map_of_injective (f := θ) PU TU hθinj] at hmod
  rw [hden', hnum'] at hmod
  have hcard : 1 ≤ 2 * S.card := by omega
  have harith : p ^ (2 * S.card) = p ^ (2 * S.card - 1) * p := by
    rw [← pow_succ]
    congr 1
    omega
  have hX : (E ⊔ Subgroup.map θ TU).relIndex U = p := by
    have hc : 0 < p ^ (2 * S.card - 1) := pow_pos hp.pos _
    have h1 : (E ⊔ Subgroup.map θ TU).relIndex U * p ^ (2 * S.card - 1)
        = p * p ^ (2 * S.card - 1) := by
      rw [mul_comm p, ← harith]
      exact hmod
    exact Nat.mul_right_cancel hc h1
  -- ### Assemble
  have hidx : (P ⊔ E).index = (P ⊔ E).relIndex U := by
    rw [← Subgroup.relIndex_top_right (H := P ⊔ E), ← htop, Subgroup.relIndex_sup_left]
  have hrelU : (P ⊔ E).relIndex U = (E ⊔ (P ⊓ U)).relIndex U := by
    rw [← Subgroup.inf_relIndex_right (H := P ⊔ E) (K := U)]
    congr 1
    rw [sup_comm P E, sup_inf_assoc_of_le P hEU]
  show (P ⊔ E).index = p
  rw [hidx, hrelU, hM]
  exact hX

end NK.GlobalCFTdeep.SecondInequality.KummerCase
