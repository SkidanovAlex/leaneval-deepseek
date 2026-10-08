/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CORE2A area (fundmath3-gorenstein_walter)
-/
import Mathlib
import Submission.Work.CORE2A.TorusDefs
import Submission.Work.CORE2A.inf_centralizer_eq_center_map

/-!
# CORE2A, pass 14, leaf **Q3** (`c14_card_CN`)

The cardinality relation of `Submission/Work/_design_gw/Core14.lean` §3 (Bender 1981, p. 220):
with

* `E := E(Ĥ) = layerIn B.Hhat`, `C := cE B = C_Ĥ(E)`, `Z := zE B = Z(E)` and `t = B.t ∈ E`,

one has

`|C_{E ⊔ C}(t)| · |Z(E)| = |C_E(t)| · |C_Ĥ(E)|`.

This is the `Mt`-centralizer count used in the proof of `Thm26bTorusProp` (leaf `T1`): the
odd-index normal subgroup `Mt` of `Ĥ` contains `E ⊔ C` with index `2`, and
`|C_{Mt}(t)| = 2 · |C_{E⊔C}(t)|` (leaf `c14_card_cent_two`), so `|C_{Mt}(t) : C_Ĥ(E)| = 2k`
with `k = |C_E(t) : Z(E)|` (`kE B`).

The proof is the "pure" computation of the design note and uses no group-theoretic hypothesis
on `B` (`T`, `hFT`, `hbc` are unused):

* `C ≤ C_G(E)` and `C ≤ C_G(t)` because `t ∈ E`;
* hence `↑(E ⊔ C) = ↑E · ↑C` (pointwise product, `E` is normalised by `C ≤ C_G(E)`), and
  every `x ∈ (E ⊔ C) ⊓ C(t)` is `e · c` with `e ∈ E ⊓ C(t)`, `c ∈ C`; so
  `(E ⊔ C) ⊓ C(t) = (E ⊓ C(t)) ⊔ C`;
* `(E ⊓ C(t)) ⊓ C = E ⊓ C_G(E) = Z(E)` (the middle step is
  `inf_centralizer_eq_center_map`, the reverse inclusion uses `t ∈ E`);
* the cardinality identity is then the second-isomorphism-theorem count
  `|A ⊔ C| · |A ⊓ C| = |A| · |C|` for `A = E ⊓ C(t)`, valid because `C ≤ N_G(A)`.
-/

open scoped MatrixGroups
open scoped Pointwise

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.CORE2A

open Subgroup

/-- `|A ⊔ B| · |A ⊓ B| = |A| · |B|` for subgroups `A`, `B` of a finite group with
`B ≤ N_G(A)`: the cardinality shadow of the second isomorphism theorem
(`|A ⊔ B : A| = |B : A ⊓ B|`). -/
private theorem card_sup_mul_card_inf_of_le_normalizer {G : Type} [Group G] [Finite G]
    {A B : Subgroup G} (h : B ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card ↥A * Nat.card ↥B := by
  have hAB : (A ⊓ B).subgroupOf B = A.subgroupOf B := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩
  have h1 : (A.subgroupOf B).index * Nat.card ↥(A ⊓ B) = Nat.card ↥B := by
    have hc : Nat.card ↥(A.subgroupOf B) = Nat.card ↥(A ⊓ B) := by
      rw [← hAB]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : A ⊓ B ≤ B)).toEquiv
    rw [← hc]
    exact Subgroup.index_mul_card (A.subgroupOf B)
  have h2 : (A.subgroupOf (A ⊔ B)).index * Nat.card ↥A = Nat.card ↥(A ⊔ B) := by
    have hc : Nat.card ↥(A.subgroupOf (A ⊔ B)) = Nat.card ↥A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : A ≤ A ⊔ B)).toEquiv
    rw [← hc]
    exact Subgroup.index_mul_card (A.subgroupOf (A ⊔ B))
  have hidx : (A.subgroupOf B).index = (A.subgroupOf (A ⊔ B)).index := by
    haveI := Subgroup.normal_subgroupOf_of_le_normalizer h
    haveI := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
    have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient B A h
    rw [Subgroup.index_eq_card (A.subgroupOf B),
      Subgroup.index_eq_card (A.subgroupOf (A ⊔ B)), sup_comm]
    exact Nat.card_congr e.toEquiv
  calc Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B)
      = ((A.subgroupOf (A ⊔ B)).index * Nat.card ↥A) * Nat.card ↥(A ⊓ B) := by rw [h2]
    _ = ((A.subgroupOf B).index * Nat.card ↥A) * Nat.card ↥(A ⊓ B) := by rw [hidx]
    _ = Nat.card ↥A * ((A.subgroupOf B).index * Nat.card ↥(A ⊓ B)) := by ring
    _ = Nat.card ↥A * Nat.card ↥B := by rw [h1]

theorem c14_card_CN (T : Work.GW2.LocalToolkit) (hFT : Work.GW2.FeitThompsonProp) {G : Type} [Group G] [Finite G] (hbc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (ht : B.t ∈ Work.GW2.layerIn B.Hhat) : Nat.card ↥((Work.GW2.layerIn B.Hhat ⊔ Work.GW2.cE B) ⊓ Subgroup.centralizer ({B.t} : Set G)) * Nat.card (Work.GW2.zE B) = Nat.card ↥(Work.GW2.layerIn B.Hhat ⊓ Subgroup.centralizer ({B.t} : Set G)) * Nat.card (Work.GW2.cE B) := by
  -- notation: `E = E(Ĥ)`, `C = C_Ĥ(E)`, `Ct = C_G(t)`
  let E : Subgroup G := Work.GW2.layerIn B.Hhat
  let C : Subgroup G := Work.GW2.cE B
  let Ct : Subgroup G := Subgroup.centralizer ({B.t} : Set G)
  change Nat.card ↥((E ⊔ C) ⊓ Ct) * Nat.card (Work.GW2.zE B) =
    Nat.card ↥(E ⊓ Ct) * Nat.card ↥C
  have hE_le_Hhat : E ≤ B.Hhat := Subgroup.map_subtype_le (Work.GW2.layer B.Hhat)
  have hmid : E ⊓ Subgroup.centralizer (E : Set G) = Work.GW2.zE B :=
    inf_centralizer_eq_center_map E
  have hCunfold : C = B.Hhat ⊓ Subgroup.centralizer (E : Set G) := rfl
  have hC_le_centE : C ≤ Subgroup.centralizer (E : Set G) := by
    rw [hCunfold]; exact inf_le_right
  -- `C` centralizes `E`, and `t ∈ E`, so `C ≤ C_G(t)`
  have hC_le_Ct : C ≤ Ct := by
    intro x hx
    show x ∈ Subgroup.centralizer ({B.t} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (Subgroup.mem_centralizer_iff.mp (hC_le_centE hx)) B.t ht
  -- `E ⊔ C` is the pointwise product `E · C`
  have hE_le_normC : E ≤ Subgroup.normalizer (C : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro e he c c_mem
    have hce : e * c = c * e := (Subgroup.mem_centralizer_iff.mp (hC_le_centE c_mem)) e he
    have : e * c * e⁻¹ = c := by rw [hce]; group
    rw [this]
    exact c_mem
  -- `C` normalises `E ⊓ C_G(t)`
  have hC_le_normH : C ≤ Subgroup.normalizer ((E ⊓ Ct : Subgroup G) : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro c hc h hh
    have hch : c * h = h * c := ((Subgroup.mem_centralizer_iff.mp (hC_le_centE hc)) h hh.1).symm
    have : c * h * c⁻¹ = h := by rw [hch]; group
    rw [this]
    exact hh
  -- the key subgroup identity
  have hkey : (E ⊔ C) ⊓ Ct = (E ⊓ Ct) ⊔ C := by
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_inf] at hx
      obtain ⟨hxsup, hxCt⟩ := hx
      have hxmul : (x : G) ∈ (E : Set G) * (C : Set G) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right E C hE_le_normC]
        exact hxsup
      rw [Set.mem_mul] at hxmul
      obtain ⟨e, he, c, hc, hxec⟩ := hxmul
      have hcCt : c ∈ Ct := hC_le_Ct hc
      have heCt : e ∈ Ct := by
        have heq : e = x * c⁻¹ := by rw [← hxec]; group
        rw [heq]
        exact Ct.mul_mem hxCt (Ct.inv_mem hcCt)
      rw [← hxec]
      exact Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨he, heCt⟩) hc
    · exact sup_le (le_inf (inf_le_left.trans le_sup_left) inf_le_right)
        (le_inf le_sup_right hC_le_Ct)
  -- `E ⊓ C = Z(E)`
  have hEC : E ⊓ C = Work.GW2.zE B := by
    rw [hCunfold, ← inf_assoc, inf_eq_left.mpr hE_le_Hhat]
    exact hmid
  -- `Z(E) ≤ C_G(t)`
  have hZleCt : Work.GW2.zE B ≤ Ct := by
    rw [← hmid]
    intro x hx
    show x ∈ Subgroup.centralizer ({B.t} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (Subgroup.mem_centralizer_iff.mp hx.2) B.t ht
  -- `(E ⊓ C_G(t)) ⊓ C = Z(E)`
  have hZeq : (E ⊓ Ct) ⊓ C = Work.GW2.zE B := by
    calc (E ⊓ Ct) ⊓ C = (E ⊓ C) ⊓ Ct := by ac_rfl
      _ = Work.GW2.zE B ⊓ Ct := by rw [hEC]
      _ = Work.GW2.zE B := inf_eq_left.mpr hZleCt
  -- the second-isomorphism-theorem count at `A = E ⊓ C_G(t)`, `B = C`
  have hcount : Nat.card ↥((E ⊓ Ct) ⊔ C) * Nat.card ↥((E ⊓ Ct) ⊓ C) =
      Nat.card ↥(E ⊓ Ct) * Nat.card ↥C :=
    card_sup_mul_card_inf_of_le_normalizer hC_le_normH
  calc Nat.card ↥((E ⊔ C) ⊓ Ct) * Nat.card (Work.GW2.zE B)
      = Nat.card ↥((E ⊓ Ct) ⊔ C) * Nat.card (Work.GW2.zE B) := by rw [hkey]
    _ = Nat.card ↥((E ⊓ Ct) ⊔ C) * Nat.card ↥((E ⊓ Ct) ⊓ C) := by rw [hZeq]
    _ = Nat.card ↥(E ⊓ Ct) * Nat.card ↥C := hcount

end Work.CORE2A
