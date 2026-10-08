import Mathlib
import Submission.Work.Tame.Defs
import Submission.Work.Tame.Tau
import Submission.Work.Tame.exists_conj_commuting_mul
import Submission.Work.Tame.projEC_mul
import Submission.Work.Tame.projEC_eq_self
import Submission.Work.Tame.relIndex_eq_card_inf

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Tame.isConj_projEC_of_coprime_order`

Feit–Thompson, *Solvability of groups of odd order*, Pacific J. Math. **13** (1963):  if `z` lies in
the normalizer `𝔑_j = N(𝔎_j)` of the supporting subgroup `𝔎_j` of a tamely imbedded subset `L̂`, and
`|z|` is coprime to `|𝔎_j|`, then `z` is conjugate in `𝔛` to its projection
`projEC Lhat (Hs j) z ∈ 𝔏 ⊓ 𝔑_j` of Definition 9.1(ii)(c).

The group-theoretic content is isolated in `isConj_component_of_coprime`: if `K ◁ Y` is a normal
Hall subgroup with complement `H` and `z ∈ Y` has order coprime to `|K|`, then `z` is conjugate to
its `H`-component `M ∈ H` (`z * M⁻¹ ∈ K`).

Proof of the group-theoretic statement.  Let `U = K ⊔ ⟨z⟩`; then `M ∈ U`, and applying Wielandt's
product lemma (`Work.Tame.exists_conj_commuting_mul`) inside `U` exhibits a conjugate of `z` as
`k * m` with `k ∈ K`, `m ∈ H ∩ U` and `k * m = m * k`.  Since `|z|` is coprime to `|K|` and
`(k*m)` has the order of `z`, the element `k` is trivial:  `k ^ |z| = (m ^ |z|)⁻¹` lies in
`K ⊓ (H ∩ U) = 1`.  So `z ~ m` with `m ∈ H ∩ U`, and it remains to see `m = M`.  Write the
conjugating element `u ∈ U` as `a * b` with `a ∈ K`, `b ∈ ⟨z⟩`; then `m = a z a⁻¹`, so
`m z⁻¹ = a (z a⁻¹ z⁻¹) ∈ K` and hence `m M⁻¹ = (m z⁻¹)(z M⁻¹) ∈ K ∩ H = 1`.
-/

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open Classical

namespace Work.Tame

variable {X : Type*}

/-- **Group-theoretic core.**  Let `K` be a normal Hall subgroup of a finite group `Y` with
complement `H`, let `z ∈ Y` have order coprime to `|K|`, and let `M ∈ H` be the `H`-component of
`z`, i.e. `z * M⁻¹ ∈ K`.  Then `z` is conjugate to `M`.

This is Feit–Thompson's argument (p. 805): "If `N ∈ 𝔑_i` then a complement of `𝔎_i` in `𝔎_i⟨N⟩`
is solvable.  Thus every element of `𝔑_i` is conjugate to an element of the form `HL = LH` with
`L ∈ 𝔏 ∩ 𝔑_i`, `H ∈ 𝔎_i`; when `|N|` is coprime to `|𝔎_i|` the factor `H` is trivial, and `L` is
then the projection of `N`. -/
theorem isConj_component_of_coprime {Y : Type*} [Group Y] [Fintype Y] {K H : Subgroup Y}
    [K.Normal] (hsup : K ⊔ H = ⊤) (hinf : K ⊓ H = ⊥)
    (hcop : (Nat.card K).Coprime (Nat.card H)) {z M : Y} (hMH : M ∈ H)
    (hzM : z * M⁻¹ ∈ K) (hcopz : (orderOf z).Coprime (Nat.card K)) : IsConj z M := by
  classical
  -- `U = K ⊔ ⟨z⟩`, the subgroup in which the argument takes place
  set U : Subgroup Y := K ⊔ Subgroup.zpowers z with hUdef
  have hKle : K ≤ U := le_sup_left
  have hzU : z ∈ U := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have hMU : M ∈ U := by
    have h1 : M = (z * M⁻¹)⁻¹ * z := by group
    rw [h1]
    exact Subgroup.mul_mem_sup (S := K) (T := Subgroup.zpowers z) (K.inv_mem hzM)
      (Subgroup.mem_zpowers z)
  let KU : Subgroup ↥U := K.subgroupOf U
  let MU : Subgroup ↥U := (H ⊓ U).subgroupOf U
  have hKUnorm : KU.Normal := (inferInstance : K.Normal).subgroupOf U
  haveI : KU.Normal := hKUnorm
  have hcardKU : Nat.card KU = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKle).toEquiv
  -- `U = K ⊔ (H ⊓ U)`
  have hsupU : KU ⊔ MU = ⊤ := by
    have hle : H ⊓ U ≤ U := inf_le_right
    have hEq : K ⊔ (H ⊓ U) = U := by
      apply le_antisymm
      · exact sup_le hKle hle
      · rw [hUdef]
        refine sup_le le_sup_left (Subgroup.zpowers_le.mpr ?_)
        have hh := Subgroup.mul_mem_sup (S := K) (T := H ⊓ U) hzM ⟨hMH, hMU⟩
        convert hh using 1
        group
    rw [show KU = K.subgroupOf U from rfl, show MU = (H ⊓ U).subgroupOf U from rfl,
      ← Subgroup.subgroupOf_sup hKle hle, hEq, Subgroup.subgroupOf_self]
  have hbotU : KU ⊓ MU = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_subgroupOf] at hx1 hx2
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    rw [Subgroup.coe_one]
    have hmem : (x : Y) ∈ K ⊓ H := ⟨hx1, hx2.1⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    exact hmem
  have hcopU : (Nat.card KU).Coprime (Nat.card MU) := by
    have h1 : Nat.card MU = Nat.card ↥(H ⊓ U) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    rw [hcardKU, h1]
    refine hcop.coprime_dvd_right ?_
    have hd := Subgroup.card_subgroup_dvd_card ((H ⊓ U).subgroupOf H)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : H ⊓ U ≤ H)).toEquiv] at hd
  let zU : ↥U := ⟨z, hzU⟩
  -- Wielandt's product lemma inside `U`
  obtain ⟨u, k, hk, m, hm, hcomm, hconj⟩ :=
    exists_conj_commuting_mul KU MU hsupU hbotU hcopU zU
  have hzUord : orderOf zU = orderOf z := Subgroup.orderOf_mk z hzU
  have h1 : orderOf (k * m) = orderOf z := by
    have h2 : orderOf zU = orderOf (u * zU * u⁻¹) :=
      SemiconjBy.orderOf_eq u (show SemiconjBy u zU (u * zU * u⁻¹) from by
        change u * zU = (u * zU * u⁻¹) * u
        group)
    rw [← hconj, ← h2, hzUord]
  -- the `K`-component `k` is trivial
  have hkr : k ^ (orderOf z) = 1 := by
    have h2 : (k * m) ^ (orderOf z) = 1 := by
      rw [← h1]; exact pow_orderOf_eq_one (k * m)
    rw [Commute.mul_pow (show Commute k m from hcomm) (orderOf z)] at h2
    have h3 : k ^ (orderOf z) = (m ^ (orderOf z))⁻¹ := eq_inv_of_mul_eq_one_left h2
    have h4 : k ^ (orderOf z) ∈ KU := Subgroup.pow_mem KU hk _
    have h5 : k ^ (orderOf z) ∈ MU := h3.symm ▸ MU.inv_mem (Subgroup.pow_mem MU hm _)
    have h6 : k ^ (orderOf z) ∈ KU ⊓ MU := Subgroup.mem_inf.mpr ⟨h4, h5⟩
    rwa [hbotU, Subgroup.mem_bot] at h6
  have hk1 : k = 1 := by
    have hdiv1 : orderOf k ∣ Nat.card K := by
      have := Subgroup.orderOf_dvd_natCard KU hk
      rwa [hcardKU] at this
    have hdiv2 : orderOf k ∣ orderOf z := orderOf_dvd_iff_pow_eq_one.mpr hkr
    have hg : orderOf k ∣ Nat.gcd (orderOf z) (Nat.card K) := Nat.dvd_gcd hdiv2 hdiv1
    rw [hcopz.gcd_eq_one] at hg
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hg)
  have hconj' : u * zU * u⁻¹ = m := by rw [hconj, hk1, one_mul]
  have hmY : (m : Y) = (u : Y) * z * (u : Y)⁻¹ := by
    have hh := congrArg (fun t : ↥U => (t : Y)) hconj'
    simpa [zU] using hh.symm
  -- `u ∈ U = K ⊔ ⟨z⟩`, so `m = a z a⁻¹` with `a ∈ K`
  obtain ⟨a, ha, b, hb, hab⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := K) (t := Subgroup.zpowers z)).mp
      (show (u : Y) ∈ K ⊔ Subgroup.zpowers z from u.2)
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hb
  have hbzb : b * z * b⁻¹ = z := by rw [← hi]; group
  have hm_eq : (m : Y) = a * z * a⁻¹ := by
    calc (m : Y) = (u : Y) * z * (u : Y)⁻¹ := hmY
      _ = (a * b) * z * (a * b)⁻¹ := by rw [← hab]
      _ = a * (b * z * b⁻¹) * a⁻¹ := by group
      _ = a * z * a⁻¹ := by rw [hbzb]
  have hmK : (m : Y) * z⁻¹ ∈ K := by
    rw [hm_eq, show a * z * a⁻¹ * z⁻¹ = a * (z * a⁻¹ * z⁻¹) from by group]
    exact K.mul_mem ha ((inferInstance : K.Normal).conj_mem a⁻¹ (K.inv_mem ha) z)
  have hmzM : (m : Y) * M⁻¹ ∈ K := by
    have h4 : (m : Y) * M⁻¹ = ((m : Y) * z⁻¹) * (z * M⁻¹) := by group
    rw [h4]
    exact K.mul_mem hmK hzM
  have hmM : (m : Y) = M := by
    have hmem : (m : Y) * M⁻¹ ∈ K ⊓ H :=
      Subgroup.mem_inf.mpr ⟨hmzM, H.mul_mem (Subgroup.mem_subgroupOf.mp hm).1 (H.inv_mem hMH)⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    exact eq_of_mul_inv_eq_one hmem
  rw [isConj_iff]
  exact ⟨(u : Y), hmY.symm.trans hmM⟩

/-- **Feit–Thompson, Chapter III (the projection of Definition 9.1(ii)(c)).**  Let `L̂` be tamely
imbedded in `X` with supporting subgroups `𝔎_1, …, 𝔎_n`, `𝔇 ≠ ∅`, and let `z ∈ 𝔑_j = N(𝔎_j)` have
order coprime to `|𝔎_j|`.  Then `z` is conjugate in `X` to the projection
`projEC Lhat (Hs j) z ∈ 𝔏 ⊓ 𝔑_j`, the unique element `M ∈ 𝔏 ⊓ 𝔑_j` with `z M⁻¹ ∈ 𝔎_j`.

This is the statement that every element of `𝔑_j` of `𝔎_j`-coprime order is conjugate to its
`𝔏 ∩ 𝔑_j`-component, which Feit–Thompson use in the proof of Lemma 9.1 (p. 805). -/
theorem isConj_projEC_of_coprime_order {X : Type*} [Group X] [Fintype X] {Lhat : Set X} {n : ℕ}
    {Hs : Fin n → Subgroup X} (h : Work.Tame.IsTamelyImbedded Lhat n Hs)
    (hD : (Work.Tame.Dset Lhat).Nonempty) (j : Fin n) {z : X}
    (hz : z ∈ Work.Tame.Lgrp (Hs j : Set X)) (hcop : (orderOf z).Coprime (Nat.card (Hs j))) :
    IsConj z ((Work.Tame.projEC Lhat (Hs j) ⟨z, hz⟩ :
      ↥(Work.Tame.Lgrp Lhat ⊓ Work.Tame.Lgrp (Hs j : Set X))) : X) := by
  classical
  -- Definition 9.1(ii)(b),(c)
  have hsupprod : Lgrp (Hs j : Set X) = Hs j ⊔ (Lgrp Lhat ⊓ Lgrp (Hs j : Set X)) :=
    h.supp_prod hD j
  have hsuppinf : Hs j ⊓ Lgrp Lhat = ⊥ := h.supp_inf hD j
  have hhall : IsHallIn (Hs j) (Lgrp (Hs j : Set X)) := h.supp_hall hD j
  -- work in the normalizer `𝔑_j = Lgrp (Hs j)`
  let zG : ↥(Lgrp (Hs j : Set X)) := ⟨z, hz⟩
  let Mv : ↥(Lgrp Lhat ⊓ Lgrp (Hs j : Set X)) := projEC Lhat (Hs j) zG
  let MG : ↥(Lgrp (Hs j : Set X)) := ⟨(Mv : X), Mv.2.2⟩
  let K : Subgroup ↥(Lgrp (Hs j : Set X)) := (Hs j).subgroupOf (Lgrp (Hs j : Set X))
  let Hc : Subgroup ↥(Lgrp (Hs j : Set X)) :=
    (Lgrp Lhat ⊓ Lgrp (Hs j : Set X)).subgroupOf (Lgrp (Hs j : Set X))
  have hKnorm : K.Normal := Subgroup.normal_in_normalizer
  haveI : K.Normal := hKnorm
  have hKsup : K ⊔ Hc = ⊤ := by
    rw [show K ⊔ Hc = (Hs j ⊔ (Lgrp Lhat ⊓ Lgrp (Hs j : Set X))).subgroupOf
          (Lgrp (Hs j : Set X)) from
        (Subgroup.subgroupOf_sup Subgroup.le_normalizer inf_le_right).symm,
      ← hsupprod, Subgroup.subgroupOf_self]
  have hKinf : K ⊓ Hc = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_subgroupOf] at hx1 hx2
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    rw [Subgroup.coe_one]
    have hmem : (x : X) ∈ Hs j ⊓ Lgrp Lhat := ⟨hx1, hx2.1⟩
    rw [hsuppinf, Subgroup.mem_bot] at hmem
    exact hmem
  have hKcop : (Nat.card K).Coprime (Nat.card Hc) := by
    have hcardH : Nat.card Hc = (Hs j).relIndex (Lgrp (Hs j : Set X)) := by
      rw [show Nat.card Hc = Nat.card ↥(Lgrp Lhat ⊓ Lgrp (Hs j : Set X)) from
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
      exact (relIndex_eq_card_inf h hD j).symm
    rw [show Nat.card K = Nat.card ↥(Hs j) from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv, hcardH]
    exact hhall.2
  have hMH : MG ∈ Hc := Subgroup.mem_subgroupOf.mpr Mv.2
  have hzMK : zG * MG⁻¹ ∈ K := by
    rw [Subgroup.mem_subgroupOf]
    have hh := mul_projEC_inv_mem (Lhat := Lhat) hsupprod zG
    simpa [MG, Mv, Subgroup.coe_mul, Subgroup.coe_inv] using hh
  have hcopz : (orderOf zG).Coprime (Nat.card K) := by
    rw [show orderOf zG = orderOf z from Subgroup.orderOf_mk z hz,
      show Nat.card K = Nat.card ↥(Hs j) from
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv]
    exact hcop
  have hconjG : IsConj zG MG := isConj_component_of_coprime hKsup hKinf hKcop hMH hzMK hcopz
  rw [isConj_iff] at hconjG ⊢
  obtain ⟨c, hc⟩ := hconjG
  refine ⟨(c : X), ?_⟩
  have hh := congrArg (fun t : ↥(Lgrp (Hs j : Set X)) => (t : X)) hc
  simpa [zG, MG, Mv, Subgroup.coe_mul, Subgroup.coe_inv] using hh

end Work.Tame
