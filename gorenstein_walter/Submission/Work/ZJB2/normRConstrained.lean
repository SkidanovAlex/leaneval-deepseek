import Mathlib
import Submission.Work.ZJB2.Defs
import Submission.Work.ZJB2.lemma52
import Submission.Work.ZJB2.mRCentralizes
import Submission.Work.GLUE.PcoreApi
import Submission.Work.GLUE.PiCoreApi

/-!
# ZJB2 — leaf `normRConstrained` (NRc)

Source: Glauberman 1968, p. 1121 ("By Lemma 5.2").

`R = (O_p(G)·C_G(O_p(G))) ∩ S` and `H = N_G(R)`.  We must show that
`H/O_{p'}(H)` is `p`-constrained, i.e.
`C_{H/O_{p'}(H)}(O_p(H/O_{p'}(H))) ≤ O_p(H/O_{p'}(H))`.

**Route.**  Glauberman's Lemma 5.2 (`Work.ZJB2.lemma52`) at the group `↥H` and the
Sylow `p`-subgroup `S' = S` (which lies in `H = N_G(R)` because `R ⊴ S`).  Its
hypothesis is `C_{S'}(P₁) ≤ P₁`, `P₁ = S' ∩ O_{p',p}(H)`:

* `R ⊴ H` and `R` is a `p`-group, so `R ≤ O_p(H) ≤ O_{p',p}(H)`; together with
  `R ≤ S` this gives `R ≤ P₁`;
* hence `C_{S'}(P₁) ≤ C_{S'}(R) ≤ C_S(P) ≤ C_G(P) ∩ S ≤ R ≤ P₁`, where `P = O_p(G)`
  (as `P ≤ R`, and `R = (P ⊔ C_G(P)) ⊓ S`).
-/

namespace Work.ZJB2

open Subgroup

/-- A Sylow `p`-subgroup of `G` contained in a subgroup `H` is a Sylow `p`-subgroup of `H`
(`Work.ZJB.IsSylowIn`, i.e. a maximal `p`-subgroup of `H`). -/
theorem isSylowIn_of_sylow_le {G : Type*} [Group G] (p : ℕ) (S : Sylow p G) {H : Subgroup G}
    (hSH : (S : Subgroup G) ≤ H) : Work.ZJB.IsSylowIn p (S : Subgroup G) H :=
  ⟨hSH, S.isPGroup', fun _Q hSQ _ hQp => S.is_maximal' hQp hSQ⟩

/-- A normal `p`-subgroup `R` of a subgroup `H` lies in `O_{p',p}(H)`. -/
theorem le_oppCore_of_normal_isPGroup {G : Type*} [Group G] (p : ℕ) {R H : Subgroup G}
    (hRnorm : (R.subgroupOf H).Normal) (hRp : IsPGroup p ↥(R.subgroupOf H)) :
    R.subgroupOf H ≤ Work.ZJB.OppCore p ↥H := by
  have hmap_norm : ((R.subgroupOf H).map (QuotientGroup.mk' (Work.ZJB.OpPrime p ↥H))).Normal :=
    hRnorm.map _ (QuotientGroup.mk'_surjective _)
  have hmap_pg : IsPGroup p
      ↥((R.subgroupOf H).map (QuotientGroup.mk' (Work.ZJB.OpPrime p ↥H))) :=
    hRp.map _
  intro x hx
  rw [Work.ZJB.OppCore, Subgroup.mem_comap]
  exact Work.GW2.le_pCore_of_normal_isPGroup hmap_pg (Subgroup.mem_map_of_mem _ hx)

theorem normRConstrained (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Finite G] :
    Work.ZJB.NormRConstrainedProp p G := by
  intro S
  set R : Subgroup G := Work.ZJB.Rsub p G S with hR
  set H : Subgroup G := Subgroup.normalizer (R : Set G) with hH
  -- basic containments
  have hRH : R ≤ H := by rw [hH]; exact Subgroup.le_normalizer
  have hSH : (S : Subgroup G) ≤ H := by
    rw [hH, hR]; exact sylow_le_normalizer_Rsub p G S
  have hPH : Work.GW2.pCore p G ≤ H := by
    rw [hH, hR]; exact pCore_le_normalizer_Rsub p G S
  have hPR : Work.GW2.pCore p G ≤ R := by
    rw [hR]; exact le_inf le_sup_left (Work.GW2.pCore_le_sylow S)
  have hRS : R ≤ (S : Subgroup G) := by rw [hR]; exact inf_le_right
  -- the Sylow `p`-subgroup `S' = S` of `↥H`
  have hSylIn : Work.ZJB.IsSylowIn p (S : Subgroup G) H := isSylowIn_of_sylow_le p S hSH
  let S' : Sylow p ↥H := subgroupOfIsSylow hSylIn
  have hS' : (S' : Subgroup ↥H) = (S : Subgroup G).subgroupOf H := subgroupOfIsSylow_coe hSylIn
  -- `R ⊴ ↥H` and `R` is a `p`-group
  have hRc_norm : (R.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRH).mpr hH.le
  have hRc_pg : IsPGroup p ↥(R.subgroupOf H) :=
    (S.isPGroup'.to_le hRS).of_equiv (Subgroup.subgroupOfEquivOfLe hRH).symm
  -- `R ≤ O_{p',p}(↥H)`
  have hRopp : R.subgroupOf H ≤ Work.ZJB.OppCore p ↥H :=
    le_oppCore_of_normal_isPGroup p hRc_norm hRc_pg
  -- `R ≤ S'`
  have hRcS' : R.subgroupOf H ≤ (S' : Subgroup ↥H) := by
    rw [hS']
    exact Subgroup.subgroupOf_mono H hRS
  -- `O_p(G) ≤ R`
  have hPcRc : (Work.GW2.pCore p G).subgroupOf H ≤ R.subgroupOf H :=
    Subgroup.subgroupOf_mono H hPR
  -- `P₁ = S' ∩ O_{p',p}(H)` contains `R`
  let P1 : Subgroup ↥H := (S' : Subgroup ↥H) ⊓ Work.ZJB.OppCore p ↥H
  have hRcP1 : R.subgroupOf H ≤ P1 := le_inf hRcS' hRopp
  -- the hypothesis `C_{S'}(P₁) ≤ P₁` of Lemma 5.2
  have hhyp : Subgroup.centralizer (P1 : Set ↥H) ⊓ (S' : Subgroup ↥H) ≤ P1 := by
    intro x hx
    obtain ⟨hxcen, hxS⟩ := Subgroup.mem_inf.mp hx
    -- `x ∈ S`
    have hxSg : (x : G) ∈ (S : Subgroup G) := by
      have h := hxS
      rw [hS', Subgroup.mem_subgroupOf] at h
      exact h
    -- `x` centralises `R`, hence `P = O_p(G)`
    have hxcenR : x ∈ Subgroup.centralizer ((R.subgroupOf H : Subgroup ↥H) : Set ↥H) :=
      Subgroup.centralizer_le hRcP1 hxcen
    have hxcenP : x ∈ Subgroup.centralizer
        (((Work.GW2.pCore p G).subgroupOf H : Subgroup ↥H) : Set ↥H) :=
      Subgroup.centralizer_le hPcRc hxcenR
    -- which happens inside `G`
    have hxcg : (x : G) ∈ Subgroup.centralizer ((Work.GW2.pCore p G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have ha' : (⟨a, hPH ha⟩ : ↥H) ∈ (Work.GW2.pCore p G).subgroupOf H :=
        Subgroup.mem_subgroupOf.mpr ha
      have hcomm := (Subgroup.mem_centralizer_iff.mp hxcenP) (⟨a, hPH ha⟩ : ↥H) ha'
      simpa using congr_arg Subtype.val hcomm
    -- so `x ∈ C_G(P) ∩ S ≤ (P ⊔ C_G(P)) ∩ S = R`
    have hxR : (x : G) ∈ R := by
      rw [hR]
      have hsup : Subgroup.centralizer (Work.GW2.pCore p G : Set G) ≤
          Work.GW2.pCore p G ⊔ Subgroup.centralizer (Work.GW2.pCore p G : Set G) :=
        le_sup_right
      exact Subgroup.mem_inf.mpr ⟨hsup hxcg, hxSg⟩
    exact Subgroup.mem_inf.mpr ⟨hxS, hRopp (Subgroup.mem_subgroupOf.mpr hxR)⟩
  exact Work.ZJB2.lemma52 p ↥H S' hhyp

end Work.ZJB2
