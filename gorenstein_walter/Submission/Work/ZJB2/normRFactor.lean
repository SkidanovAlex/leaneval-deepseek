import Mathlib
import Submission.Work.ZJB2.Defs
import Submission.Work.ZJB2.frattiniIn
import Submission.Work.ZJB2.zjMap
import Submission.Work.ZJB2.mRCentralizes
import Submission.Work.ZJB2.isSylowInOfLe
import Submission.Work.ZJB2.sylowInConj
import Submission.Work.ZJB2.normRConstrained
import Submission.Work.ZJB2.nrfSylowSup
import Submission.Work.GLUE.PcoreApi

/-!
# gorenstein_walter, ZJB2 — leaf `normRFactor` (NRf), Glauberman (5.5)

Source: Glauberman 1968, p. 1121.  With `P = O_p(G)`, `R = (P·C_G(P)) ∩ S`,
`Y = N_G(R)`, `M = O_{p'}(Y)` and `K(S) = Z(J(S))`, the claim is

  `N_G(R) = M · N_{N_G(R)}(K(S))`     (Glauberman's (5.5)),

formalised elementwise: every `r ∈ N_G(R)` is `m * k` with `m ∈ M` and
`k ∈ N_G(Z(J(S)))`.

**Proof.**  Work in `H = ↥Y`.  `S ≤ Y = N(R)`, so `S` is a Sylow `p`-subgroup of
`Y` (G3) and `O_{p'}(H)` is a normal `p'`-subgroup of `H`.  Lemma 5.2 applied to
`H` (with `S' = S` inside `H`) shows that `H/O_{p'}(H)` is `p`-constrained — the
hypothesis `C_{S'}(S' ∩ O_{p',p}(H)) ≤ S' ∩ O_{p',p}(H)` holds because
`R ≤ O_{p',p}(H)` and `C_S(R) ≤ C_S(P) ⊆ R`.  Hypothesis (a), applied to the
subquotient `H/O_{p'}(H)`, now gives that `Z(J(Q))` is normal in `H/O_{p'}(H)`,
where `Q` is the image of `S'`; by the characteristic-functor property
`Z(J(Q)) = Z(J(S'))O_{p'}(H)/O_{p'}(H)`.  Hence `Z(J(S)) · M ⊴ Y`, and since
`M` is a `p'`-group, `Z(J(S))` is a Sylow `p`-subgroup of that product.  The
Frattini argument with `L = M·Z(J(S))`, `T = Z(J(S))` gives
`Y = L · N_Y(Z(J(S)))`, and `L = M·Z(J(S))` because `M ⊴ Y`; finally
`M ≤ N(R)` and `Z(J(S)) ≤ S ≤ N(R)` are reflected along `Y.subtype`.
-/

namespace Work.ZJB2

open Work.ZJB
open Work.GW2
open Subgroup

open scoped Pointwise

/-! ## The lemma -/

set_option maxHeartbeats 800000 in
theorem normRFactor (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Finite G] :
    Work.ZJB.NormRFactorProp p G := by
  intro hA S r hr
  -- ### Setup: `Y = N_G(R)`, `Lq = O_{p'}(Y)`, `Sh` = `S` as a Sylow subgroup of `Y`,
  -- ### `Zq = Z(J(Sh))`
  let Y : Subgroup G := Subgroup.normalizer (Work.ZJB.Rsub p G S : Set G)
  let Lq : Subgroup ↥Y := Work.ZJB.OpPrime p ↥Y
  haveI hLqN : Lq.Normal := Work.ZJB.piCore_normal' {q : ℕ | q ≠ p} ↥Y
  have hSY : (S : Subgroup G) ≤ Y := sylow_le_normalizer_Rsub p G S
  have hSylY : Work.ZJB.IsSylowIn p (S : Subgroup G) Y := isSylowInOfLe p G S Y hSY
  let Sh : Sylow p ↥Y := subgroupOfIsSylow hSylY
  let Zq : Subgroup ↥Y := ZJ (Sh : Subgroup ↥Y)
  have hSh : (Sh : Subgroup ↥Y) = (S : Subgroup G).subgroupOf Y := subgroupOfIsSylow_coe hSylY
  -- `Sh` maps back to `S`, and `MR` is the image of `O_{p'}(Y)`
  have hShMap : Sh.map Y.subtype = (S : Subgroup G) := by
    rw [hSh, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hSY]
  have hMR : Work.ZJB.MR p G S = Lq.map Y.subtype := rfl
  -- `Z(J(·))` is a characteristic functor: transport along `Y.subtype`
  have hker_sub : Y.subtype.ker ⊓ (Sh : Subgroup ↥Y) = ⊥ := by
    rw [Subgroup.ker_subtype]
    exact bot_inf_eq _
  have hZJsub : ZJ (Sh.map Y.subtype) = (ZJ Sh).map Y.subtype :=
    (zjMap ↥Y) G Y.subtype Sh hker_sub
  have hZJ : ZJ (S : Subgroup G) = Zq.map Y.subtype := by
    rw [← hShMap]
    exact hZJsub
  -- `O_{p'}(Y)` is a `p'`-group; `Z(J(Sh)) = Zq` is a `p`-group
  have hLqPi : Subgroup.IsPiSubgroup ({p}ᶜ : Set ℕ) Lq := by
    have h := OddOrder.Isaacs.Ch03.oPiCore.isPiGroup ({p}ᶜ : Set ℕ) (G := ↥Y)
    rw [← Work.GW2.piCore_eq_oPiCore] at h
    exact h
  have hShPi : Subgroup.IsPiSubgroup ({p} : Set ℕ) (Sh : Subgroup ↥Y) :=
    Subgroup.isPiSubgroup_of_isPGroup_of_mem (π := ({p} : Set ℕ))
      (X := (Sh : Subgroup ↥Y)) Sh.isPGroup' (Set.mem_singleton p)
  have hZqle : Zq ≤ (Sh : Subgroup ↥Y) :=
    le_trans inf_le_left (Work.GW2.thompsonJ_le (Sh : Subgroup ↥Y))
  have hZqP : IsPGroup p Zq := (Sh.isPGroup').to_le hZqle
  -- ### Normality of `Zq·O_{p'}(Y)` in `↥Y`
  -- the constrainedness of `Y/O_{p'}(Y)` (Lemma 5.2 = NRc)
  have hConstr : Subgroup.centralizer (Work.GW2.pCore p (↥Y ⧸ Lq) : Set (↥Y ⧸ Lq)) ≤
      Work.GW2.pCore p (↥Y ⧸ Lq) := normRConstrained p G S
  -- hypothesis (a) at the subquotient `Y/Lq`
  have hZJQnorm : (ZJ ((Sylow.mapSurjective (QuotientGroup.mk'_surjective Lq) Sh :
      Sylow p (↥Y ⧸ Lq)) : Subgroup (↥Y ⧸ Lq))).Normal :=
    hA Y Lq hConstr _
  have hQeq : ((Sylow.mapSurjective (QuotientGroup.mk'_surjective Lq) Sh :
      Sylow p (↥Y ⧸ Lq)) : Subgroup (↥Y ⧸ Lq)) = Sh.map (QuotientGroup.mk' Lq) :=
    Sylow.coe_mapSurjective _ Sh
  -- the characteristic functor property across `mk'`
  have hZJmapq : ZJ (Sh.map (QuotientGroup.mk' Lq)) = Zq.map (QuotientGroup.mk' Lq) := by
    refine (zjMap ↥Y) (↥Y ⧸ Lq) (QuotientGroup.mk' Lq) Sh ?_
    rw [QuotientGroup.ker_mk']
    have h := OddOrder.GroupTheory.inf_eq_bot_of_isPiSubgroup_of_isPiSubgroup_compl
      hShPi hLqPi
    rwa [inf_comm] at h
  have hZJmapqNorm : (Zq.map (QuotientGroup.mk' Lq)).Normal := by
    rw [← hZJmapq, ← hQeq]
    exact hZJQnorm
  have hZqMixedNorm : (Zq ⊔ Lq).Normal := by
    have h2 : (Subgroup.comap (QuotientGroup.mk' Lq)
        (Zq.map (QuotientGroup.mk' Lq))).Normal := hZJmapqNorm.comap _
    have h3 : Zq ⊔ Lq = Subgroup.comap (QuotientGroup.mk' Lq)
        (Zq.map (QuotientGroup.mk' Lq)) := by
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
    rw [h3]
    exact h2
  have hZqNorm2 : (Lq ⊔ Zq).Normal := by
    rw [sup_comm]
    exact hZqMixedNorm
  -- ### Frattini in `↥Y` with `L = Lq ⊔ Zq`, `T = Zq`
  have hSylL : Work.ZJB.IsSylowIn p Zq (Lq ⊔ Zq) :=
    nrfSylowSup Lq Zq hLqPi hZqP
  have hnorm : (⊤ : Subgroup ↥Y) ≤
      Subgroup.normalizer ((Lq ⊔ Zq : Subgroup ↥Y) : Set ↥Y) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hZqNorm2]
  obtain ⟨l, hl, n, hn, hln⟩ :=
    frattiniIn p ↥Y ⊤ (Lq ⊔ Zq) Zq le_top hnorm hSylL ⟨r, hr⟩ trivial
  have hnNorm : n ∈ Subgroup.normalizer (Zq : Set ↥Y) :=
    (Subgroup.mem_inf.mp hn).2
  -- `L` is the product of `Lq` and `Zq` (the former being normal)
  obtain ⟨m, hm, z, hz, hmz⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := Lq) (t := Zq)).mp hl
  -- ### Transport back to `G`
  have hr_eq : r = (m : G) * ((z : G) * (n : G)) := by
    have h2 : (l : G) = (m : G) * (z : G) := by
      rw [← hmz]
      rfl
    have h1 : r = (m : G) * (z : G) * (n : G) := by
      have h1' : r = (l : G) * (n : G) := by
        simpa using congrArg Subtype.val hln
      rw [h2] at h1'
      exact h1'
    rw [h1, mul_assoc]
  have hmMR : (m : G) ∈ Work.ZJB.MR p G S := by
    rw [hMR]
    exact Subgroup.mem_map_of_mem Y.subtype hm
  have hzZJ : (z : G) ∈ ZJ (S : Subgroup G) := by
    rw [hZJ]
    exact Subgroup.mem_map_of_mem Y.subtype hz
  have hnNormG : (n : G) ∈ Subgroup.normalizer (ZJ (S : Subgroup G) : Set G) := by
    have hle := Subgroup.le_normalizer_map (Y.subtype) (H := Zq)
    have hmem : (n : G) ∈ Subgroup.map Y.subtype (Subgroup.normalizer (Zq : Set ↥Y)) :=
      Subgroup.mem_map_of_mem Y.subtype hnNorm
    have h := hle hmem
    rwa [← hZJ] at h
  refine ⟨(m : G), hmMR, (z : G) * (n : G), ?_, hr_eq⟩
  exact (Subgroup.normalizer (ZJ (S : Subgroup G) : Set G)).mul_mem
    (Subgroup.le_normalizer hzZJ) hnNormG

end Work.ZJB2
