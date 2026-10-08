import Mathlib
import Submission.Work.ZJB2.Defs
import Submission.Work.GLUE.PcoreApi
import Submission.Work.GLUE.PiCoreApi
import Submission.Work.ZJB2.sylowInConj
import Submission.Work.ZJB2.sylowInInfNormal
import Submission.Work.ZJB2.l52NormalMap
import Submission.Work.ZJB2.l52MemPCore
import Submission.Work.ZJB2.l52Complement

/-!
# gorenstein_walter, ZJB2 — Glauberman's Lemma 5.2 (`lemma52`)

Source: Glauberman 1968, p. 1120, Lemma 5.2.

`Work.ZJB.Lemma52Prop p` states: for a finite group `H` with a Sylow `p`-subgroup `S`, if
`C_S(P₁) ≤ P₁` where `P₁ = S ⊓ O_{p',p}(H)`, then `H/O_{p'}(H)` is `p`-constrained, i.e.
`C(O_p(H/O_{p'}(H))) ≤ O_p(H/O_{p'}(H))`.

**Route** (all in `Q = H/O_{p'}(H)`, `P = O_p(Q)`, `S̄` the image of `S`).

* `O_{p'}(Q) = 1` (`piCore_quotient_self_eq_bot`, obtained from the odd-order library's
  `oPiCore_quotient_self_eq_bot` by transporting along `piCore = oPiCore`).
* (`l52MemPCore`) every element of `D ∩ S̄` lies in `P`, where `D = C_Q(P)`: lift `x ∈ D ∩ S̄`
  to `s ∈ S`; for `y ∈ P₁` the commutator `[s,y]` lies in `S ⊓ O_{p'}(H) = 1`, so
  `s ∈ C_S(P₁) ≤ P₁` and hence `x ∈ P`.
* since `P ≤ C_Q(P) = D` (by definition) this gives `D ∩ S̄ ≤ C_Q(D)`.
* `D ⊓ S̄` is a Sylow `p`-subgroup of `D` (G2, as `D ⊴ Q` and `S̄ ∈ Syl_p(Q)`), and it is
  central in `D`; Burnside's normal `p`-complement theorem (`l52Complement`) then produces a
  normal complement `K ≅ D/(D ∩ S̄)` of `D ∩ S̄` in `D` consisting exactly of the `p'`-elements
  of `D`.
* `K` is characteristic in `D ⊴ Q`, so its image in `Q` is normal (`l52NormalMap`), and it is
  a `p'`-subgroup; hence `K ≤ O_{p'}(Q) = 1`, so `D = D ⊓ S̄ ≤ P`.
-/

namespace Work.ZJB2

open Work.GW2 Subgroup

/-! ## Auxiliary facts -/

/-- `O_π(G/O_π(G)) = 1`: quotienting by `O_π(G)` kills the `π`-radical.

This is the odd-order library's `oPiCore_quotient_self_eq_bot`, transported along the bridge
`piCore = oPiCore` via the induced isomorphism of the two quotients. -/
theorem piCore_quotient_self_eq_bot {G : Type*} [Group G] [Finite G] (π : Set ℕ) :
    Work.GW2.piCore π (G ⧸ Work.GW2.piCore π G) = ⊥ := by
  let e : (G ⧸ Work.GW2.piCore π G) ≃* (G ⧸ OddOrder.Isaacs.Ch03.oPiCore π G) :=
    QuotientGroup.quotientMulEquivOfEq (Work.GW2.piCore_eq_oPiCore π)
  have hkey : (OddOrder.Isaacs.Ch03.oPiCore π (G ⧸ Work.GW2.piCore π G)).map
      (e : G ⧸ Work.GW2.piCore π G →* G ⧸ OddOrder.Isaacs.Ch03.oPiCore π G) = ⊥ := by
    rw [OddOrder.Isaacs.Ch03.oPiCore.map_eq_of_mulEquiv π e,
      OddOrder.Isaacs.Ch03.oPiCore_quotient_self_eq_bot π]
  have h2 : Work.GW2.piCore π (G ⧸ Work.GW2.piCore π G)
      = OddOrder.Isaacs.Ch03.oPiCore π (G ⧸ Work.GW2.piCore π G) :=
    Work.GW2.piCore_eq_oPiCore π
  have hbot : (Work.GW2.piCore π (G ⧸ Work.GW2.piCore π G)).map
      (e : G ⧸ Work.GW2.piCore π G →* G ⧸ OddOrder.Isaacs.Ch03.oPiCore π G) = ⊥ := by
    rw [h2]
    exact hkey
  rw [Subgroup.map_eq_bot_iff] at hbot
  have hker : (e : G ⧸ Work.GW2.piCore π G →* G ⧸ OddOrder.Isaacs.Ch03.oPiCore π G).ker = ⊥ := by
    rw [MonoidHom.ker_eq_bot_iff]
    exact e.injective
  rw [hker, le_bot_iff] at hbot
  exact hbot

/-- `O_{p'}(H/O_{p'}(H)) = 1`. -/
theorem piCore_quotient_opPrime_eq_bot (p : ℕ) [Fact p.Prime] (H : Type*) [Group H] [Finite H] :
    Work.GW2.piCore {q : ℕ | q ≠ p} (H ⧸ Work.ZJB.OpPrime p H) = ⊥ :=
  piCore_quotient_self_eq_bot {q : ℕ | q ≠ p} (G := H)

/-! ## Glauberman's Lemma 5.2 -/

theorem lemma52 (p : ℕ) [Fact p.Prime] : Work.ZJB.Lemma52Prop p := by
  intro H _ _ S hhyp
  haveI : (Work.ZJB.OpPrime p H).Normal := Work.ZJB.piCore_normal' {q : ℕ | q ≠ p} H
  -- `S̄`, the image of `S` in `Q = H/O_{p'}(H)`
  let Sbar : Sylow p (H ⧸ Work.ZJB.OpPrime p H) :=
    Sylow.mapSurjective (QuotientGroup.mk'_surjective (Work.ZJB.OpPrime p H)) S
  have hSbar : (Sbar : Subgroup (H ⧸ Work.ZJB.OpPrime p H))
      = (S : Subgroup H).map (QuotientGroup.mk' (Work.ZJB.OpPrime p H)) :=
    Sylow.coe_mapSurjective _ S
  -- `D = C_Q(O_p(Q))`
  let D : Subgroup (H ⧸ Work.ZJB.OpPrime p H) :=
    Subgroup.centralizer ((Work.GW2.pCore p (H ⧸ Work.ZJB.OpPrime p H)) :
      Set (H ⧸ Work.ZJB.OpPrime p H))
  have hDnorm : D.Normal := inferInstance
  haveI : D.Normal := hDnorm
  have hDle : D ≤ Work.GW2.pCore p (H ⧸ Work.ZJB.OpPrime p H) := by
    -- `D ⊓ S̄ ≤ C_Q(D)`
    have hinf : D ⊓ (Sbar : Subgroup (H ⧸ Work.ZJB.OpPrime p H)) ≤
        Subgroup.centralizer (D : Set (H ⧸ Work.ZJB.OpPrime p H)) := by
      intro x hx
      have hx2 : x ∈ (S : Subgroup H).map (QuotientGroup.mk' (Work.ZJB.OpPrime p H)) := by
        rw [← hSbar]; exact hx.2
      have hxP : x ∈ Work.GW2.pCore p (H ⧸ Work.ZJB.OpPrime p H) :=
        l52MemPCore p H S hhyp hx.1 hx2
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      exact (Subgroup.mem_centralizer_iff.mp hd x hxP).symm
    -- `S̄` is a maximal `p`-subgroup of `Q`
    have hSylTop : Work.ZJB.IsSylowIn p (Sbar : Subgroup (H ⧸ Work.ZJB.OpPrime p H)) ⊤ :=
      ⟨le_top, Sbar.isPGroup', fun R hR _ hRp => Sbar.is_maximal' hRp hR⟩
    -- G2: `S̄ ⊓ D` is a Sylow `p`-subgroup of `D`
    have hSylIn : Work.ZJB.IsSylowIn p
        ((Sbar : Subgroup (H ⧸ Work.ZJB.OpPrime p H)) ⊓ D) D :=
      Step1.sylowInInfNormal hSylTop le_top (le_of_eq (Subgroup.normalizer_eq_top D).symm)
    -- as a subgroup of `↥D` it is a Sylow subgroup, central in `D`
    have hTcenter : ((subgroupOfIsSylow hSylIn : Sylow p ↥D) : Subgroup ↥D) ≤
        Subgroup.center ↥D := by
      intro x hx
      have hxmem : (x : H ⧸ Work.ZJB.OpPrime p H) ∈
          (Sbar : Subgroup (H ⧸ Work.ZJB.OpPrime p H)) ⊓ D := by
        rw [subgroupOfIsSylow_coe hSylIn, Subgroup.mem_subgroupOf] at hx
        exact hx
      have hxcen := hinf ⟨hxmem.2, hxmem.1⟩
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxcen (y : H ⧸ Work.ZJB.OpPrime p H) y.2)
    -- Burnside: a normal `p`-complement `K` of `D ⊓ S̄`, consisting of the `p'`-elements
    obtain ⟨K, _hKnorm, hKsup, _hKdisj, hKcop, hKchar⟩ :=
      l52Complement (subgroupOfIsSylow hSylIn) hTcenter
    -- its image in `Q` is a normal `p'`-subgroup of `Q`, hence trivial
    have hKQnorm : (K.map D.subtype).Normal := l52NormalMap hDnorm hKchar
    haveI : (K.map D.subtype).Normal := hKQnorm
    have hKcop' : Nat.Coprime (Nat.card ↥(K.map D.subtype)) p := by
      rw [Subgroup.card_map_of_injective D.subtype_injective]
      exact hKcop
    have hKpi : Subgroup.IsPiSubgroup {q : ℕ | q ≠ p} (K.map D.subtype) := by
      have hp : Nat.Prime p := Fact.out
      have hnotdvd : ¬ p ∣ Nat.card ↥(K.map D.subtype) := by
        rw [← hp.coprime_iff_not_dvd]
        exact Nat.coprime_comm.mp hKcop'
      intro q hq hqp
      exact hnotdvd (hqp ▸ (Nat.mem_primeFactors.mp hq).2.1)
    have hKbot : K.map D.subtype = ⊥ := by
      have h := Work.GW2.le_piCore_of_normal_isPiGroup hKpi
      rw [piCore_quotient_opPrime_eq_bot p H] at h
      exact le_bot_iff.mp h
    -- so `K = ⊥` and `D = D ⊓ S̄` is a `p`-subgroup
    have hKbot' : K = ⊥ := by
      have h := (Subgroup.map_eq_bot_iff K (f := D.subtype)).mp hKbot
      rw [Subgroup.ker_subtype] at h
      exact le_bot_iff.mp h
    have hTtop : (subgroupOfIsSylow hSylIn : Subgroup ↥D) = ⊤ := by
      rw [← hKsup, hKbot', bot_sup_eq]
    have hDp : IsPGroup p ↥D := by
      have h1 := (subgroupOfIsSylow hSylIn).isPGroup'
      rw [hTtop] at h1
      exact h1.of_equiv Subgroup.topEquiv
    exact Work.GW2.le_pCore_of_normal_isPGroup hDp
  exact hDle

end Work.ZJB2
