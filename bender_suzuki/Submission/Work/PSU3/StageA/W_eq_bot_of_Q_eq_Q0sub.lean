import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.ThmF.Setup
import Submission.Work.PSU3.StageA.centD_ne_bot
import Submission.Work.PSU3.StageA.distinguished_exists
import Submission.Work.PSU3.StageA.centD_eq_centralizer_s
import Submission.Work.PSU3.RankOne.H16
import Submission.Work.PSU3.RankOne.canon_conj
import Submission.Work.PSU3.RankOne.canon_mul
import Submission.Work.ThmF.ChV12.L5Base
import Submission.Work.RankOneUniqueness.closure_Q_t_eq_top

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.PSU3.StageA.not_caseA` (A5a): case a) contradicts simplicity

Peterfalvi II Ch. VI §1 Prop. case a) is `S = Q₀` (here `Q = Q0sub H`) and `st` of order `3`;
the "Réduction" of Ch. VI §3 (p. 264) kills it: `G₀ = (SK) ∪ (SKtS)` is a proper normal
subgroup (`K = J(D,t)`), contradiction with simplicity.

## Status of the statement `not_caseA` as requested

The requested statement is **missing a structural hypothesis**.  Its sibling `not_caseB`
(`Submission/Work/PSU3/StageA/not_caseB.lean`) carries
`(hC4 : ChIIFourProp) (hHig : HigmanProp)`, and every node of the area that has to know that
`K = J(D,t) = Kset H t` is a *subgroup* of `D` (Peterfalvi II Ch. V §1 Prop. 2: `K` is a cyclic
normal subgroup of `D`) carries that fact as an explicit hypothesis: `Work.ThmF.ChV12.prop3`,
`corProp2`, `chi_on_D`, `exists_linear`, `exists_linear_v2`, `Work.ThmF.ChV12.lemma5a`.  In this
workspace it is derived only

* from Appendix X + Feit–Thompson (`Work.ThmF.Tools.appX` needs `hFT : FeitThompsonProp`, via
  `Work.ThmF.ChV12.prop2v2`), and `FeitThompsonProp` is the single open hole of the whole project
  (`Work.Skeleton.minSimpleOdd_false` is a `hole`), or
* from `PSU3Hyp` + `ChIIFourProp` (`Work.PSU3.StageA.Ksub_eq_Kset_of_W_ne_bot`, the case
  `W ≠ ⊥`), and `ChIIFourProp` is itself only available modulo Feit–Thompson
  (`Work.ThreePoints.chIIFourProp_of_thmC` takes `hFT`, and `Work.ThreePoints.thmC` is a `hole`).

None of these inputs follows from `PSU3Hyp` alone, and the counting identity available from the
split rank-one data (`|D| = |V| · |Kset|`, `Work.ThmF.Bender.cardInvertedMulCardCentralizer`)
does **not** force this: the abstract claim "`⟨J(D,t)⟩ = D ⟹ C_D(t) = 1`" is false, as the
Heisenberg group `H₃(3)` of order 27 with the involutory automorphism `x ↦ x⁻¹, y ↦ y⁻¹, z ↦ z`
shows (`C_D = Z(D)` has order 3, `J(D,τ)` has order 9 and generates `D`).

## What *is* provable without those inputs, and is proved below

In case a) — i.e. if `Q = Q0sub H` (equivalently, after `Work.ThmF.ChV12.prop1c` +
`Work.PSU3.PSU3Hyp.two`, `Q = Q₀ = Inv(H) ∪ {1}` elementary abelian) — the group
`W = C_V(Kset)` must be trivial:

* `W ≤ centD H t = D ⊓ C_G(s)` (where `s` is the distinguished involution of the structure
  identity `t s t = r⁻¹ t r`), so every `w ∈ W` centralises `s`;
* `Kset H t` acts on `Inv H` with `k s k⁻¹ = u`, so `w u w⁻¹ = (w k w⁻¹)(w s w⁻¹)(w k⁻¹ w⁻¹) = u`
  for every involution `u ∈ H`: **`W` centralises `Q0sub H`**;
* in case a) `Q0sub H = Q`, and `W ≤ centD H t ≤ C_G(t)`, so `W` centralises `⟨Q, t⟩ = ⊤`
  (`Work.RankOneUniqueness.closure_Q_t_eq_top`), i.e. `W ≤ Z(G) = ⊥` by simplicity.

Combining this with `Work.PSU3.StageA.false_of_centD_normal` (proved) and
`Work.PSU3.StageA.centD_normal_of_PSU3Hyp` (`hS`, `hC4`) gives the intended contradiction as soon
as `ChIIFourProp` is among the hypotheses — which is exactly what the requested statement lacks.
-/

namespace Work.PSU3.StageA

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

/-- **Case a) forces `W = C_V(Kset) = ⊥`.**

If `Q = Q0sub H` and `s ∈ Q` is the distinguished involution of the structure identity
`t * s * t = r⁻¹ * t * r`, then `W = W H t` is trivial.  (No `ChIIFourProp` is used: the only
inputs are the structure identity's consequence `V = D ⊓ C_G(s)` —
`Work.PSU3.StageA.centD_eq_centralizer_s` — and the sharp transitivity of `Kset H t` on
`Inv H` — `Work.ThmF.L5.Kset_regular`.) -/
theorem W_eq_bot_of_Q_eq_Q0sub {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) {s r : G} (hs : s ∈ Q) (hs2 : orderOf s = 2)
    (hr : r ∈ Q) (hsr : t * s * t = r⁻¹ * t * r)
    (hQ : (Q : Set G) = Work.ThmF.Q0sub H) : Work.ThmF.W H t = ⊥ := by
  have hsplit : IsSplitRankOne H Q t := hS.split
  -- the structure identity gives `V = C_D(s)`
  have hV : Submission.Blueprint.centD H t =
      Submission.Blueprint.twoPoint H t ⊓ Subgroup.centralizer ({s} : Set G) :=
    centD_eq_centralizer_s hS hs hs2 hr hsr
  -- `s` is an involution of `H`
  have hsInv : s ∈ involutions (H : Set G) := ⟨hsplit.le hs, hs2⟩
  -- ## Step 1: every `w ∈ W` commutes with every involution of `H`
  have hWinv : ∀ w ∈ Work.ThmF.W H t, ∀ u ∈ involutions (H : Set G), w * u = u * w := by
    intro w hw u hu
    have hwc : w ∈ Submission.Blueprint.centD H t := Work.ThmF.W_le_centD H t hw
    -- `w` centralises `s`
    have hws : w * s = s * w := by
      rw [hV] at hwc
      exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hwc).2
    -- `w` centralises `Kset H t`
    have hwK : ∀ k ∈ Work.ThmF.Kset H t, w * k = k * w := by
      intro k hk
      have hc : w ∈ Subgroup.centralizer (Work.ThmF.Kset H t : Set G) := (Subgroup.mem_inf.mp hw).2
      exact (Subgroup.mem_centralizer_iff.mp hc k hk).symm
    -- write `u = k s k⁻¹` with `k ∈ Kset H t`
    obtain ⟨k, hk, hkuniq⟩ := Work.ThmF.L5.Kset_regular hsplit s hsInv u hu
    obtain ⟨hkK, hkconj⟩ := hk
    have hwk : w * k * w⁻¹ = k := by
      rw [hwK k hkK, mul_assoc, mul_inv_cancel, mul_one]
    have hwkinv : w * k⁻¹ * w⁻¹ = k⁻¹ := by
      rw [show w * k⁻¹ * w⁻¹ = (w * k * w⁻¹)⁻¹ by group, hwk]
    have hwsw : w * s * w⁻¹ = s := by
      rw [hws, mul_assoc, mul_inv_cancel, mul_one]
    have hconj : w * u * w⁻¹ = u := by
      rw [← hkconj]
      calc w * (k * s * k⁻¹) * w⁻¹
          = (w * k * w⁻¹) * (w * s * w⁻¹) * (w * k⁻¹ * w⁻¹) := by group
        _ = k * s * k⁻¹ := by rw [hwk, hwsw, hwkinv]
    have := congrArg (· * w) hconj
    simpa [mul_assoc] using this
  -- ## Step 2: `W` centralises `Q0sub H = ⟨Q0 H⟩`
  have hWcent : ∀ w ∈ Work.ThmF.W H t, ∀ x ∈ Work.ThmF.Q0sub H, x * w = w * x := by
    intro w hw x hx
    have hle : Work.ThmF.Q0sub H ≤ Subgroup.centralizer ({w} : Set G) := by
      rw [Work.ThmF.Q0sub]
      refine (Subgroup.closure_le _).mpr ?_
      intro y hy
      rcases Work.ThmF.mem_Q0_iff.mp hy with ⟨hyH, hy2⟩ | rfl
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hWinv w hw y ⟨hyH, hy2⟩).symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (by rw [one_mul, mul_one])
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
  -- ## Step 3: in case a), `W` centralises `Q` and `t`, hence lies in the centre of `G`
  have hQsub : Work.ThmF.Q0sub H = Q := Subgroup.ext (fun x => (Set.ext_iff.mp hQ x).symm)
  have hWQ : ∀ w ∈ Work.ThmF.W H t, ∀ q ∈ Q, q * w = w * q := by
    intro w hw q hq
    exact hWcent w hw q (by rw [hQsub]; exact hq)
  have hWt : ∀ w ∈ Work.ThmF.W H t, t * w = w * t := by
    intro w hw
    have hwc : w ∈ Submission.Blueprint.centD H t := Work.ThmF.W_le_centD H t hw
    exact (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hwc).2).symm
  haveI : IsSimpleGroup G := hS.simple
  have htop : Subgroup.closure ((Q : Set G) ∪ {t}) = ⊤ :=
    Work.RankOneUniqueness.closure_Q_t_eq_top hsplit
  have hWZ : Work.ThmF.W H t ≤ Subgroup.center G := by
    intro w hw
    rw [Subgroup.mem_center_iff]
    intro g
    have hle : (⊤ : Subgroup G) ≤ Subgroup.centralizer ({w} : Set G) := by
      rw [← htop]
      refine (Subgroup.closure_le _).mpr ?_
      intro y hy
      rcases hy with hy | hy
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hWQ w hw y hy)
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        exact Subgroup.mem_centralizer_singleton_iff.mpr (hWt w hw)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top g))
  -- ## Step 4: the centre of a simple nonabelian group is trivial
  have hZbot : Subgroup.center G = ⊥ := by
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hS.simple (Subgroup.center G) (inferInstance) with h | h
    · exact h
    · exfalso
      have hHcenter : H ≤ Subgroup.center G := by rw [h]; exact le_top
      have hHnorm : H.Normal := ⟨fun a ha b => by
        have hcomm : b * a = a * b := Subgroup.mem_center_iff.mp (hHcenter ha) b
        rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
        exact ha⟩
      rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hS.simple H hHnorm with hb | ht
      · have heven : Even (Nat.card H) := hsplit.stronglyEmbedded.2.1
        rw [hb, Subgroup.card_bot] at heven
        exact absurd heven (by norm_num)
      · exact hsplit.stronglyEmbedded.1 ht
  exact le_bot_iff.mp (hWZ.trans (le_of_eq hZbot))

end Work.PSU3.StageA
