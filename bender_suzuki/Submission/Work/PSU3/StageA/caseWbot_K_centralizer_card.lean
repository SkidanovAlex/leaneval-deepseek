import Mathlib
import Submission.Work.PSU3.StageA.caseWbot_setup
import Submission.Work.PSU3.StageA.centD_eq_centralizer_s
import Submission.Work.ThmF.ChV12.prop3
import Submission.Work.ThmF.ChV12.prop3_card_fixed_pow
import Submission.Work.ThmF.ChV12.fixedField_card_pow
import Submission.Work.ThmF.ChV12.mem_fixedField_iff_mem_centralizer

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.PSU3.StageA.caseWbot_K_centralizer_card`

In the situation `PSU3Hyp H Q t` with `W = C_V(K)` (`K = Ksub H t = J(D,t)`, `V = centD H t`),
let `P ≤ V` be a subgroup (in the application of prime order with `P ⊓ W = ⊥`).  Then the
`P`-fixed points of `K` and of `Q₀ = Q0sub H = ⟨Inv H⟩` are related by

  `|C_K(P)| = |C_{Q₀}(P)| - 1`.

Indeed, by Peterfalvi II Ch. V §1 Prop. 2 (with `FeitThompsonProp`) the subgroup
`K = Ksub H t` equals the set `Kset H t = J(D,t)`, and by Ch. V §2 Lemma 3 a) the
distinguished involution `s ∈ Q` of the structure identity satisfies
`V = C_D(t) = D ⊓ C_G(s)`.  Hence for `k ∈ K` and `p ∈ P ≤ V`:

* `p k p⁻¹ ∈ K` (as `p ∈ D` centralises `t`, and `D` is a group), and
* `p (k s k⁻¹) p⁻¹ = (p k p⁻¹) s (p k p⁻¹)⁻¹` because `p` centralises `s`.

Consequently, by the regularity of the action of `K` on the involutions of `H`
(Ch. V §1 Prop. 2 / `Kset_regular`: for `a, b ∈ Inv H` there is a *unique* `k ∈ K` with
`k a k⁻¹ = b`), the map `k ↦ k s k⁻¹` is a bijection `K → Q₀ \ {1}` which is *equivariant*
for the conjugation action of `P`:

  `k ∈ C_G(P) ⟺ k s k⁻¹ ∈ C_G(P)`  for `k ∈ K`.

So `k ↦ k s k⁻¹` restricts to a bijection `C_K(P) → C_{Q₀}(P) \ {1}`, giving
`|C_K(P)| = |C_{Q₀}(P)| - 1`.

The result is slightly stronger than stated: neither the primality of `|P|` nor
`P ⊓ W = ⊥` is needed, only `P ≤ V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.PSU3.StageA

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

omit [Finite G] in
/-- If `p ∈ V = centD H t` and `x ∈ Kset H t` then `p * x * p⁻¹ ∈ Kset H t`:
`p ∈ D = twoPoint H t` centralises `t` and `D` is a subgroup, while
`t (p x p⁻¹) t⁻¹ = (t p t⁻¹)(t x t⁻¹)(t p t⁻¹)⁻¹ = p x⁻¹ p⁻¹ = (p x p⁻¹)⁻¹`. -/
theorem conj_mem_Kset_of_mem_centD {x p : G} (hx : x ∈ Work.ThmF.Kset H t)
    (hp : p ∈ Submission.Blueprint.centD H t) : p * x * p⁻¹ ∈ Work.ThmF.Kset H t := by
  obtain ⟨hxD, hxinv⟩ := hx
  have hpD : p ∈ Submission.Blueprint.twoPoint H t := (Subgroup.mem_inf.mp hp).1
  have hpCt : p ∈ Subgroup.centralizer ({t} : Set G) := (Subgroup.mem_inf.mp hp).2
  have hpt : p * t = t * p := Subgroup.mem_centralizer_singleton_iff.mp hpCt
  refine ⟨(Submission.Blueprint.twoPoint H t).mul_mem
      ((Submission.Blueprint.twoPoint H t).mul_mem hpD hxD)
      ((Submission.Blueprint.twoPoint H t).inv_mem hpD), ?_⟩
  have htpt : t * p * t⁻¹ = p := by rw [← hpt]; group
  rw [show t * (p * x * p⁻¹) * t⁻¹
        = (t * p * t⁻¹) * (t * x * t⁻¹) * (t * p * t⁻¹)⁻¹ from by group, htpt, hxinv]
  group

theorem caseWbot_K_centralizer_card {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hFT : Submission.Blueprint.FeitThompsonProp)
    {P : Subgroup G} (hPV : P ≤ Submission.Blueprint.centD H t) (hPp : (Nat.card P).Prime)
    (hPW : P ⊓ Work.ThmF.W H t = ⊥) :
    Nat.card ↥(Work.ThmF.Ksub H t ⊓ Subgroup.centralizer (P : Set G))
      = Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G)) - 1 := by
  classical
  -- ## Setup
  obtain ⟨hKcyc, hKsub, hKn⟩ := caseWbot_K_facts (H := H) (Q := Q) (t := t) hS hFT hC4
  obtain ⟨⟨s, ρ⟩, ⟨hsQ, hs2, hρQ, hsr⟩, huniq⟩ :=
    Work.ThmF.ChV12.structureIdentity (Work.ThmF.IsSplitRankOne.toData hS.split)
  have ht2 : orderOf t = 2 := hS.split.invol
  have htinv : t⁻¹ = t := by
    have h := pow_orderOf_eq_one t
    rw [ht2, pow_two] at h
    exact inv_eq_of_mul_eq_one_right h
  have hsH : s ∈ H := hS.split.le hsQ
  have hsInv : s ∈ Submission.Blueprint.involutions (H : Set G) := ⟨hsH, hs2⟩
  -- Ch. V §2 Lemma 3 a): `V = D ⊓ C_G(s)`
  have hVeq : Submission.Blueprint.centD H t
      = Submission.Blueprint.twoPoint H t ⊓ Subgroup.centralizer ({s} : Set G) :=
    centD_eq_centralizer_s hS hsQ hs2 (Q.inv_mem hρQ)
      (by rw [inv_inv]; simpa [htinv] using hsr)
  set C : Subgroup G := Subgroup.centralizer (P : Set G) with hCdef
  -- ## Elementary facts about `Q₀` and `K`
  have hcomm := Work.ThmF.ChV12.involutions_of_H_commute hS.situation hC4 H Q t hS.split
  have hQ0 := Work.ThmF.ChV12.Q0sub_elementary H hcomm
  have hreg := Work.ThmF.L5.Kset_regular (H := H) (Q := Q) (t := t) hS.split
  have hone_notmem : (1 : G) ∉ Submission.Blueprint.involutions (H : Set G) := by
    rintro ⟨-, ho⟩
    rw [orderOf_one] at ho
    omega
  -- `Q₀sub H` as a set is `Inv H ∪ {1}`
  have hQ0set : (Work.ThmF.Q0sub H : Set G)
      = Submission.Blueprint.involutions (H : Set G) ∪ {1} := by
    refine Set.Subset.antisymm (fun x hx => ?_)
      (fun x hx => hx.elim (fun h => Work.ThmF.Q0_le_Q0sub H
        (Work.ThmF.involutions_subset_Q0 H h)) (fun h => h ▸ (Work.ThmF.Q0sub H).one_mem))
    rcases eq_or_ne x 1 with rfl | hx1
    · exact Or.inr rfl
    · exact Or.inl (hQ0.2.2.2 x hx hx1)
  -- ## `φ : k ↦ k * s * k⁻¹` is a bijection `K → Inv H`
  have hphi_bij : Set.BijOn (fun k : G => k * s * k⁻¹) (Work.ThmF.Kset H t)
      (Submission.Blueprint.involutions (H : Set G)) := by
    refine ⟨?_, ?_, ?_⟩
    · -- maps to
      intro x hx
      have hxH : x ∈ H := (Subgroup.mem_inf.mp (Work.ThmF.Kset_subset H t hx)).1
      exact ⟨H.mul_mem (H.mul_mem hxH hsH) (H.inv_mem hxH),
        by rw [Work.ThmF.Bender.orderOf_conj_eq, hs2]⟩
    · -- injective
      intro x hx y hy hxy
      have hxH : x ∈ H := (Subgroup.mem_inf.mp (Work.ThmF.Kset_subset H t hx)).1
      have hxinv : x * s * x⁻¹ ∈ Submission.Blueprint.involutions (H : Set G) :=
        ⟨H.mul_mem (H.mul_mem hxH hsH) (H.inv_mem hxH),
          by rw [Work.ThmF.Bender.orderOf_conj_eq, hs2]⟩
      obtain ⟨k, ⟨hk, hkval⟩, huniqK⟩ := hreg s hsInv (x * s * x⁻¹) hxinv
      have h1 : x = k := huniqK x ⟨hx, rfl⟩
      have h2 : y = k := huniqK y ⟨hy, hxy.symm⟩
      rw [h1, h2]
    · -- surjective
      intro b hb
      obtain ⟨k, ⟨hk, hkval⟩, -⟩ := hreg s hsInv b hb
      exact ⟨k, hk, hkval⟩
  -- ## Equivariance: for `x ∈ K`, `x ∈ C ⟺ φ x ∈ C`
  have hiff : ∀ x ∈ Work.ThmF.Kset H t, (x * s * x⁻¹ ∈ C ↔ x ∈ C) := by
    intro x hx
    -- every `p ∈ P ≤ V` centralises `s`, hence conjugates `(·)*s*(·)⁻¹` through
    have key : ∀ p ∈ P,
        (p * x * p⁻¹) * s * (p * x * p⁻¹)⁻¹ = p * (x * s * x⁻¹) * p⁻¹ := by
      intro p hp
      have hpCs : p ∈ Subgroup.centralizer ({s} : Set G) :=
        (Subgroup.mem_inf.mp (hVeq ▸ hPV hp)).2
      have hcomm' : Commute p s := Subgroup.mem_centralizer_singleton_iff.mp hpCs
      have hpsinv : p⁻¹ * s * p = s := by
        rw [hcomm'.inv_left.eq]; group
      rw [show (p * x * p⁻¹) * s * (p * x * p⁻¹)⁻¹
            = p * x * (p⁻¹ * s * p) * x⁻¹ * p⁻¹ from by group, hpsinv]
      group
    constructor
    · intro hxc
      refine Subgroup.mem_centralizer_iff.mpr (fun p hp => ?_)
      have hpy : p * (x * s * x⁻¹) * p⁻¹ = x * s * x⁻¹ := by
        rw [Subgroup.mem_centralizer_iff.mp hxc p hp]; group
      have heq : (p * x * p⁻¹) * s * (p * x * p⁻¹)⁻¹ = x * s * x⁻¹ := by
        rw [key p hp, hpy]
      have hpk : p * x * p⁻¹ ∈ Work.ThmF.Kset H t :=
        conj_mem_Kset_of_mem_centD hx (hPV hp)
      exact mul_inv_eq_iff_eq_mul.mp (hphi_bij.injOn hpk hx heq)
    · intro hxc
      refine Subgroup.mem_centralizer_iff.mpr (fun p hp => ?_)
      have hpx : p * x * p⁻¹ = x := by
        rw [Subgroup.mem_centralizer_iff.mp hxc p hp]; group
      have hpCs : p ∈ Subgroup.centralizer ({s} : Set G) :=
        (Subgroup.mem_inf.mp (hVeq ▸ hPV hp)).2
      have hps : p * s * p⁻¹ = s := by
        rw [Subgroup.mem_centralizer_singleton_iff.mp hpCs]; group
      have hgoal : p * (x * s * x⁻¹) * p⁻¹ = x * s * x⁻¹ := by
        rw [show p * (x * s * x⁻¹) * p⁻¹
              = (p * x * p⁻¹) * (p * s * p⁻¹) * (p * x * p⁻¹)⁻¹ from by group, hpx, hps]
      exact mul_inv_eq_iff_eq_mul.mp hgoal
  -- ## The restricted bijection gives `|K ∩ C| = |Inv H ∩ C|`
  have himg : (fun k : G => k * s * k⁻¹) '' (Work.ThmF.Kset H t ∩ (C : Set G))
      = Submission.Blueprint.involutions (H : Set G) ∩ (C : Set G) := by
    ext y
    constructor
    · rintro ⟨x, ⟨hx, hxC⟩, rfl⟩
      exact ⟨hphi_bij.mapsTo hx, (hiff x hx).mpr hxC⟩
    · rintro ⟨hy, hyC⟩
      obtain ⟨x, hx, hxy⟩ := hphi_bij.surjOn hy
      refine ⟨x, ⟨hx, ?_⟩, hxy⟩
      have hxy' : x * s * x⁻¹ = y := hxy
      exact (hiff x hx).mp (by rw [hxy']; exact hyC)
  have hcard_inv : (Work.ThmF.Kset H t ∩ (C : Set G)).ncard
      = (Submission.Blueprint.involutions (H : Set G) ∩ (C : Set G)).ncard := by
    rw [← himg]
    exact (hphi_bij.injOn.mono Set.inter_subset_left).ncard_image.symm
  -- ## The cardinality of `Q₀ ∩ C` is that of `Inv H ∩ C` plus one
  have hQ0C : ((Work.ThmF.Q0sub H : Set G) ∩ (C : Set G)).ncard
      = (Submission.Blueprint.involutions (H : Set G) ∩ (C : Set G)).ncard + 1 := by
    have h1 : ({1} : Set G) ∩ (C : Set G) = {1} := by
      rw [Set.inter_eq_left]
      exact Set.singleton_subset_iff.mpr C.one_mem
    have h2 : (1 : G) ∉ Submission.Blueprint.involutions (H : Set G) ∩ (C : Set G) :=
      fun h => hone_notmem h.1
    rw [hQ0set, Set.union_inter_distrib_right, h1, Set.union_comm, Set.singleton_union,
      Set.ncard_insert_of_notMem h2]
  -- ## Assembly
  rw [show Nat.card ↥(Work.ThmF.Ksub H t ⊓ C)
        = ((Work.ThmF.Ksub H t ⊓ C : Subgroup G) : Set G).ncard from Nat.card_coe_set_eq _,
    show Nat.card ↥(Work.ThmF.Q0sub H ⊓ C)
        = ((Work.ThmF.Q0sub H ⊓ C : Subgroup G) : Set G).ncard from Nat.card_coe_set_eq _,
    Subgroup.coe_inf, Subgroup.coe_inf, hKsub, hQ0C, hcard_inv]
  omega

end Work.PSU3.StageA
