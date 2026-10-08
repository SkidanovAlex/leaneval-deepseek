import Mathlib
import Submission.Work.NormalComplement.Prelim
import Submission.Work.NormalComplement.BenderPrelimAux
import Submission.Work.ThreePoints.Omega
import Submission.Work.ThreePoints.Sec2
import Submission.Work.ThreePoints.exists_involution_conj_of_odd_orderOf_mul
import Submission.Work.DoubleTransitivity.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Work.ThreePoints

namespace Work.NormalComplement

/-- Peterfalvi I Ch. I §2 Prop. 2(b): `D = H ∩ H^t` is transitive on the involutions of `H`.
Available API: `Work.ThreePoints.Omega` (`exists_conj_mem`, `card_inf_conj_odd`,
`conj_eq_of_even_card_inf`, `mk_eq_of_conj_eq`, `ncard_fixedPts_zpowers`,
`centralizer_le_stabilizer`, `stabilizer_mk`, `mem_fixedPts_iff_le_stabilizer`),
`Work.ThreePoints.Basic` (`IsStronglyEmbedded.normalizer_eq`, `IsBenderGroup.normalizer_le_of_dvd`,
`isStronglyEmbedded_iff_isBenderGroup`), `Work.ThreePoints.Sec2` (`odd_orderOf_mul` = Ch. I §2
Prop. 1(a) first part), `Work.ThreePoints.exists_involution_conj_of_odd_orderOf_mul`
(Prop. 1(a) second part), `Work.DoubleTransitivity.Basic` (the `conj`/`Ω` API).
Route (Ch. I §2 pp. 151-152): (i) Lemma 1: for `X ≤ H` of odd order, `u ∈ Inv H`, `t ∉ H` an
involution, `|u^X| ≥ |J(X,t)|` (the map `x ↦ u^x` on `J(X,t)` is injective by Prop. 1(a));
(ii) Prop. 2(a): `D` normalises `Inv(Ht)`, `J(H,t) = K`, `|t^D| = |K|` (App. I (1)(a) =
`appI_one`), `u ↦ ut` is a bijection `Inv(Ht) → K`, so `D` is transitive on `Inv(Ht)` and
`|Inv(Ht)| = |K|`; (iii) `|Inv(H)| = |Inv(Ht)|` by Prop. 1(c) (the number of involutions `u`
with `H^u = H^t` is `n`, computed from the bijection `Inv(G)∖Inv(H) → Inv(G)∖Inv(H)`,
`u ↦ s^u`, for a fixed involution `s`); (iv) `|u^D| ≥ |K| = n = |Inv(H)|` by (i) with `X = D`,
so `u^D = Inv(H)` and `D` is transitive. -/
theorem bender_prelim : Work.NormalComplement.BenderPrelimProp := by
  intro G _ _ _ H hH t ht htH u hu v hv
  obtain ⟨huH, hu2⟩ := hu
  -- `D = twoPoint H t = H ⊓ H^t` has odd order (`H ≠ H^t` since `t ∉ N_G(H) = H`)
  have hDodd : Odd (Nat.card (twoPoint H t)) := by
    have hne : conj (1 : G) H ≠ conj t H := by
      intro h
      refine htH ?_
      have : t ∈ Subgroup.normalizer (H : Set G) := by
        rw [← DoubleTransitivity.conj_eq_self_iff_mem_normalizer]
        rw [← h, DoubleTransitivity.conj_one]
      rwa [IsStronglyEmbedded.normalizer_eq hH] at this
    have h1 := card_inf_conj_odd hH hne
    rwa [DoubleTransitivity.conj_one] at h1
  -- `|K| = |Inv(H)| = n`: the bijection `Inv(Ht) ≅ K` and Prop. 1(c)
  have hK : (invertedBy (twoPoint H t) t).ncard = (involutions (H : Set G)).ncard := by
    rw [kapp_ncard_eq_invOfConj_ncard hH ht htH,
      invOfConj_ncard_eq_involutions_ncard hH ht htH]
  -- Lemma 1 with `X = D`
  have hle : (invertedBy (twoPoint H t) t).ncard ≤
      ((fun x : G => x * u * x⁻¹) '' ((twoPoint H t : Subgroup G) : Set G)).ncard :=
    lemma1_ncard_orbit_ge hH hu2 huH ht htH inf_le_left
  -- the `D`-orbit of `u` consists of involutions of `H`
  have hsub : ((fun x : G => x * u * x⁻¹) '' ((twoPoint H t : Subgroup G) : Set G)) ⊆
      (involutions (H : Set G)) := by
    rintro y ⟨d, hd, rfl⟩
    have hdH : d ∈ H := hd.1
    refine ⟨H.mul_mem (H.mul_mem hdH huH) (H.inv_mem hdH), ?_⟩
    change orderOf (d * u * d⁻¹) = 2
    have hval : d * u * d⁻¹ = (MulAut.conj d) u := by rw [MulAut.conj_apply]
    rw [hval, MulEquiv.orderOf_eq, hu2]
  -- hence the orbit is all of `Inv(H)`
  have hmain : ((fun x : G => x * u * x⁻¹) '' ((twoPoint H t : Subgroup G) : Set G)).ncard =
      (involutions (H : Set G)).ncard := by
    refine le_antisymm (Set.ncard_le_ncard hsub) ?_
    rw [← hK]; exact hle
  have hset : ((fun x : G => x * u * x⁻¹) '' ((twoPoint H t : Subgroup G) : Set G)) =
      (involutions (H : Set G)) :=
    Set.eq_of_subset_of_ncard_le hsub (le_of_eq hmain.symm)
  have hv' : v ∈ ((fun x : G => x * u * x⁻¹) '' ((twoPoint H t : Subgroup G) : Set G)) := by
    rw [hset]; exact hv
  obtain ⟨d, hd, hduv⟩ := hv'
  exact ⟨d, hd, hduv⟩

end Work.NormalComplement
