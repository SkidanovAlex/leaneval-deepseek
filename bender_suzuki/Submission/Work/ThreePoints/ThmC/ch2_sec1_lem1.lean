/-
# `Work.ThreePoints.ThmC.ch2_sec1_lem1` — Peterfalvi I Ch. II §1, first statement (p. 164)

If `u ∈ Inv(H)` does not centralise a subgroup `X` of a two-point stabiliser `H ∩ H^g` that it
normalises, then some involution of `H` fails to commute with `u`.  This is the contrapositive
half of the source's §1 argument: `X` has odd order, so App. I (1)(b)
(`Work.DoubleTransitivity.App1.app1_1b`) splits it as `X = C_X(u)·J(X,u)`; if `J(X,u) = 1` then
`X = C_X(u)`, and otherwise any `x ∈ J(X,u)^#` has `u·x` an involution of `H` that does not commute
with `u`.
-/
import Mathlib
import Submission.Work.ThreePoints.ThmC.Defs
import Submission.Work.DoubleTransitivity.App1.app1_1b
import Submission.Work.ThreePoints.Sec2

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.ThreePoints.ThmC

open Submission.Blueprint

/-- **Peterfalvi I Ch. II §1, first statement (p. 164).**  Let `H` be strongly embedded in the
finite group `G`, `g ∉ H`, and `X ≤ H ∩ H^g` a subgroup of the two-point stabiliser normalised by an
involution `u ∈ Inv(H)`.  If `u` does not centralise `X`, then `H` contains two involutions that do
not commute, one of them being `u`: there is `u' ∈ Inv(H)` with `u * u' ≠ u' * u`. -/
theorem ch2_sec1_lem1 {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : IsStronglyEmbedded H) {g : G} (hg : g ∉ H)
    {X : Subgroup G} (hX : X ≤ H ⊓ conj g H) {u : G}
    (hu : u ∈ involutions (H : Set G))
    (huN : u ∈ Subgroup.normalizer (X : Set G))
    (hnc : ∃ x ∈ X, u * x ≠ x * u) :
    ∃ u' : G, u' ∈ involutions (H : Set G) ∧ u * u' ≠ u' * u := by
  classical
  obtain ⟨huH, hu2⟩ := hu
  have hu2' : u * u = 1 := by rw [← pow_two, ← hu2]; exact pow_orderOf_eq_one u
  have hunorm : u * u⁻¹ = 1 := mul_inv_cancel u
  have hXH : X ≤ H := le_trans hX inf_le_left
  have hoddX : Odd (Nat.card X) :=
    Odd.of_dvd (Subgroup.card_dvd_of_le hX) (IsStronglyEmbedded.odd_card_inf_conj hH hg)
  -- App. I (1)(b): `|X| = |C_X(u)| · |J(X,u)|`
  have hcard := (Work.DoubleTransitivity.App1.app1_1b (G := G) (X := X) (t := u) hu2 hoddX huN).2
  -- `J(X,u) ≠ {1}`, else `X = C_X(u)`, contradicting `hnc`
  have hJ : ∃ x ∈ invertedBy X u, x ≠ 1 := by
    by_contra hcon
    have hJsub : invertedBy X u ⊆ ({1} : Set G) := by
      intro y hy
      rw [Set.mem_singleton_iff]
      by_contra hy1
      exact hcon ⟨y, hy, hy1⟩
    have hJcard : (invertedBy X u).ncard ≤ 1 := by
      simpa using Set.ncard_le_ncard hJsub (Set.toFinite _)
    have hJpos : 1 ≤ (invertedBy X u).ncard := by
      have h1 : (1 : G) ∈ invertedBy X u := one_mem_invertedBy X u
      have h2 : 0 < (invertedBy X u).ncard :=
        (Set.ncard_pos (Set.toFinite (invertedBy X u))).mpr ⟨1, h1⟩
      omega
    have hJeq : (invertedBy X u).ncard = 1 := le_antisymm hJcard hJpos
    have hcardX : Nat.card ↥X =
        Nat.card ↥(X ⊓ Subgroup.centralizer ({u} : Set G)) := by
      rw [hcard, hJeq, mul_one]
    have hCle : X ⊓ Subgroup.centralizer ({u} : Set G) ≤ X := inf_le_left
    have hCeq : X ⊓ Subgroup.centralizer ({u} : Set G) = X :=
      Subgroup.eq_of_le_of_card_ge hCle (le_of_eq hcardX)
    obtain ⟨x, hxX, hne⟩ := hnc
    have hxmem : x ∈ X ⊓ Subgroup.centralizer ({u} : Set G) := by rw [hCeq]; exact hxX
    have hxcen : x ∈ Subgroup.centralizer ({u} : Set G) := hxmem.2
    exact hne (Subgroup.mem_centralizer_singleton_iff.mp hxcen).symm
  obtain ⟨x, hx, hxne⟩ := hJ
  obtain ⟨hxX, hxinv⟩ := hx
  have hxord : Odd (orderOf x) := by
    refine Odd.of_dvd ?_ hoddX
    rw [← Subgroup.orderOf_mk x hxX]
    exact orderOf_dvd_natCard _
  have hxneinv : x ≠ x⁻¹ := by
    intro h1
    have hx2 : x * x = 1 := by
      calc x * x = x * x⁻¹ := by rw [← h1]
        _ = 1 := mul_inv_cancel x
    have hdvd : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hx2)
    have h1' : orderOf x = 1 := by
      rcases Nat.prime_two.eq_one_or_self_of_dvd _ hdvd with h | h
      · exact h
      · exact absurd (by rw [h]; norm_num : Even (orderOf x)) (Nat.not_even_iff_odd.mpr hxord)
    exact hxne (orderOf_eq_one_iff.mp h1')
  have hux : u * x = x⁻¹ * u := by
    calc u * x = (u * x * u⁻¹) * u := by group
      _ = x⁻¹ * u := by rw [hxinv]
  have huxu : u * x * u = x⁻¹ := by
    calc u * x * u = (u * x * u⁻¹) * (u * u) := by group
      _ = x⁻¹ := by rw [hxinv, hu2', mul_one]
  have huxne : u * x ≠ 1 := by
    intro h1
    have hxu : x = u := by
      have h := congrArg (fun z => u * z) h1
      have h2 : u * (u * x) = x := by
        calc u * (u * x) = (u * u) * x := by rw [mul_assoc]
          _ = x := by rw [hu2', one_mul]
      rw [h2, mul_one] at h
      exact h
    have hx2 : orderOf x = 2 := by rw [hxu]; exact hu2
    exact Nat.not_even_iff_odd.mpr hxord (by rw [hx2]; norm_num)
  refine ⟨u * x, ⟨H.mul_mem huH (hXH hxX), ?_⟩, ?_⟩
  · refine Work.ThreePoints.orderOf_eq_two_of huxne ?_
    calc (u * x) * (u * x) = (u * x * u) * x := by group
      _ = x⁻¹ * x := by rw [huxu]
      _ = 1 := inv_mul_cancel x
  · intro hcon
    have h1 : u * (u * x) = x := by
      calc u * (u * x) = (u * u) * x := by rw [mul_assoc]
        _ = x := by rw [hu2', one_mul]
    have hfin : x⁻¹ = x := by
      rw [huxu.symm, ← hcon]
      exact h1
    exact hxneinv hfin.symm

end Work.ThreePoints.ThmC
