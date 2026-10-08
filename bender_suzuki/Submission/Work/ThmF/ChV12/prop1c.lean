import Mathlib
import Submission.Work.ThmF.Setup
import Submission.Work.ThmF.Bender.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Peterfalvi II, Ch. V, Prop. 1 (c): the involutions of `H` lie in `Z(Q)`

Source (Peterfalvi, *Le théorème de Bender–Suzuki II*, Ch. V §1, p. 240):

> Prop. 1. c) `Inv(H) ⊆ Z(Q)` and `Inv(H) ∪ {1}` is an elementary abelian 2-group.
>
> *Proof.* `Q` nilpotent of even order, so `Z(Q)` contains an involution. `D` is transitive on
> `Inv(H)`, hence `Inv(H) ⊆ Z(Q)` and `Inv(H) ∪ {1}` is elementary abelian.

The statement below is the half of the paper's claim that needs no commutativity hypothesis: in a
split rank-one datum `H = Q ⋊ D`, `D = H ∩ Hᵗ`, if `D` is transitive by conjugation on `Inv(H)`
and `Q` is nilpotent, then every involution of `H` lies in `Z(Q)`.

Two ingredients are used.

* `|Q|` is even: `|H| = |Q| · |D|` and `|D|` is odd, while `|H|` is even.
* In a finite nilpotent group of even order the centre contains an **involution** (not merely a
  nontrivial element): the prime `2` divides the order of the centre
  (`Group.IsNilpotent.prime_dvd_card_center`), and Cauchy's theorem produces an element of order
  `2` there.

Then, for an involution `u ∈ H`, choose `d ∈ D` with `d z d⁻¹ = u` for the central involution
`z ∈ Z(Q)`: since `D ≤ H` normalises `Q` (and hence its centre), `u = d z d⁻¹` is again a
central involution of `Q`, i.e. `u ∈ Z(Q) = Q ⊓ C_G(Q)`.
-/

set_option linter.unusedVariables false

namespace Work.ThmF.ChV12

/-- In a finite nilpotent subgroup `Q ≤ G` of even order the centre contains an involution:
`2` divides the order of the centre, and an element of order `2` of that centre is an element of
`Q` of order `2` commuting with every element of `Q`. -/
theorem exists_involution_mem_centerOf {G : Type*} [Group G] [Finite G] (Q : Subgroup G)
    (hnil : Group.IsNilpotent ↥Q) (heven : Even (Nat.card ↥Q)) :
    ∃ z : G, z ∈ Q ∧ orderOf z = 2 ∧ ∀ y ∈ Q, z * y = y * z := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥Q)) 2
    (@Group.IsNilpotent.prime_dvd_card_center ↥Q _ _ hnil 2 _
      (even_iff_two_dvd.mp heven))
  refine ⟨((x : ↥Q) : G), (x : ↥Q).2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe (x : ↥Q), Subgroup.orderOf_coe x]; exact hx
  · intro y hy
    have hh : (⟨y, hy⟩ : ↥Q) * (x : ↥Q) = (x : ↥Q) * ⟨y, hy⟩ :=
      (Subgroup.mem_center_iff.mp x.2) ⟨y, hy⟩
    have h2 := congrArg (Subtype.val) hh
    simpa using h2.symm

open LeanEval.GroupTheory.Defs Submission.Blueprint Work.ThmF in theorem prop1c {G : Type} [Group G] [Finite G] (hS : Situation G) (H Q : Subgroup G) (t : G) (h : IsSplitRankOne H Q t) (hD : ∀ a ∈ involutions (H : Set G), ∀ b ∈ involutions (H : Set G), ∃ d ∈ twoPoint H t, d * a * d⁻¹ = b) (hnil : Group.IsNilpotent ↥Q) : ∀ u ∈ involutions (H : Set G), u ∈ centerOf Q := by
  -- `D = H ∩ H^t` has odd order and `|H| = |Q| * |D|` is even, so `|Q|` is even.
  have hDodd : Odd (Nat.card ↥(twoPoint H t)) := split_odd_card_twoPoint h
  have hQeven : Even (Nat.card ↥Q) := by
    have h1 : Even (Nat.card ↥Q * Nat.card ↥(twoPoint H t)) := by
      rw [← split_card_H h]; exact split_even_card_H h
    rw [Nat.even_mul] at h1
    exact h1.resolve_right (Nat.not_even_iff_odd.mpr hDodd)
  -- A central involution `z` of `Q`.
  obtain ⟨z, hzQ, hzord, hzcent⟩ :
      ∃ z : G, z ∈ Q ∧ orderOf z = 2 ∧ ∀ y ∈ Q, z * y = y * z :=
    exists_involution_mem_centerOf Q hnil hQeven
  intro u hu
  rw [mem_centerOf]
  have hzI : z ∈ involutions (H : Set G) := ⟨h.le hzQ, hzord⟩
  -- `D` is transitive on the involutions of `H`, so `u = d z d⁻¹` for some `d ∈ D`.
  obtain ⟨d, hdD, hdz⟩ := hD z hzI u hu
  have hdH : d ∈ H := Work.Models.twoPoint_le_left H t hdD
  have hdn : d ∈ Subgroup.normalizer (Q : Set G) := h.normal hdH
  have hconj : ∀ x : G, x ∈ Q ↔ d * x * d⁻¹ ∈ Q := Subgroup.mem_normalizer_iff.mp hdn
  have hdq : ∀ x : G, x ∈ Q → d⁻¹ * x * d ∈ Q := fun x hx =>
    (hconj (d⁻¹ * x * d)).mpr (by convert hx using 1; group)
  refine ⟨?_, ?_⟩
  · -- `u = d z d⁻¹ ∈ Q` because `d` normalises `Q`.
    have h1 : d⁻¹ * u * d ∈ Q := by
      rw [show d⁻¹ * u * d = z from by rw [← hdz]; group]
      exact hzQ
    have h2 := (hconj (d⁻¹ * u * d)).mp h1
    convert h2 using 1
    group
  · -- `u` commutes with every element of `Q`, conjugating the centrality of `z`.
    intro y hy
    have hyq : d⁻¹ * y * d ∈ Q := hdq y hy
    calc u * y = d * z * d⁻¹ * y := by rw [← hdz]
      _ = d * (z * (d⁻¹ * y * d)) * d⁻¹ := by group
      _ = d * ((d⁻¹ * y * d) * z) * d⁻¹ := by rw [hzcent (d⁻¹ * y * d) hyq]
      _ = y * (d * z * d⁻¹) := by group
      _ = y * u := by rw [hdz]

end Work.ThmF.ChV12
