import Mathlib
import Submission.Work.ZassenhausSuzuki.Defs
import Submission.Work.ThmF.ChV12.prop1c
import Submission.Work.ThmF.Bender.DTransitiveInv
import Submission.Work.ThmF.ChV12.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Inv(H) ⊆ Z(Q)` for split rank-one data with a 2-group `Q`

Peterfalvi, *Le théorème de Bender–Suzuki II*, Ch. V §1, Prop. 1 (c) (p. 240):

> `Inv(H) ⊆ Z(Q)`.

*Proof.* `Q` is a finite 2-group, hence nilpotent of even order, so its centre `Z(Q)` contains an
**involution** (`exists_involution_mem_centerOf`).  The two-point stabiliser `D = H ∩ Hᵗ` acts by
conjugation transitively on `Inv(H)` (`Work.ThmF.Bender.DTransitiveInv`), so every involution
`u ∈ H` is `D`-conjugate to that central involution `z ∈ Z(Q)`.  Since `D ≤ H` normalises `Q`
(and hence its centre), `u` is again a central involution of `Q`.

This is `Work.ThmF.ChV12.prop1c` with its two extra hypotheses discharged in the Zassenhaus /
Suzuki situation (`IsSplitRankOne` + `IsPGroup 2 Q`): the `D`-transitivity comes from strong
embeddedness, and nilpotency of `Q` from `Q` being a finite 2-group.  The `Situation G`
hypothesis of `prop1c` is not used by its proof, so it is not reproduced here (the statement
below carries no hypotheses beyond the split rank-one datum).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausSuzuki

/-- In a split rank-one configuration `H = Q ⋊ (H ∩ Hᵗ)` with `Q` a 2-group, every involution of
`H` is central in `Q` (Peterfalvi II Ch. V §1 Prop. 1 c). -/
theorem QSZ_invH_le_centerQ {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (h2 : IsPGroup 2 Q) :
    ∀ u ∈ Submission.Blueprint.involutions (H : Set G), u ∈ Work.ThmF.centerOf Q := by
  -- `D = H ∩ Hᵗ` is transitive on `Inv(H)` (strong embeddedness).
  have hD : ∀ a ∈ involutions (H : Set G), ∀ b ∈ involutions (H : Set G),
      ∃ d ∈ twoPoint H t, d * a * d⁻¹ = b :=
    Work.ThmF.Bender.DTransitiveInv h.stronglyEmbedded h.invol h.not_mem
  -- A finite 2-group is nilpotent.
  have hnil : Group.IsNilpotent ↥Q := IsPGroup.isNilpotent h2
  -- `|Q|` is even: `|H| = |Q| · |D|` is even and `|D|` is odd.
  have hDodd : Odd (Nat.card ↥(twoPoint H t)) := Work.ThmF.split_odd_card_twoPoint h
  have hQeven : Even (Nat.card ↥Q) := by
    have h1 : Even (Nat.card ↥Q * Nat.card ↥(twoPoint H t)) := by
      rw [← Work.ThmF.split_card_H h]
      exact Work.ThmF.split_even_card_H h
    rw [Nat.even_mul] at h1
    exact h1.resolve_right (Nat.not_even_iff_odd.mpr hDodd)
  -- a central involution `z` of `Q`
  obtain ⟨z, hzQ, hzord, hzcent⟩ :
      ∃ z : G, z ∈ Q ∧ orderOf z = 2 ∧ ∀ y ∈ Q, z * y = y * z :=
    Work.ThmF.ChV12.exists_involution_mem_centerOf Q hnil hQeven
  intro u hu
  rw [Work.ThmF.mem_centerOf]
  have hzI : z ∈ involutions (H : Set G) := ⟨h.le hzQ, hzord⟩
  obtain ⟨d, hdD, hdz⟩ := hD z hzI u hu
  have hdH : d ∈ H := (Subgroup.mem_inf.mp hdD).1
  have hdn : d ∈ Subgroup.normalizer (Q : Set G) := h.normal hdH
  have hconj : ∀ x : G, x ∈ Q ↔ d * x * d⁻¹ ∈ Q := Subgroup.mem_normalizer_iff.mp hdn
  have hdq : ∀ x : G, x ∈ Q → d⁻¹ * x * d ∈ Q := fun x hx =>
    (hconj (d⁻¹ * x * d)).mpr (by convert hx using 1; group)
  refine ⟨?_, ?_⟩
  · -- `u = d z d⁻¹ ∈ Q`
    have h1 : d⁻¹ * u * d ∈ Q := by
      rw [show d⁻¹ * u * d = z from by rw [← hdz]; group]
      exact hzQ
    have h2 := (hconj (d⁻¹ * u * d)).mp h1
    convert h2 using 1
    group
  · -- `u` commutes with every element of `Q`
    intro y hy
    have hyq : d⁻¹ * y * d ∈ Q := hdq y hy
    calc u * y = d * z * d⁻¹ * y := by rw [← hdz]
      _ = d * (z * (d⁻¹ * y * d)) * d⁻¹ := by group
      _ = d * ((d⁻¹ * y * d) * z) * d⁻¹ := by rw [hzcent (d⁻¹ * y * d) hyq]
      _ = y * (d * z * d⁻¹) := by group
      _ = y * u := by rw [hdz]

end Work.ZassenhausSuzuki
