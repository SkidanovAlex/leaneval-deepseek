/-
# `Work.ThreePoints.ThmC.ch1_sec6_cor1` — Peterfalvi I Ch. I §6 Corollary 1 (p. 162)

`G` acts transitively on the triples `(H₁,H₂,u)` with `H₁,H₂` distinct conjugates of `H` and
`u ∈ Inv(H₁)`.

The two ingredients are Theorem A (2-transitivity, hypothesis `h2t`) and Ch. I §2 Prop. 2(b)
(`Work.ThreePoints.twoPoint_transitive_on_involutions`): the two-point stabiliser `H₁ ⊓ H₂` of a
pair of distinct conjugates of `H` acts transitively by conjugation on `Inv(H₁)`.  The latter is
stated in the library for a pair `(H, H^t)` with `t` an involution; the first result below removes
that restriction (using Ch. I §2 Prop. 1(c) to produce the conjugating involution).
-/
import Mathlib
import Submission.Work.ThreePoints.ThmC.Defs
import Submission.Work.ThreePoints.TwoPointTransitive
import Submission.Work.ThreePoints.ch1_lem2
import Submission.Work.DoubleTransitivity.App2.app2_2

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

/-- Ch. I §2 Prop. 2(b) in the form needed below: the two-point stabiliser `H₁ ⊓ H₂` of an
arbitrary pair of distinct conjugates of `H` acts transitively on the involutions of `H₁`. -/
theorem twoPoint_transitive_on_involutions_conj {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : IsStronglyEmbedded H) {g₁ g₂ : G} (hne : conj g₁ H ≠ conj g₂ H) {u u' : G}
    (hu : u ∈ involutions ((conj g₁ H : Subgroup G) : Set G))
    (hu' : u' ∈ involutions ((conj g₁ H : Subgroup G) : Set G)) :
    ∃ d ∈ conj g₁ H ⊓ conj g₂ H, d * u * d⁻¹ = u' := by
  classical
  -- Ch. I §2 Prop. 1(c): some involution conjugates `conj g₁ H` to `conj g₂ H`
  obtain ⟨t, ht, htconj⟩ := Work.ThreePoints.exists_involution_conj_of_even_card_inf (F := ⊤) hH
    hne (by simpa using IsStronglyEmbedded.even_card (conj_stronglyEmbedded hH g₁))
    (by simpa using IsStronglyEmbedded.even_card (conj_stronglyEmbedded hH g₂))
  have ht2 : orderOf t = 2 := ht.2
  have htH : t ∉ conj g₁ H := by
    intro hmem
    exact hne ((conj_eq_self_of_mem hmem).symm.trans htconj)
  obtain ⟨d, hd, hdconj⟩ :=
    Work.ThreePoints.twoPoint_transitive_on_involutions (conj_stronglyEmbedded hH g₁) ht2 htH hu hu'
  refine ⟨d, ?_, hdconj⟩
  rw [twoPoint_eq, htconj] at hd
  exact hd

/-- **Peterfalvi I Ch. I §6 Corollary 1 (p. 162).**  `G` acts transitively on the triples
`(H₁,H₂,u)` with `H₁,H₂` distinct conjugates of `H` and `u ∈ Inv(H₁)`. -/
theorem ch1_sec6_cor1 {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : IsStronglyEmbedded H)
    (h2t : Submission.Blueprint.IsTwoTransitiveOn H)
    {g₁ g₂ g₁' g₂' : G} (hne : conj g₁ H ≠ conj g₂ H)
    (hne' : conj g₁' H ≠ conj g₂' H)
    {u u' : G} (hu : u ∈ involutions ((conj g₁ H : Subgroup G) : Set G))
    (hu' : u' ∈ involutions ((conj g₁' H : Subgroup G) : Set G)) :
    ∃ x : G, conj x (conj g₁ H) = conj g₁' H ∧ conj x (conj g₂ H) = conj g₂' H ∧
      x * u * x⁻¹ = u' := by
  classical
  have hpt : ((g₁ : G ⧸ H)) ≠ (g₂ : G ⧸ H) := fun h => hne (by
    have h' := congrArg (MulAction.stabilizer G) h
    rwa [stabilizer_mk H g₁, stabilizer_mk H g₂] at h')
  have hpt' : ((g₁' : G ⧸ H)) ≠ (g₂' : G ⧸ H) := fun h => hne' (by
    have h' := congrArg (MulAction.stabilizer G) h
    rwa [stabilizer_mk H g₁', stabilizer_mk H g₂'] at h')
  obtain ⟨x, hx₁, hx₂⟩ := (MulAction.is_two_pretransitive_iff.mp h2t) hpt hpt'
  have hxconj₁ : conj x (conj g₁ H) = conj g₁' H := by
    rw [← stabilizer_mk H g₁, ← Work.DoubleTransitivity.App2.stabilizer_smul_eq_conj x
      (g₁ : G ⧸ H), hx₁, stabilizer_mk H g₁']
  have hxconj₂ : conj x (conj g₂ H) = conj g₂' H := by
    rw [← stabilizer_mk H g₂, ← Work.DoubleTransitivity.App2.stabilizer_smul_eq_conj x
      (g₂ : G ⧸ H), hx₂, stabilizer_mk H g₂']
  -- `u^x` is an involution of `conj g₁' H`
  have hux : x * u * x⁻¹ ∈ involutions ((conj g₁' H : Subgroup G) : Set G) := by
    refine ⟨?_, ?_⟩
    · have h1 : x * u * x⁻¹ ∈ conj x (conj g₁ H) :=
        Subgroup.mem_map.mpr ⟨u, hu.1, MulAut.conj_apply x u⟩
      rwa [hxconj₁] at h1
    · rw [Work.ThmF.Bender.orderOf_conj_eq, hu.2]
  obtain ⟨y, hy, hyconj⟩ := twoPoint_transitive_on_involutions_conj hH hne' hux hu'
  refine ⟨y * x, ?_, ?_, ?_⟩
  · rw [Work.DoubleTransitivity.conj_mul, hxconj₁]
    exact conj_eq_self_of_mem hy.1
  · rw [Work.DoubleTransitivity.conj_mul, hxconj₂]
    exact conj_eq_self_of_mem hy.2
  · calc (y * x) * u * (y * x)⁻¹ = y * (x * u * x⁻¹) * y⁻¹ := by group
      _ = u' := hyconj

end Work.ThreePoints.ThmC
