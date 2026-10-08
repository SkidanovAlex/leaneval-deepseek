/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CORE2A area (fundmath3-gorenstein_walter)
-/
import Mathlib
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE2A.Basic

/-!
# CORE2A: `|I_U(s)|` divides the number of involutions outside `H`

Bender 1981, Lemma 2.2 (p. 219).  In the notation of `BenderSetup G` let `I = I_U(s)` be the
subgroup of `U = O(H)` inverted by `s` and assume Bender's hypothesis (c)

  `N_G(X) ≤ H` for every `1 ≠ X ≤ I`.

Then the number of involutions of `G` lying outside `H = C_G(t)` is divisible by `|I|`.

The mathematics is a free-action count: `I` acts on `Ω = {x | x² = 1, x ∉ H}` by conjugation
(this needs only `I ≤ U ≤ H`), and the hypothesis says precisely that no `1 ≠ i ∈ I` fixes an
element of `Ω`: if `i` commuted with `x ∈ Ω`, then `x` would normalize the nontrivial subgroup
`⟨i⟩ ≤ I`, so `x ∈ N_G(⟨i⟩) ≤ H`.  Hence all `I`-orbits on `Ω` have exactly `|I|` elements.

## Main results

* `conj_orderOf_eq_two_and_notMem_of_le` : conjugation by an element of a subgroup `J ≤ H`
  preserves "involution outside `H`".
* `mem_normalizer_zpowers_of_commute` : an element commuting with `i` normalizes `⟨i⟩`.
* `ncard_invSet_dvd_ncard_involutions_compl` : the divisibility.
-/

open scoped MatrixGroups

-- the local group action below is built with `letI`, which the style linter misreads
set_option linter.style.haveILetI false

namespace Work.CORE2A

open Subgroup

/-- Conjugation by an element of a subgroup `J ≤ Hh` preserves the property "is an involution
outside `Hh`".  (Here only `J ≤ Hh` is used: `Hh` need not be normal.) -/
theorem conj_orderOf_eq_two_and_notMem_of_le {G : Type} [Group G] {Hh J : Subgroup G}
    (hJH : J ≤ Hh) {i x : G} (hi : i ∈ J) (hx2 : orderOf x = 2) (hxH : x ∉ Hh) :
    orderOf (i * x * i⁻¹) = 2 ∧ i * x * i⁻¹ ∉ Hh := by
  constructor
  · rw [← MulAut.conj_apply i x, MulEquiv.orderOf_eq]
    exact hx2
  · intro hmem
    refine hxH ?_
    have hx : x = i⁻¹ * (i * x * i⁻¹) * i := by group
    rw [hx]
    exact Hh.mul_mem (Hh.mul_mem (inv_mem (hJH hi)) hmem) (hJH hi)

/-- An element commuting with `i` lies in the normalizer of the cyclic subgroup `⟨i⟩`. -/
theorem mem_normalizer_zpowers_of_commute {G : Type} [Group G] {x i : G} (h : i * x = x * i) :
    x ∈ Subgroup.normalizer ((Subgroup.zpowers i : Subgroup G) : Set G) := by
  have hconv : x * i * x⁻¹ = i := by rw [← h]; group
  rw [Subgroup.mem_set_normalizer_iff]
  intro hh
  have hh' : x * hh * x⁻¹ = (MulAut.conj x) hh := (MulAut.conj_apply x hh).symm
  have hmap : Subgroup.map (MulAut.conj x).toMonoidHom (Subgroup.zpowers i) =
      Subgroup.zpowers i := by
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers ((MulAut.conj x) i) = Subgroup.zpowers i
    rw [MulAut.conj_apply, hconv]
  have hiff : ((MulAut.conj x) hh ∈ Subgroup.zpowers i) ↔ (hh ∈ Subgroup.zpowers i) := by
    conv_lhs => rw [← hmap]
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, heq⟩
      exact (MulAut.conj x).injective heq ▸ hy
    · intro hy
      exact ⟨hh, hy, rfl⟩
  rw [hh']
  exact hiff.symm

/-- **Bender 1981, Lemma 2.2.**  With `I = I_U(s)` as in the hypothesis and `N_G(X) ≤ H` for
every `1 ≠ X ≤ I`, the order of `I` divides the number of involutions outside `H`. -/
theorem ncard_invSet_dvd_ncard_involutions_compl {G : Type} [Group G] [Finite G]
    (B : Work.GW2.BenderSetup G) {s : G} (I : Subgroup G) (hI : (I : Set G) = Work.GW2.invSet B.U s)
    (hNX : ∀ X : Subgroup G, X ≠ ⊥ → X ≤ I → Subgroup.normalizer (X : Set G) ≤ B.H) :
    Nat.card I ∣ {x : G | orderOf x = 2 ∧ x ∉ B.H}.ncard := by
  classical
  have hIU : (I : Set G) ⊆ (B.U : Set G) := by
    rw [hI]; exact invSet_subset B.U s
  have hIH : I ≤ B.H := fun i hi => bSetup_U_le_H B (hIU hi)
  -- the set of involutions outside `H`, as a type
  let Ω := {x : G // orderOf x = 2 ∧ x ∉ B.H}
  have hconj : ∀ (i : I) (x : Ω), orderOf ((i : G) * (x : G) * (i : G)⁻¹) = 2 ∧
      (i : G) * (x : G) * (i : G)⁻¹ ∉ B.H :=
    fun i x => conj_orderOf_eq_two_and_notMem_of_le hIH i.2 x.2.1 x.2.2
  -- `I` acts on `Ω` by conjugation
  letI : SMul I Ω := ⟨fun i x => ⟨(i : G) * (x : G) * (i : G)⁻¹, hconj i x⟩⟩
  letI : MulAction I Ω :=
    { one_smul := fun x => Subtype.ext (by
        change (1 : G) * (x : G) * (1 : G)⁻¹ = (x : G)
        group)
      mul_smul := fun i j x => Subtype.ext (by
        change ((i : G) * (j : G)) * (x : G) * ((i : G) * (j : G))⁻¹ =
          (i : G) * ((j : G) * (x : G) * (j : G)⁻¹) * (i : G)⁻¹
        group) }
  -- the action is free: this is exactly hypothesis (c)
  have hstab : ∀ b : Ω, MulAction.stabilizer I b = ⊥ := by
    intro b
    rw [Subgroup.eq_bot_iff_forall]
    intro i hi
    have hfix : (i : G) * (b : G) * (i : G)⁻¹ = (b : G) :=
      congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp hi)
    by_contra hi1
    have hiG1 : (i : G) ≠ 1 := fun h => hi1 (Subtype.ext h)
    have hcomm : (i : G) * (b : G) = (b : G) * (i : G) := by
      have := congrArg (fun z => z * (i : G)) hfix
      simpa [mul_assoc] using this
    have hnorm := mem_normalizer_zpowers_of_commute hcomm
    have hbH : (b : G) ∈ B.H :=
      hNX (Subgroup.zpowers (i : G)) (fun h => hiG1 (Subgroup.zpowers_eq_bot.mp h))
        (by rw [Subgroup.zpowers_le]; exact i.2) hnorm
    exact b.2.2 hbH
  -- a free action gives `Nat.card Ω = #orbits * Nat.card I`
  have hcard : Nat.card Ω = Nat.card (Quotient (MulAction.orbitRel I Ω)) * Nat.card I := by
    rw [Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd (G := I) (X := Ω) hstab),
      Nat.card_prod]
  have hdvd : Nat.card I ∣ Nat.card Ω :=
    ⟨Nat.card (Quotient (MulAction.orbitRel I Ω)), by rw [hcard, Nat.mul_comm]⟩
  rw [← Nat.card_coe_set_eq]
  exact hdvd

end Work.CORE2A
