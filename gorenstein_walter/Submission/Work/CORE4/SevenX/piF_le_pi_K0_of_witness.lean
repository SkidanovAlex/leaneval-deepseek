/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4.SevenX`)

# `π(F) ⊆ π(K₀)` from Bender's §4 (6)-witness

Bender's §4 (7) chain (p. 225 of Bender, *Finite groups with dihedral Sylow 2-subgroups*,
J. Algebra **70** (1981) 216–228) is

    π(K F(M) [S∩M, B]) = π(C_U(K₀F)) = π = π(K₀),      π := π(F(U)),   K₀ := F(U) ∩ K.

The equality `π = π(K₀)` splits into two ingredients (see `CORE4/Case2Seven.lean`,
`conj2_iff_piF`): Bender's `X`-argument `π(F(U)) = π(K₀F)`, and the inclusion `π(F) ⊆ π(K₀)`.
The latter is what Bender obtains at the end of his §4 (6)-paragraph, from the witness

    ∃ g ∉ M,  F^g ≤ F(U) ∩ M = K₀ F.

This file proves exactly that ingredient (`piF_le_pi_K0_of_witness`), so that the sibling
lemma `SevenX/piFU_le_pi_K0F` and `conj2_iff_piF` assemble `π(K₀) = π(F(U))`.

## The argument

Write `H := K₀ ⊔ F` and `A := F(U)`. By Bender's (3) (`SixThree`, = `K0_sup_F_eq`),
`H = A ⊓ M`, so the witness gives `F^g ≤ H`. By `Case2Pre.N_F`, `N_G(F) = M`, and `H ≤ M`,
so `F ⊴ H`; by §4 (6) (`Case2Ctx6.F_ti`), `F^g ⊓ F = ⊥`.

Now `Y := F^g` is a subgroup of `H` with `Y ⊓ F = ⊥`, so its image under the quotient map
`↥H →* ↥H ⧸ F` has order `|Y| = |F|`; being a subgroup of the quotient group, its order
divides `|↥H ⧸ F|`. Finally `|↥H ⧸ F| = F.relIndex H = |H| / |F| = |K₀|`, using
`relIndex_mul_card` and `card_K0_sup_F` (`|H| = |K₀| · |F|`). Hence `|F| ∣ |K₀|` and therefore
`π(F) ⊆ π(K₀)`.

The abstract cardinality step is isolated as
`card_dvd_card_quotient_of_inf_eq_bot` below.
-/
import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.SixThree
import Submission.Work.CORE4.Case2Seven

set_option linter.style.haveILetI false

namespace Work.CORE4.SevenX

open Work.GW2 Subgroup

/-- **A subgroup with trivial intersection with a normal subgroup embeds in the quotient.**

If `F ⊴ H` (recorded as `(F.subgroupOf H).Normal`) and `Y ≤ H` with `Y ⊓ F = ⊥`, then the
composite `↥Y →* ↥H ⧸ F.subgroupOf H` is injective; its image is a subgroup of the quotient, so
by Lagrange `|Y|` divides the order `|↥H ⧸ F.subgroupOf H| = F.relIndex H` of the quotient. -/
theorem card_dvd_card_quotient_of_inf_eq_bot {G : Type*} [Group G] [Finite G]
    (F H Y : Subgroup G) [hN : (F.subgroupOf H).Normal] (hYH : Y ≤ H) (hinf : Y ⊓ F = ⊥) :
    Nat.card ↥Y ∣ Nat.card ((↥H) ⧸ (F.subgroupOf H)) := by
  let ψ : ↥Y →* ((↥H) ⧸ (F.subgroupOf H)) :=
    (QuotientGroup.mk' (F.subgroupOf H)).comp (Subgroup.inclusion hYH)
  refine Subgroup.card_dvd_of_injective ψ ?_
  rw [← MonoidHom.ker_eq_bot_iff]
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  rw [MonoidHom.mem_ker] at hy
  have hmem : (Subgroup.inclusion hYH y) ∈ F.subgroupOf H := by
    refine (QuotientGroup.eq_one_iff _).mp ?_
    simpa [ψ] using hy
  have hmemF : (y : G) ∈ F := Subgroup.mem_subgroupOf.mp hmem
  have hmemY : (y : G) ∈ Y := y.2
  have h : (y : G) ∈ Y ⊓ F := Subgroup.mem_inf.mpr ⟨hmemY, hmemF⟩
  rw [hinf] at h
  exact Subtype.ext (Subgroup.mem_bot.mp h)

/-- **Bender §4 (6)/(7): `π(F) ⊆ π(K₀)` from the witness `∃ g ∉ M, F^g ≤ F(U) ⊓ M`.**

See the module docstring for the argument; the essential points are that
`F(U) ⊓ M = K₀ ⊔ F` (Bender's (3)), that `F ⊴ (K₀ ⊔ F)` because `K₀ ⊔ F ≤ M = N_G(F)`, that
`F^g ⊓ F = ⊥` by §4 (6), and that the order of the quotient `(K₀ ⊔ F)/F` is `|K₀|`. -/
theorem piF_le_pi_K0_of_witness (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G → ∀ B : Work.GW2.BenderSetup G,
      Work.GW2.Case2 B → ∀ C : Work.GW2.Case2Ctx6 B, Work.GW2.Case2PrePlus B C.D →
        (∃ g : G, g ∉ C.D.M ∧ Work.GW2.conjSub g C.D.F ≤ Work.GW2.fittingIn B.U ⊓ C.D.M) →
        Work.GW2.primesOf C.D.F ⊆ Work.GW2.primesOf C.D.K0 := by
  intro G _ _ hbc B _hcase2 C _hpreplus hwit
  obtain ⟨D, hpre, hF_ti, _hF_cyclic⟩ := C
  obtain ⟨g, hgM, hgF⟩ := hwit
  -- Bender §4 (3): `F(U) ⊓ M = K₀ ⊔ F`
  have hH_eq : D.K0 ⊔ D.F = Work.GW2.fittingIn B.U ⊓ D.M :=
    Work.CORE4.K0_sup_F_eq I hbc B D hpre
  -- the witness, reoriented: `F^g ≤ K₀ ⊔ F`
  have hYH : Work.GW2.conjSub g D.F ≤ D.K0 ⊔ D.F := by
    rw [hH_eq]; exact hgF
  -- §4 (6): `F^g ⊓ F = ⊥`
  have hYinf : Work.GW2.conjSub g D.F ⊓ D.F = ⊥ := by
    rw [inf_comm]; exact hF_ti g hgM
  have hFH : D.F ≤ D.K0 ⊔ D.F := le_sup_right
  -- `K₀ ⊔ F ≤ M`
  have hHleM : D.K0 ⊔ D.F ≤ D.M :=
    sup_le (le_trans inf_le_right (D.K_le_M B)) (le_trans (D.F_le_UinfM B) inf_le_right)
  -- `K₀ ⊔ F ≤ N_G(F) = M`, hence `F ⊴ K₀ ⊔ F`
  have hHN : D.K0 ⊔ D.F ≤ Subgroup.normalizer (D.F : Set G) := by
    rw [Work.GW2.Case2Pre.N_F B D hpre]; exact hHleM
  letI : (D.F.subgroupOf (D.K0 ⊔ D.F)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hHN
  -- `|(K₀ ⊔ F) ⧸ F| = |K₀|`
  have hrel : D.F.relIndex (D.K0 ⊔ D.F) = Nat.card ↥D.K0 := by
    have h1 := Subgroup.relIndex_mul_card D.F (D.K0 ⊔ D.F)
    rw [inf_eq_left.mpr hFH] at h1
    rw [Work.CORE4.card_K0_sup_F I hbc B D hpre] at h1
    exact Nat.mul_right_cancel (Nat.card_pos (α := ↥D.F)) h1
  have hquot_eq :
      Nat.card ((↥(D.K0 ⊔ D.F)) ⧸ (D.F.subgroupOf (D.K0 ⊔ D.F))) = Nat.card ↥D.K0 := by
    rw [← Subgroup.index_eq_card]
    exact hrel
  -- `|F^g| ∣ |(K₀ ⊔ F) ⧸ F|`
  have hdvd_quot : Nat.card ↥(Work.GW2.conjSub g D.F) ∣
      Nat.card ((↥(D.K0 ⊔ D.F)) ⧸ (D.F.subgroupOf (D.K0 ⊔ D.F))) :=
    card_dvd_card_quotient_of_inf_eq_bot (F := D.F) (H := D.K0 ⊔ D.F)
      (Y := Work.GW2.conjSub g D.F) hYH hYinf
  have hconj_card : Nat.card ↥(Work.GW2.conjSub g D.F) = Nat.card ↥D.F := by
    rw [Work.GW2.conjSub, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  -- hence `|F| ∣ |K₀|`, and therefore `π(F) ⊆ π(K₀)`
  have hdvd : Nat.card ↥D.F ∣ Nat.card ↥D.K0 := by
    rw [← hconj_card, ← hquot_eq]
    exact hdvd_quot
  intro p hp
  exact Nat.primeFactors_mono hdvd (Nat.card_pos.ne') hp

end Work.CORE4.SevenX
