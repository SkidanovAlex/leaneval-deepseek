/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW, `Work.BSW`)

# BSW, order case: the value of `Ind_K^G θ` on `K ∖ {1}`

For a Bender configuration `BSWHyps2 G t s K` (so `H = C_G(t) = K⟨s⟩`, `K` abelian, `s` inverts
`K`, `K` is TI with respect to `H`) and any class function `θ` on `K`, the induced class function
from `K` to `G` satisfies

`Ind_K^G θ (a) = θ a + θ a⁻¹`   for every `a ∈ K`, `a ≠ 1`.

Proof route (Bender §2 / Isaacs, the `K ◁ H` index-two case):

* induction is transitive, `Ind_K^G θ = Ind_H^G (Ind_K^H θ)` (`induce_induce_subgroupOf`);
* `K ◁ H` (`K_normal_in_centralizer`) with `H/K = ⟨sK⟩` of order two and `s` inverting `K`, so
  `Ind_K^H θ (a) = θ a + θ a⁻¹` (`induce_apply_normal_index_two`);
* `Ind_K^H θ` is supported on `K`, and `K#` is a TI-subset with normalizer bound `H`
  (`isTISubset_Kdiff`), so the second induction is the identity on `K ∖ {1}`
  (`induceApplyCoeSupportSubset`).
-/
import Mathlib
import Submission.Work.BSW.Cases.Order.Setup
import Submission.Work.BSW.Api.K_normal_in_centralizer
import Submission.Work.BSW.Api.mem_centralizer_iff
import Submission.Work.BSW.Char.inner_alpha_beta
import Submission.Work.BSW.Char.induceApplyCoeSupportSubset

open Subgroup Work.GW2 OddOrder.RepresentationTheory

namespace Work.BSW.Cases.Order

set_option linter.style.haveILetI false

theorem induceApplyCoeMemK {G : Type} [Group G] [Finite G] [Fintype G] {t s : G} {K : Subgroup G}
    [Invertible (Nat.card ↥K : ℂ)] (h : Work.GW2.BSWHyps2 G t s K)
    (θ : OddOrder.RepresentationTheory.ClassFunction ↥K ℂ) {a : ↥K} (ha : (a : G) ≠ 1) :
    OddOrder.RepresentationTheory.ClassFunction.induce K θ (a : G) = θ a + θ a⁻¹ := by
  classical
  -- `H = C_G(t) = K ⊔ ⟨s⟩` is the normalizer bound of the TI-subset `K#`.
  let H : Subgroup G := Subgroup.centralizer ({t} : Set G)
  have hKH : K ≤ H := Work.BSW.K_le_centralizer_t h
  have hsH : s ∈ H := Work.BSW.s_mem_centralizer_t h
  have hTI : OddOrder.GroupTheory.IsTISubset ((K : Set G) \ {1}) H :=
    Work.BSW.Char.isTISubset_Kdiff h
  haveI hN : (K.subgroupOf H).Normal := Work.BSW.Api.K_normal_in_centralizer h
  haveI : Fintype ↥H := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥H : ℂ) := Work.BSW.Char.invertible_natCard_subgroup H
  haveI : Invertible (Nat.card ↥(K.subgroupOf H) : ℂ) :=
    Work.BSW.Char.invertible_natCard_subgroup (K.subgroupOf H)
  haveI : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (by
      rw [Nat.cast_ne_zero]
      exact Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩)
  -- Step 1 (transitivity): `Ind_K^G θ = Ind_H^G (Ind_K^H θ)`.
  have htrans : ClassFunction.induce H
      (ClassFunction.induce (K.subgroupOf H)
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKH).toMonoidHom θ))
      = ClassFunction.induce K θ :=
    OddOrder.RepresentationTheory.induce_induce_subgroupOf (M := G) hKH θ
  set ψ : ClassFunction ↥H ℂ := ClassFunction.induce (K.subgroupOf H)
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKH).toMonoidHom θ) with hψ
  -- Step 2: `ψ = Ind_K^H θ` is supported on `K`.
  have hsupp : ∀ x : ↥H, (x : G) ∉ K → ψ x = 0 := by
    intro x hx
    have hxN : x ∉ K.subgroupOf H := by rwa [Subgroup.mem_subgroupOf]
    rw [hψ]
    exact ClassFunction.induce_apply_eq_zero_of_not_mem_normal (K.subgroupOf H) _ hxN
  -- Step 3 (TI value identity): `Ind_H^G ψ` agrees with `ψ` at `a ∈ K ∖ {1}`.
  have hval : ClassFunction.induce H ψ (a : G) = ψ ⟨(a : G), hKH a.2⟩ :=
    Work.BSW.Char.induceApplyCoeSupportSubset (K := K) (H := H) hKH hTI ψ hsupp ha
  -- Step 4 (index-two data in `H = K ⊔ ⟨s⟩`).
  have hσ : (⟨s, hsH⟩ : ↥H) * ⟨s, hsH⟩ = 1 := by
    apply Subtype.ext
    simpa using Work.BSW.s_mul_self h
  have hσN : (⟨s, hsH⟩ : ↥H) ∉ K.subgroupOf H := by
    intro hmem
    exact Work.BSW.s_notMem_K h (by rwa [Subgroup.mem_subgroupOf] at hmem)
  have hcover : ∀ b : ↥H, b ∉ K.subgroupOf H → b * ⟨s, hsH⟩ ∈ K.subgroupOf H := by
    intro b hb
    rw [Subgroup.mem_subgroupOf]
    have hbG : (b : G) ∉ K := by
      intro hc; exact hb (by rwa [Subgroup.mem_subgroupOf])
    rcases (Work.BSW.Api.mem_centralizer_iff h (b : G)).mp b.2 with h1 | ⟨k, hk, hkeq⟩
    · exact absurd h1 hbG
    · have hcoe : ((b * ⟨s, hsH⟩ : ↥H) : G) = k := by
        show (b : G) * s = k
        rw [hkeq, mul_assoc, Work.BSW.s_mul_self h, mul_one]
      rw [hcoe]; exact hk
  have hinv : ∀ n : ↥H, n ∈ K.subgroupOf H → ⟨s, hsH⟩ * n * ⟨s, hsH⟩⁻¹ = n⁻¹ := by
    intro n hn
    apply Subtype.ext
    show s * (n : G) * s⁻¹ = ((n⁻¹ : ↥H) : G)
    rw [Work.BSW.inverts_s_K h (n : G) ((Subgroup.mem_subgroupOf).mp hn)]
    rfl
  -- Step 5 (index-two evaluation): `Ind_K^H θ (a) = θ a + θ a⁻¹`.
  set e := Subgroup.subgroupOfEquivOfLe hKH with he
  set ψ' : ClassFunction ↥(K.subgroupOf H) ℂ := ClassFunction.compHom e.toMonoidHom θ with hψ'
  let m : ↥(K.subgroupOf H) := e.symm a
  have hidx := Work.BSW.Char.induce_apply_normal_index_two (N := K.subgroupOf H)
    hσ hσN hcover hinv ψ' m
  have hm : m = e.symm a := rfl
  have hmcoe : ((m : ↥H)) = ⟨(a : G), hKH a.2⟩ := by
    apply Subtype.ext
    show ((m : ↥H) : G) = (a : G)
    rw [show ((m : ↥H) : G) = ((e m : ↥K) : G) from rfl, hm, MulEquiv.apply_symm_apply]
  have h1 : ψ' m = θ a := by
    rw [hψ', ClassFunction.compHom_apply, hm]
    simp
  have h2 : ψ' ⟨(m : ↥H)⁻¹, (K.subgroupOf H).inv_mem m.2⟩ = θ a⁻¹ := by
    rw [hψ', ClassFunction.compHom_apply]
    have hmm : (⟨(m : ↥H)⁻¹, (K.subgroupOf H).inv_mem m.2⟩ : ↥(K.subgroupOf H)) = m⁻¹ := by
      apply Subtype.ext; rfl
    rw [hmm, hm]
    simp
  calc ClassFunction.induce K θ (a : G)
      = ClassFunction.induce H ψ (a : G) := by rw [← htrans, hψ]
    _ = ψ ⟨(a : G), hKH a.2⟩ := hval
    _ = ψ ((m : ↥H)) := by rw [hmcoe]
    _ = ψ' m + ψ' ⟨(m : ↥H)⁻¹, (K.subgroupOf H).inv_mem m.2⟩ := hidx
    _ = θ a + θ a⁻¹ := by rw [h1, h2]

end Work.BSW.Cases.Order
