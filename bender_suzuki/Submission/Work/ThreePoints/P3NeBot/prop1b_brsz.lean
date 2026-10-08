/-
# `Work.ThreePoints.P3NeBot.prop1b_brsz`: Peterfalvi I Ch. II §4 Prop. 1 (b)

Same statement as `Work.ThreePoints.stronglyEmbedded_subgroupOf_inf_conj`, but built on the
Brauer–Suzuki-conditional Prop. 1 (a) `Work.ThreePoints.P3NeBot.prop1a_brsz`, so that the
import closure is free of `hole`. -/
import Mathlib
import Submission.Work.ThreePoints.Omega
import Submission.Work.ThreePoints.P3NeBot.prop1a_brsz

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.ThreePoints

open Submission.Blueprint

variable {G : Type} [Group G] [Finite G]

/-! ## 1. Even-order subgroups contain involutions -/

/-- A subgroup of even order contains an element of order two (Cauchy's theorem). -/
theorem exists_mem_orderOf_eq_two_of_even_card {K : Subgroup G} (h : Even (Nat.card K)) :
    ∃ x : G, x ∈ K ∧ orderOf x = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp h)
  exact ⟨(x : G), x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩

/-! ## 2. Evenness transfers from `M ⊓ C_G(X)` to `F ⊓ M` -/

/-- If `Inv C_G(X) ⊆ F` and `|M ⊓ C_G(X)|` is even, then `|F ⊓ M|` is even: any involution of
`C_G(X)` in `M` lies in `F` by hypothesis. -/
theorem even_card_inf_of_even_card_inf_centralizer {X F M : Subgroup G}
    (hev : Even (Nat.card (M ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)))
    (hFX : involutions (Subgroup.centralizer (X : Set G) : Set G) ⊆ F) :
    Even (Nat.card (F ⊓ M : Subgroup G)) := by
  obtain ⟨u, hu, hu2⟩ := exists_mem_orderOf_eq_two_of_even_card hev
  have huF : u ∈ F := hFX ⟨hu.2, hu2⟩
  have huFM : u ∈ F ⊓ M := ⟨huF, hu.1⟩
  have hdvd : Nat.card (Subgroup.zpowers u : Subgroup G) ∣ Nat.card (F ⊓ M : Subgroup G) :=
    Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr huFM)
  rw [even_iff_two_dvd]
  rwa [Nat.card_zpowers, hu2] at hdvd

/-! ## 3. A second fixed point of `X` -/

/-- If `X` fixes at least three points of `Ω` then, for any prescribed `g`, some other coset `g'H`
is also fixed by `X`. -/
theorem exists_mk_fixedPts_ne {H X : Subgroup G} {g : G} (hX3 : 3 ≤ (fixedPts H X).ncard) :
    ∃ g' : G, (g' : G ⧸ H) ∈ fixedPts H X ∧ (g' : G ⧸ H) ≠ (g : G ⧸ H) := by
  have h2 : 1 < (fixedPts H X).ncard := by omega
  obtain ⟨ω₁, hω₁, ω₂, hω₂, hne⟩ := (Set.one_lt_ncard (s := fixedPts H X)).mp h2
  by_cases h : ω₁ = (g : G ⧸ H)
  · obtain ⟨g', hg'⟩ := QuotientGroup.mk_surjective ω₂
    refine ⟨g', hg'.symm ▸ hω₂, fun hcontra => hne ?_⟩
    rw [h, ← hg']
    exact hcontra.symm
  · obtain ⟨g', hg'⟩ := QuotientGroup.mk_surjective ω₁
    exact ⟨g', hg'.symm ▸ hω₁, fun hcontra => h (by rw [← hg', hcontra])⟩

/-! ## 4. Proposition 1 (b) from Proposition 1 (a) -/

/-- Peterfalvi I Ch. II §4 Prop. 1 (b), conditional form: given the evenness conclusion of
Prop. 1 (a) for every fixed point of `X` (`hEV`), the subgroup `F ⊓ M` is strongly embedded in
`F` for every fixed point `M = H^g ⊇ X` of `X`. -/
theorem stronglyEmbedded_subgroupOf_inf_conj_of_even_card {H X F : Subgroup G} {g : G}
    (hH : IsStronglyEmbedded H) (hX3 : 3 ≤ (fixedPts H X).ncard)
    (hFX : involutions (Subgroup.centralizer (X : Set G) : Set G) ⊆ F)
    (hg : X ≤ conj g H)
    (hEV : ∀ {X' M' : Subgroup G}, 3 ≤ (fixedPts H X').ncard →
      (∃ g' : G, M' = conj g' H) → X' ≤ M' →
      Even (Nat.card (M' ⊓ Subgroup.centralizer (X' : Set G) : Subgroup G))) :
    IsStronglyEmbedded ((F ⊓ conj g H).subgroupOf F) := by
  have hM : IsStronglyEmbedded (conj g H) := conj_stronglyEmbedded hH g
  -- (a) `F ⊓ conj g H` has even order
  have hev : Even (Nat.card (F ⊓ conj g H : Subgroup G)) :=
    even_card_inf_of_even_card_inf_centralizer (hEV hX3 ⟨g, rfl⟩ hg) hFX
  -- (b) `F ⊓ conj g H` is a proper subgroup of `F`
  have hproper : (F ⊓ conj g H).subgroupOf F ≠ ⊤ := by
    obtain ⟨g', hfix, hne_pt⟩ := exists_mk_fixedPts_ne (H := H) (X := X) (g := g) hX3
    have hXg' : X ≤ conj g' H := by
      rw [← stabilizer_mk H g']
      exact mem_fixedPts_iff_le_stabilizer.mp hfix
    have hconjne : conj g H ≠ conj g' H := by
      intro heq
      exact hne_pt (mk_eq_of_conj_eq hH heq.symm)
    obtain ⟨u, hu, hu2⟩ := exists_mem_orderOf_eq_two_of_even_card (hEV hX3 ⟨g', rfl⟩ hXg')
    have huF : u ∈ F := hFX ⟨hu.2, hu2⟩
    have huNotM : u ∉ conj g H := by
      intro huM
      have huinf : u ∈ conj g H ⊓ conj g' H := ⟨huM, hu.1⟩
      have hdvd : Nat.card (Subgroup.zpowers u : Subgroup G) ∣
          Nat.card (conj g H ⊓ conj g' H : Subgroup G) :=
        Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr huinf)
      rw [Nat.card_zpowers, hu2] at hdvd
      exact Nat.not_even_iff_odd.mpr (card_inf_conj_odd hH hconjne)
        (even_iff_two_dvd.mpr hdvd)
    intro htop
    have hmem : u ∈ F ⊓ conj g H := by
      refine ⟨huF, ?_⟩
      have h' : (⟨u, huF⟩ : F) ∈ (F ⊓ conj g H).subgroupOf F := by rw [htop]; trivial
      exact (Subgroup.mem_subgroupOf.mp h').2
    exact huNotM hmem.2
  -- (c) Ch. I §1 (6)
  exact IsStronglyEmbedded.subgroupOf_inf hM hproper hev

end Work.ThreePoints

namespace Work.ThreePoints.P3NeBot

open Submission.Blueprint

/-- Peterfalvi I Ch. II §4 Prop. 1 (b) (with the Brauer–Suzuki black box): under (B0)–(B2), if
`X` fixes at least three points of `Ω = G ⧸ H` and `Inv C_G(X) ⊆ F ≤ N_G(X)`, then for
every fixed point `M = H^g ⊇ X` of `X` the subgroup `F ⊓ M` is strongly embedded in `F`. -/
theorem prop1b_brsz {G : Type} [Group G] [Finite G]
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC : Submission.Blueprint.ThmCProp)
    (hA : Submission.Blueprint.ThmAProp) (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    (hS : Submission.Blueprint.Situation G) {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {X F : Subgroup G}
    (hX3 : 3 ≤ (Submission.Blueprint.fixedPts H X).ncard)
    (hInv : Submission.Blueprint.involutions (Subgroup.centralizer (X : Set G) : Set G) ⊆ F)
    (hFN : F ≤ Subgroup.normalizer (X : Set G)) :
    ∀ g : G, X ≤ Submission.Blueprint.conj g H →
      LeanEval.GroupTheory.Defs.IsStronglyEmbedded ((F ⊓ Submission.Blueprint.conj g H).subgroupOf F) :=
  fun g hg => stronglyEmbedded_subgroupOf_inf_conj_of_even_card hH hX3 hInv hg
    (fun hX3' hM' hXM' => prop1a_brsz hFT hC hA hBrSz hS hH hX3' hM' hXM')

end Work.ThreePoints.P3NeBot
