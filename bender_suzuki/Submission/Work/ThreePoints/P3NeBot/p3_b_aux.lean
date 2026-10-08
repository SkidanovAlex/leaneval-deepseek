import Mathlib
import Submission.Blueprint.Interfaces
import Submission.Work.ThreePoints.P3Sub.Basic
import Submission.Work.ThreePoints.P3NeBot.Basic
import Submission.Work.ThreePoints.P3NeBot.oddResidual_basic
import Submission.Work.ThreePoints.Omega
import Submission.Work.ThreePoints.Sec2
import Submission.Work.ThreePoints.Sec2b
import Submission.Work.ThreePoints.OddResidual
import Submission.Work.ThreePoints.isStronglyEmbedded_map_quotient
import Submission.Work.ThreePoints.oddCore_le_of_stronglyEmbedded
import Submission.Work.Reductions.OddResidual

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThreePoints.P3NeBot.p3_b_aux` — glue for Peterfalvi I Ch. II §4 Prop. 3 (b)

Auxiliary lemmas used by `Work.ThreePoints.P3NeBot.p3_b`.  They are elementary (no `(B1)`, no
`hMod`): the `3` fixed points of `V = C_D(t)`, an even-order subgroup contains an involution,
Prop. 2 (c) (`x ∈ K#` fixes exactly two points) built directly on Ch. II §4 Prop. 1 (a), the copy
of the "Prop. 1 (a) ⟹ Prop. 1 (b)" step, and the export of `O^{2'}(O^{2'}(G)) = ⊤`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open LeanEval.GroupTheory.Defs

namespace Work.ThreePoints.P3NeBot

open Submission.Blueprint

variable {G : Type} [Group G] [Finite G]

/-! ## An even-order subgroup contains an involution -/

/-- An even-order subgroup contains an element of order `2` (Cauchy for `p = 2`). -/
theorem exists_orderOf_two_of_even_card {C : Subgroup G} (h : Even (Nat.card C)) :
    ∃ u ∈ C, orderOf u = 2 := by
  haveI : Fintype ↥C := Fintype.ofFinite ↥C
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Fintype.card ↥C := by
    rw [Fintype.card_eq_nat_card]; exact even_iff_two_dvd.mp h
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card (G := ↥C) 2 h2
  exact ⟨(u : G), u.2, (orderOf_injective C.subtype C.subtype_injective u).trans hu⟩

/-! ## `V = C_D(t)` fixes at least three points of `Ω`

(Transferred from `Work.ThreePoints.three_le_ncard_fixedPts_centD`, whose module's closure
contains a `hole`; the proof is self-contained.) -/

/-- `V = C_D(t)` fixes at least the three points `H`, `tH` and the (unique) fixed point of the
involution `t` in `Ω = G ⧸ H`. -/
theorem three_le_ncard_fixedPts_centD {H : Subgroup G} (hH : IsStronglyEmbedded H) {t : G}
    (ht : orderOf t = 2) (htH : t ∉ H) :
    3 ≤ (fixedPts H (centD H t)).ncard := by
  have ht2 : t * t = 1 := mul_self_eq_one_of_orderOf_eq_two ht
  set V : Subgroup G := centD H t with hV
  have hVH : V ≤ H := by
    rw [hV, centD]
    exact le_trans inf_le_left inf_le_left
  have hVt : V ≤ conj t H := by
    rw [hV, centD]
    exact le_trans inf_le_left inf_le_right
  have hmem1 : ((1 : G) : G ⧸ H) ∈ fixedPts H V := by
    rw [mem_fixedPts_iff_le_stabilizer, stabilizer_mk, conj_one]
    exact hVH
  have hmemt : (t : G ⧸ H) ∈ fixedPts H V := by
    rw [mem_fixedPts_iff_le_stabilizer, stabilizer_mk]
    exact hVt
  obtain ⟨ω, hω⟩ := Set.ncard_eq_one.mp (ncard_fixedPts_zpowers hH ht)
  have hmemω : ω ∈ fixedPts H V := by
    rw [mem_fixedPts_iff_le_stabilizer]
    intro v hv
    rw [MulAction.mem_stabilizer_iff]
    have hvC : v ∈ Subgroup.centralizer ({t} : Set G) := by
      rw [hV, centD] at hv
      exact (Subgroup.mem_inf.mp hv).2
    have hvt : v * t = t * v := Subgroup.mem_centralizer_singleton_iff.mp hvC
    have htω : t • ω = ω := by
      have hmem : ω ∈ fixedPts H (Subgroup.zpowers t) := by rw [hω]; exact Set.mem_singleton ω
      exact mem_fixedPts.mp hmem t (Subgroup.mem_zpowers t)
    have htvω : t • (v • ω) = v • ω := by rw [← mul_smul, ← hvt, mul_smul, htω]
    have hmem : v • ω ∈ fixedPts H (Subgroup.zpowers t) := by
      rw [mem_fixedPts_iff_le_stabilizer, Subgroup.zpowers_le, MulAction.mem_stabilizer_iff]
      exact htvω
    rw [hω] at hmem
    simpa using hmem
  have h1t : ((1 : G) : G ⧸ H) ≠ (t : G ⧸ H) := by
    intro hcon
    rw [QuotientGroup.eq] at hcon
    exact htH (by simpa using hcon)
  have h1notmem : ((1 : G) : G ⧸ H) ∉ fixedPts H (Subgroup.zpowers t) := by
    intro hmem
    have h := mem_fixedPts.mp hmem t (Subgroup.mem_zpowers t)
    have h' : ((1 : G) : G ⧸ H) = (t : G ⧸ H) := by simpa [smul_mk] using h.symm
    exact h1t h'
  have h1ω : ((1 : G) : G ⧸ H) ≠ ω := by
    intro hcon
    have hmem : ω ∈ fixedPts H (Subgroup.zpowers t) := by rw [hω]; exact Set.mem_singleton ω
    rw [← hcon] at hmem
    exact h1notmem hmem
  have htnotmem : (t : G ⧸ H) ∉ fixedPts H (Subgroup.zpowers t) := by
    intro hmem
    have h := mem_fixedPts.mp hmem t (Subgroup.mem_zpowers t)
    have h' : ((1 : G) : G ⧸ H) = (t : G ⧸ H) := by simpa [smul_mk, ht2] using h
    exact h1t h'
  have htω : (t : G ⧸ H) ≠ ω := by
    intro hcon
    have hmem : ω ∈ fixedPts H (Subgroup.zpowers t) := by rw [hω]; exact Set.mem_singleton ω
    rw [← hcon] at hmem
    exact htnotmem hmem
  have hsub : ({((1 : G) : G ⧸ H), (t : G ⧸ H), ω} : Set (G ⧸ H)) ⊆ fixedPts H V := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact hmem1
    · exact hmemt
    · exact hmemω
  have hcard : ({((1 : G) : G ⧸ H), (t : G ⧸ H), ω} : Set (G ⧸ H)).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by simp [h1t, h1ω]),
      Set.ncard_insert_of_notMem (by simp [htω]), Set.ncard_singleton]
  calc 3 = _ := hcard.symm
    _ ≤ (fixedPts H V).ncard := Set.ncard_le_ncard hsub

/-- `3 ≤ |fixedPts H X|` for `X ≤ centD H t`. -/
theorem three_le_ncard_fixedPts_of_le_centD {H : Subgroup G} (hH : IsStronglyEmbedded H) {t : G}
    (ht : orderOf t = 2) (htH : t ∉ H) {X : Subgroup G} (hX : X ≤ centD H t) :
    3 ≤ (fixedPts H X).ncard :=
  le_trans (three_le_ncard_fixedPts_centD hH ht htH) (Set.ncard_mono (fixedPts_mono hX))

/-! ## Prop. 1 (a) ⟹ Prop. 1 (b)

(Transferred from `Work.ThreePoints.P3NeBot.prop1b_brsz` — same proof, but callable from a module
whose closure has no `hole`.) -/

/-- If `Inv C_G(X) ⊆ F` and `|M ⊓ C_G(X)|` is even, then `|F ⊓ M|` is even. -/
theorem even_card_inf_of_even_card_inf_centralizer {X F M : Subgroup G}
    (hev : Even (Nat.card (M ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)))
    (hFX : involutions (Subgroup.centralizer (X : Set G) : Set G) ⊆ F) :
    Even (Nat.card (F ⊓ M : Subgroup G)) := by
  obtain ⟨u, hu, hu2⟩ := exists_orderOf_two_of_even_card hev
  have huF : u ∈ F := hFX ⟨hu.2, hu2⟩
  have huFM : u ∈ F ⊓ M := ⟨huF, hu.1⟩
  have hdvd : Nat.card (Subgroup.zpowers u : Subgroup G) ∣ Nat.card (F ⊓ M : Subgroup G) :=
    Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr huFM)
  rw [even_iff_two_dvd]
  rwa [Nat.card_zpowers, hu2] at hdvd

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
  have hev : Even (Nat.card (F ⊓ conj g H : Subgroup G)) :=
    even_card_inf_of_even_card_inf_centralizer (hEV hX3 ⟨g, rfl⟩ hg) hFX
  have hproper : (F ⊓ conj g H).subgroupOf F ≠ ⊤ := by
    obtain ⟨g', hfix, hne_pt⟩ := exists_mk_fixedPts_ne (H := H) (X := X) (g := g) hX3
    have hXg' : X ≤ conj g' H := by
      rw [← stabilizer_mk H g']
      exact mem_fixedPts_iff_le_stabilizer.mp hfix
    have hconjne : conj g H ≠ conj g' H := by
      intro heq
      exact hne_pt (mk_eq_of_conj_eq hH heq.symm)
    obtain ⟨u, hu, hu2⟩ := exists_orderOf_two_of_even_card (hEV hX3 ⟨g', rfl⟩ hXg')
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
  exact IsStronglyEmbedded.subgroupOf_inf hM hproper hev

end Work.ThreePoints.P3NeBot
