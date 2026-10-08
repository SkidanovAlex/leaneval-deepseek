/-
# `Work.ThreePoints.ThmC.Crux` — assembly of Theorem C from the §3 "Steps 1–3" input

This file isolates the *outer* part of the proof of Peterfalvi's Theorem C (Ch. II §3): given the
existence of a suitable subgroup `A` of the two-point stabiliser (Ch. II §3 Steps 1–3), Theorem C
follows from `ch2_sec1_lem1` (§1) and `ch2_sec2_lem2` (§2).

The remaining input `hAexists` is exactly the conclusion of Steps 1–3: for `u ∈ Inv(H)` and
`t ∈ Inv(G∖H)` with `u ∉ C(D ∩ D^u)`, `D = twoPoint H t`, there is `A ≤ D` with `A ≠ ⊥`, `A ⊴ D`,
`u`- and `t`-invariant (with `u` an involution of `H` normalising `A`).
-/
import Mathlib
import Submission.Work.ThreePoints.ThmC.Defs
import Submission.Work.ThreePoints.ThmC.Base
import Submission.Work.ThreePoints.ThmC.ch2_sec1_lem1
import Submission.Work.ThreePoints.ThmC.ch2_sec2_lem2
import Submission.Work.ThreePoints.ch1_lem2

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

/-- **Theorem C from the §3 input.**  If a `u`- and `t`-invariant nontrivial normal subgroup `A` of
a two-point stabiliser `D = H ∩ H^t` always exists when `u ∈ Inv(H)` fails to centralise
`D ∩ D^u`, then `ThmCProp` holds. -/
theorem thmC_of_A (hFT : FeitThompsonProp) (hA : ThmAProp) (hZJ : GlaubermanZJProp)
    (hBrSz : BrauerSuzukiProp) (hMod : ModelFactsProp)
    (hAexists : ∀ {G : Type} [Group G] [Finite G], Situation G → ∀ {H : Subgroup G},
      IsStronglyEmbedded H → ∀ {t u : G}, orderOf t = 2 → t ∉ H →
      u ∈ involutions (H : Set G) →
      (∃ y ∈ twoPoint H t ⊓ conj u (twoPoint H t), u * y ≠ y * u) →
      ∃ A : Subgroup G, A ≤ twoPoint H t ∧ A ≠ ⊥ ∧
        (∀ d ∈ twoPoint H t, conj d A = A) ∧
        (∃ u' ∈ involutions (H : Set G), u' ∈ Subgroup.normalizer (A : Set G)) ∧
        t ∈ Subgroup.normalizer (A : Set G)) :
    ThmCProp := by
  intro G _ _ hSit H hH g hg u hu X hX huN x hx
  have hfour : HasFourGroup G := hSit.1.1
  have hB1 : ThmBBelow (Nat.card G) := hSit.2.1
  have hbot : oddCore G = ⊥ := hSit.2.2
  have h2t : IsTwoTransitiveOn H := hA G hfour H hH
  -- Case: `u` centralises `X`
  by_cases hcent : ∀ x ∈ X, u * x = x * u
  · exact hcent x hx
  · -- otherwise some `x ∈ X` is moved, and `H` has non-commuting involutions
    have hnc : ∃ x ∈ X, u * x ≠ x * u := by
      by_contra h
      exact hcent fun y hy => by
        by_contra hne
        exact h ⟨y, hy, hne⟩
    obtain ⟨u', hu', hnc_uu'⟩ := ch2_sec1_lem1 hH hg hX hu huN hnc
    -- choose `t ∈ Inv(G∖H)` with `H^t = H^g`
    have hne_one : conj (1 : G) H ≠ conj g H := by
      rw [conj_one]
      intro h
      have hmem : g ∈ Subgroup.normalizer (H : Set G) :=
        (Work.DoubleTransitivity.conj_eq_self_iff_mem_normalizer g H).mp h.symm
      rw [Work.ThreePoints.IsStronglyEmbedded.normalizer_eq hH] at hmem
      exact hg hmem
    obtain ⟨t, ht, htconj⟩ := Work.ThreePoints.exists_involution_conj_of_even_card_inf (F := ⊤) hH
      hne_one (by simpa using IsStronglyEmbedded.even_card hH)
      (by simpa using IsStronglyEmbedded.even_card (conj_stronglyEmbedded hH g))
    rw [conj_one] at htconj
    have ht2 : orderOf t = 2 := ht.2
    rw [conj_one] at hne_one
    have htH : t ∉ H := by
      intro hmem
      rw [conj_eq_self_of_mem hmem] at htconj
      exact hne_one htconj
    -- `X ≤ D ⊓ D^u`, so `u` does not centralise `D ⊓ D^u`
    have hX_D : X ≤ twoPoint H t := by
      rw [twoPoint_eq, htconj]
      exact hX
    have hX_Du : X ≤ conj u (twoPoint H t) := by
      have h1 : conj u X = X :=
        (Work.DoubleTransitivity.conj_eq_self_iff_mem_normalizer u X).mpr huN
      rw [← h1]
      exact Subgroup.map_mono hX_D
    have hnc_D : ∃ y ∈ twoPoint H t ⊓ conj u (twoPoint H t), u * y ≠ y * u := by
      obtain ⟨y, hyX, hy⟩ := hnc
      exact ⟨y, ⟨hX_D hyX, hX_Du hyX⟩, hy⟩
    -- Steps 1–3 provide `A`
    obtain ⟨A, hAle, hAne, hAnorm, ⟨u'', hu'', hu''N⟩, htN⟩ :=
      hAexists hSit hH ht2 htH hu hnc_D
    -- Ch. II §2 Lemma 2 contradicts `O_{2'}(G) = ⊥`
    have hcontra : oddCore G ≠ ⊥ := ch2_sec2_lem2 (G := G) hB1 hMod hfour hH h2t ht2 htH hAle
      hAnorm hAne htN ⟨u'', hu'', hu''N⟩ ⟨u, u', hu, hu', hnc_uu'⟩
    exact (hcontra hbot).elim

end Work.ThreePoints.ThmC
