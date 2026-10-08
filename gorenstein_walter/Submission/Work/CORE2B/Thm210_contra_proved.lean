import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.API
import Submission.Work.CORE2B.fittingIn_U_normalizer
import Submission.Work.CORE2B.Thm210_hall_and_normal
import Submission.Work.CORE2B.Core18OwedBad

/-!
# AREA CORE2B — Theorem 2.10 of Bender (1981), contradiction form

The leaf `Work.CORE2B.Thm210_contra`: under `BenderCtx G` and the toolkit, if both cases of
Bender's Theorem 2.10 fail then `False`.

## Structure of the proof (Bender, pp. 221–222)

Write `F = O(C_G(t)) = B.U`, `F(U) = fittingIn B.U`, `Ĥ = B.Hhat`.

* **`U = ⊥`** (`case1_of_U_eq_bot`): then `F(U) = ⊥`, the set `I_U(s) = {1} = ⊥` is a Hall
  subgroup of `⊥`, and case (1) holds vacuously.  Contradiction with `¬ Case1`.
* **`U ≠ ⊥`**: `F(U) ≠ ⊥`, `F(U) ⊴ Ĥ`, `N_G(F(U)) = Ĥ` and `F(U) ≤ F(Ĥ)` — all from
  Theorem 2.6 (`h26`, which gives `O(Ĥ) = U`) plus `F(U) char U ⊴ Ĥ` (`owed_fittingIn_facts`).
  * If `t ∈ E(Ĥ)` (`case2_of_mem_layer_Hhat`): case (2) holds with `M = Ĥ` and `X = F(U)`,
    since `N_G(F(U)) = Ĥ`.  Contradiction with `¬ Case2`.
  * If `t ∉ E(Ĥ)`: we show `Case1`, contradicting `¬ Case1`.  Its first conjunct (the Hall
    property of `I_U(s)`, `s ∈ S − S₀`) is Bender's *first half* (`owed_hall`); for the second
    conjunct, given `1 ≠ X ≤ F(U)` with `N_G(X) ≰ Ĥ`, a coatom `M ≥ ⟨N_G(X), S⟩` gives
    `Ĥ ⇝ M` (witnessed by `X ≤ F(U) ≤ F(Ĥ)`) and Lemma 2.8 (`h28`) yields `t ∈ E(M)`, i.e.
    case (2) (`case2_of_not_normalizer_le_good`), contradiction with `¬ Case2`.
    That such a coatom exists unless `N_G(X) ⊔ S = ⊤`; the remaining *bad* configuration is
    `owed_bad` (Bender's argument supplies no `M` there — see the notes in the discussion).

## Status

* Bender's **first half** is proved in the sibling module
  `Work.CORE2B.Thm210_hall_and_normal` (per-prime dichotomy `HallPerPrime` + the group-theoretic
  reduction `InvSetHallStructure`): for `s ∈ S − S₀`, `I_U(s)` is the carrier of a subgroup of `U`
  normal in `U` and Hall in `F(U)`.
* The `F(U)`-facts (`F(U) ≠ ⊥`, `N_G(F(U)) = Ĥ`, `F(U) ≤ F(Ĥ)`) are proved in the sibling module
  `Work.CORE2B.fittingIn_U_normalizer`.
* The remaining obligation is `owed_bad`: the *bad* configuration, where no coatom containing
  `N_G(X)` also contains `S`, equivalently `N_G(X) ⊔ S = ⊤`.  There the `S`-closure
  `Y = ⟨X^S⟩ ≤ F(U)` of `X` should be normal in `G = ⟨N_G(X), S⟩` (whence `Y = ⊤` by simplicity,
  contradicting `Y ≤ U ≤ Ĥ ≠ ⊤`), so case (2) holds.  The needed group-theoretic input
  (`N_G(X)` permutes the `S`-conjugates of `X`) is Bender's own use of `T.fus` and is isolated
  in the sibling module `Work.CORE2B.Thm210_bad_normalizer`.
-/

open scoped MatrixGroups

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.CORE2B

open Subgroup

variable {G : Type} [Group G] [Finite G]

/-! ## The trivial case `U = ⊥` -/

/-- `F(U) = ⊥` when `U = ⊥`. -/
theorem fittingIn_eq_bot_of_U_eq_bot (B : Work.GW2.BenderSetup G) (hU : B.U = ⊥) :
    Work.GW2.fittingIn B.U = ⊥ := by
  have hbot : Work.GW2.fitting ↥(⊥ : Subgroup G) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x _
    exact Subsingleton.elim x 1
  rw [hU, Work.GW2.fittingIn, hbot, Subgroup.map_bot]

/-- `U = ⊥` gives case (1) of Bender's Theorem 2.10. -/
theorem case1_of_U_eq_bot (B : Work.GW2.BenderSetup G) (hU : B.U = ⊥) : Work.GW2.Case1 B := by
  have hfib : Work.GW2.fittingIn B.U = ⊥ := fittingIn_eq_bot_of_U_eq_bot B hU
  constructor
  · intro s _ _
    refine ⟨⊥, ?_, ?_⟩
    · ext x
      constructor
      · intro hx
        have hx1 : x = 1 := by simpa using hx
        subst hx1
        exact ⟨by simp [hU], by simp⟩
      · intro hx
        have hxU : x ∈ B.U := hx.1
        rw [hU] at hxU
        simpa using hxU
    · rw [hfib]
      refine ⟨bot_le, ?_⟩
      simp [Subgroup.relIndex]
  · intro X hX hXle
    exact absurd (le_bot_iff.mp (by rw [hfib] at hXle; exact hXle)) hX

/-! ## The case `t ∈ E(Ĥ)` -/

/-- If `t ∈ E(Ĥ)` then case (2) holds, with `M = Ĥ` and `X = F(U)`. -/
theorem case2_of_mem_layer_Hhat (B : Work.GW2.BenderSetup G)
    (hFne : Work.GW2.fittingIn B.U ≠ ⊥)
    (hFnorm : Subgroup.normalizer (Work.GW2.fittingIn B.U : Set G) = B.Hhat)
    (htE : B.t ∈ Work.GW2.layerIn B.Hhat) : Work.GW2.Case2 B :=
  ⟨B.Hhat, B.Hhat_coatom, htE, Work.GW2.fittingIn B.U, hFne, le_rfl, hFnorm.le⟩

/-! ## The second half, "good" configuration -/

/-- **Bender's second half, good configuration.**  If a coatom `M` contains both `N_G(X)` and
`S`, and `I_U(s) ⊴ U` for every `s ∈ S − S₀` (Bender's Lemma 2.8 hypothesis), then case (2)
holds. -/
theorem case2_of_not_normalizer_le_good (h28 : Work.GW2.Lemma28Prop)
    (hFT : Work.GW2.FeitThompsonProp) (hCtx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G)
    (hInv : ∀ s ∈ (B.S : Subgroup G), s ∉ B.S0 →
      ∃ I : Subgroup G, (I : Set G) = Work.GW2.invSet B.U s ∧ (I.subgroupOf B.U).Normal)
    (hFle : Work.GW2.fittingIn B.U ≤ Work.GW2.fittingIn B.Hhat)
    (X : Subgroup G) (hXne : X ≠ ⊥) (hXle : X ≤ Work.GW2.fittingIn B.U)
    (hXnorm : ¬ Subgroup.normalizer (X : Set G) ≤ B.Hhat)
    (M : Subgroup G) (hM : IsCoatom M) (hNM : Subgroup.normalizer (X : Set G) ≤ M)
    (hSM : (B.S : Subgroup G) ≤ M) : Work.GW2.Case2 B := by
  have hrel : Work.GW2.BRel B.Hhat M :=
    ⟨X, le_trans hXle hFle, le_trans inf_le_left hNM⟩
  have hnotle : ¬ M ≤ B.Hhat := fun h => hXnorm (le_trans hNM h)
  have htEM : B.t ∈ Work.GW2.layerIn M :=
    (h28 G hFT hCtx B hInv).2 M hM.ne_top hrel hnotle hSM
  exact ⟨M, hM, htEM, X, hXne, hXle, hNM⟩

/-! ## The three outstanding mathematical inputs -/

/-- **Owed (iii)**: in the *bad* configuration — no coatom contains both `N_G(X)` and `S`, i.e.
`N_G(X) ⊔ S = ⊤` — one still gets case (2). -/
theorem owed_bad (T : Work.GW2.LocalToolkit) (h26 : Work.GW2.Thm26Prop)
    (h27 : Work.GW2.Lemma27Prop) (h28 : Work.GW2.Lemma28Prop) (G : Type) [Group G] [Finite G]
    (hFT : Work.GW2.FeitThompsonProp) (hCtx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G)
    (hnot1 : ¬ Work.GW2.Case1 B) (hnot2 : ¬ Work.GW2.Case2 B)
    (X : Subgroup G) (hXne : X ≠ ⊥) (hXle : X ≤ Work.GW2.fittingIn B.U)
    (hXnorm : ¬ Subgroup.normalizer (X : Set G) ≤ B.Hhat)
    (hbad : ∀ M : Subgroup G, IsCoatom M → Subgroup.normalizer (X : Set G) ≤ M →
      ¬ (B.S : Subgroup G) ≤ M) : Work.GW2.Case2 B :=
  Work.GW18.Core18OwedBad T h26 h27 h28 G hFT hCtx B hnot1 hnot2 X hXne hXle hXnorm hbad

/-! ## Theorem 2.10, contradiction form -/

theorem Thm210_contra_proved : Work.CORE2B.Thm210_contra := by
  intro T h26 h27 h28 G _ _ hFT hCtx B hnot1 hnot2
  by_cases hU : B.U = ⊥
  · exact hnot1 (case1_of_U_eq_bot B hU)
  · obtain ⟨hFne, hFnorm, hFle⟩ := fittingIn_U_normalizer h26 G hFT hCtx B hU
    have hHallW : ∀ s ∈ (B.S : Subgroup G), s ∉ B.S0 → ∃ I : Subgroup G,
        (I : Set G) = Work.GW2.invSet B.U s ∧
          Work.GW2.IsHallIn I (Work.GW2.fittingIn B.U) ∧ (I.subgroupOf B.U).Normal :=
      fun s hs hs0 => Thm210_hall_and_normal T h26 h27 h28 G hFT hCtx B hnot1 hnot2 s hs hs0
    have hHall : ∀ s ∈ (B.S : Subgroup G), s ∉ B.S0 → ∃ I : Subgroup G,
        (I : Set G) = Work.GW2.invSet B.U s ∧ Work.GW2.IsHallIn I (Work.GW2.fittingIn B.U) :=
      fun s hs hs0 => ⟨(hHallW s hs hs0).choose, (hHallW s hs hs0).choose_spec.1,
        (hHallW s hs hs0).choose_spec.2.1⟩
    have hInv : ∀ s ∈ (B.S : Subgroup G), s ∉ B.S0 →
        ∃ I : Subgroup G, (I : Set G) = Work.GW2.invSet B.U s ∧ (I.subgroupOf B.U).Normal :=
      fun s hs hs0 => ⟨(hHallW s hs hs0).choose, (hHallW s hs hs0).choose_spec.1,
        (hHallW s hs hs0).choose_spec.2.2⟩
    by_cases htE : B.t ∈ Work.GW2.layerIn B.Hhat
    · exact hnot2 (case2_of_mem_layer_Hhat B hFne hFnorm htE)
    · have hb : ∀ X : Subgroup G, X ≠ ⊥ → X ≤ Work.GW2.fittingIn B.U →
          Subgroup.normalizer (X : Set G) ≤ B.Hhat := by
        intro X hXne hXle
        by_contra hXnorm
        by_cases hgood : ∃ M : Subgroup G, IsCoatom M ∧ Subgroup.normalizer (X : Set G) ≤ M ∧
            (B.S : Subgroup G) ≤ M
        · obtain ⟨M, hM, hNM, hSM⟩ := hgood
          exact hnot2 (case2_of_not_normalizer_le_good h28 hFT hCtx B hInv hFle X hXne hXle
            hXnorm M hM hNM hSM)
        · exact hnot2 (owed_bad T h26 h27 h28 G hFT hCtx B hnot1 hnot2 X hXne hXle hXnorm
            (fun M hM hNM hSM => hgood ⟨M, hM, hNM, hSM⟩))
      exact hnot1 ⟨hHall, hb⟩

end Work.CORE2B
