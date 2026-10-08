import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.API
import Submission.Work.CORE2B.L27_solvable_base
import Submission.Work.CORE2B.L27_step1_leaf
import Submission.Work.CORE2B.L27_two_part_centralized_proved
import Submission.Work.CORE2B.L27_conj_t_inverts
import Submission.Work.CORE2B.L27_pi_subgroup_in_fittingPi
import Submission.Work.CORE2B.L27cf_twoResidual
import Submission.Work.CORE2B.L27_centralizes_fitting_crux
import Submission.Work.CORE2B.L27_crux_commutator_2prime
import Submission.Work.CORE2B.layer_eq_bot_of_normal_contains_t
import Submission.Work.CORE2B.L27_commutator_le_of_odd_crux
import Submission.Work.CORE2B.L27_fittingPiIn_le_iSup_singleton

/-!
# `Work.CORE2B.L27_commutator_le` — Bender 1981, Lemma 2.7 (a): `⁅M,t⁆ ≤ F_{π'}(M)`

This file assembles the leaf `Work.CORE2B.L27_commutator_le` from the pieces of Bender's
proof that are already available, sorry-free, in the area:

* `L27fin_pi_centralized` — `t` centralizes `F_π(M)` (Lemma 2.3.i plus `t ∈ O₂(Ĥ)`);
* `L27fin_cent` — `⁅M,t⁆ ≤ C_M(F(M))` (`L27_centralizes_fitting_crux`);
* `L27fin_KF` — `⁅M,t⁆ ≤ F(M)` (`E(M) = 1` from step 1 via
  `layer_eq_bot_of_normal_contains_t`, plus `C_M(F(M)) ≤ F(M)` = Bender 1.2);
* `L27fin_odd_of_O2_bot` — `O₂(M) = ⊥` gives `Odd |⁅M,t⁆|`.

Bender's remaining step is "hence `O₂(M) ⊆ O₂(Ĥ)`, hence `O₂(M) = 1` (otherwise,
`N_G(O₂(M)) ⊄ Ĥ`)" (p. 221): the maximality of `Ĥ` turns `O₂(M) ⊴ Ĥ` into `O₂(M) ⊴ G`.
`L27fin_O2_eq_bot` records the coatom/simplicity half of that argument, so that once
`O₂(M) ⊴ Ĥ` is supplied the leaf follows.

The final `π`-refinement is `L27_commutator_le_of_odd_crux` (proved).
-/

open scoped MatrixGroups commutatorElement

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.CORE2B

open Subgroup

/-! ## 1. `t` centralizes `F_π(M)` (Bender: "`t` centralizes `F_π(M)`") -/

theorem L27fin_pi_centralized {G : Type} [Group G] [Finite G]
    (T : Work.GW2.LocalToolkit) (h23 : Work.GW2.Lemma23Prop) (h26 : Work.GW2.Thm26Prop)
    (hFT : Work.GW2.FeitThompsonProp) (hCtx : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (M : Subgroup G) (hD : L27Hyp B M) :
    Work.GW2.fittingPiIn B.pi M ≤ Subgroup.centralizer ({B.t} : Set G) := by
  -- the odd part `F_{π ∩ {2}ᶜ}(M)` of `F_π(M)` is centralized (Lemma 2.3.i)
  have hodd : Work.GW2.fittingPiIn (B.pi ∩ ({2}ᶜ : Set ℕ)) M ≤
      Subgroup.centralizer ({B.t} : Set G) :=
    L27cff_centralizes_odd_pi_part G hFT hCtx B M hD h23 h26
  -- the `2`-part `F₂(M) ≤ O₂(M) ≤ C(t)` (Bender's step 1)
  have htwo : Work.GW2.fittingPiIn ({2} : Set ℕ) M ≤ Subgroup.centralizer ({B.t} : Set G) :=
    L27cff_two_part_centralized T h23 h26 G hFT hCtx B M hD
  -- assemble over the primes of `π`
  refine (L27_fittingPiIn_le_iSup_singleton B.pi M).trans ?_
  refine iSup_le fun q => iSup_le fun hq => ?_
  by_cases hq2 : q = 2
  · subst hq2
    exact htwo
  · refine (fittingPiIn_mono' (K := M) ?_).trans hodd
    intro r hr
    rw [Set.mem_singleton_iff] at hr
    subst hr
    exact ⟨hq, by simpa using hq2⟩

/-! ## 2. `⁅M,t⁆ ≤ C_M(F(M)) ⊆ F(M)` -/

/-- `⁅M,t⁆ ≤ C_M(F(M))` (Bender: "Now `[M,t] ⊆ C_M(F(M))`"). -/
theorem L27fin_cent {G : Type} [Group G] [Finite G]
    (T : Work.GW2.LocalToolkit) (h23 : Work.GW2.Lemma23Prop) (h26 : Work.GW2.Thm26Prop)
    (hFT : Work.GW2.FeitThompsonProp) (hCtx : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (M : Subgroup G) (hD : L27Hyp B M) :
    ⁅M, Subgroup.zpowers B.t⁆ ≤
      Subgroup.centralizer ((Work.GW2.fittingIn M : Subgroup G) : Set G) :=
  L27_centralizes_fitting_crux T h23 h26 G hFT hCtx B M hD

/-- `⁅M,t⁆ ≤ F(M)` (Bender: "`[M,t] ⊆ C_M(F(M)) ≤ F(M)`"). -/
theorem L27fin_KF {G : Type} [Group G] [Finite G]
    (T : Work.GW2.LocalToolkit) (h23 : Work.GW2.Lemma23Prop) (h26 : Work.GW2.Thm26Prop)
    (hFT : Work.GW2.FeitThompsonProp) (hCtx : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (M : Subgroup G) (hD : L27Hyp B M) :
    ⁅M, Subgroup.zpowers B.t⁆ ≤ Work.GW2.fittingIn M := by
  -- Bender: "Hence `E(M) = 1`"
  have hlayer : Work.GW2.layerIn M = ⊥ :=
    layer_eq_bot_of_normal_contains_t L27_step1_leaf T h23 h26 G hFT hCtx B M hD
  -- `C_M(F(M)) ⊓ M ≤ F(M)` (Bender 1.2 for the D-group `↥M`, with `E(M) = 1`)
  have hfM := centralizer_fittingIn_inf_le_fitting T hFT hCtx B M hD hlayer
  have hcent := L27fin_cent T h23 h26 hFT hCtx B M hD
  -- `⁅M,t⁆ ≤ M`
  have hKM : ⁅M, Subgroup.zpowers B.t⁆ ≤ M := by
    rw [Subgroup.commutator_le]
    intro m hm y hy
    have hyM : y ∈ M := (Subgroup.zpowers_le.mpr hD.t_mem) hy
    rw [commutatorElement_def]
    exact M.mul_mem (M.mul_mem (M.mul_mem hm hyM) (M.inv_mem hm)) (M.inv_mem hyM)
  exact (le_inf hcent hKM).trans hfM

/-! ## 3. `O₂(M) = ⊥` gives the oddness of `⁅M,t⁆` -/

/-- If `O₂(M) = ⊥` then `⁅M,t⁆` has odd order: `⁅M,t⁆ ≤ F(M) = F_{2'}(M)`, and `F_{2'}(M)` is
odd.  (The `2`-part of `F(M)` is `O₂(M) = F₂(M)`, and `F(M)` is the supremum of its `π`-parts.) -/
theorem L27fin_odd_of_O2_bot {G : Type} [Group G] [Finite G]
    (T : Work.GW2.LocalToolkit) (h23 : Work.GW2.Lemma23Prop) (h26 : Work.GW2.Thm26Prop)
    (hFT : Work.GW2.FeitThompsonProp) (hCtx : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (M : Subgroup G) (hD : L27Hyp B M)
    (hO2 : Work.GW2.pCoreIn 2 M = ⊥) :
    Odd (Nat.card (⁅M, Subgroup.zpowers B.t⁆ : Subgroup G)) := by
  -- `F₂(M) = O₂(F(M)) ≤ O₂(M) = ⊥`
  have hF2 : Work.GW2.fittingPiIn ({2} : Set ℕ) M = ⊥ :=
    le_bot_iff.mp ((L27cff_fittingPiIn_two_le_pCoreIn_two (G := G) M).trans (le_of_eq hO2))
  -- `F(M) ≤ F₂(M) ⊔ F_{2'}(M) ⊔ F_{2'}(M)`
  have hdec : Work.GW2.fittingIn M ≤
      Work.GW2.fittingPiIn ({2} : Set ℕ) M ⊔
        Work.GW2.fittingPiIn ({2}ᶜ : Set ℕ) M ⊔ Work.GW2.fittingPiIn ({2}ᶜ : Set ℕ) M :=
    L27cff_fittingIn_le_sup_three M (fun q _ => by
      by_cases h : q = 2
      · exact Or.inl (by rw [h]; exact Set.mem_singleton 2)
      · exact Or.inr (Or.inl (by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact h)))
  have hFbot : Work.GW2.fittingPiIn ({2}ᶜ : Set ℕ) M = Work.GW2.fittingIn M := by
    refine le_antisymm ?_ ?_
    · exact Subgroup.map_mono (Subgroup.map_subtype_le _)
    · refine hdec.trans ?_
      rw [hF2]
      simp
  -- `⁅M,t⁆ ≤ F_{2'}(M)` has odd order
  have hoddF : Odd (Nat.card (Work.GW2.fittingPiIn ({2}ᶜ : Set ℕ) M)) :=
    L27cff_odd_card_fittingPiIn_of_subset_compl (G := G) (σ := ({2}ᶜ : Set ℕ))
      (subset_refl _) M
  have hle : ⁅M, Subgroup.zpowers B.t⁆ ≤ Work.GW2.fittingPiIn ({2}ᶜ : Set ℕ) M := by
    rw [hFbot]
    exact L27fin_KF T h23 h26 hFT hCtx B M hD
  exact hoddF.of_dvd_nat (Subgroup.card_dvd_of_le hle)

/-! ## 4. Bender's coatom argument: `O₂(M) ⊴ Ĥ` forces `O₂(M) = ⊥` -/

/-- The `Ĥ`-maximality half of Bender's "hence `O₂(M) ⊆ O₂(Ĥ)`, hence `O₂(M) = 1`": if
`O₂(M) ⊴ Ĥ`, then `M ≤ N_G(O₂(M))` and `Ĥ ≤ N_G(O₂(M))` with `⟨M,Ĥ⟩ = G` give `O₂(M) ⊴ G`, so
`O₂(M) = 1` by simplicity of `G` and `M ≠ ⊤`. -/
theorem L27fin_O2_eq_bot {G : Type} [Group G] [Finite G]
    (T : Work.GW2.LocalToolkit) (h23 : Work.GW2.Lemma23Prop) (h26 : Work.GW2.Thm26Prop)
    (hFT : Work.GW2.FeitThompsonProp) (hCtx : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (M : Subgroup G) (hD : L27Hyp B M)
    (hnorm : B.Hhat ≤
      Subgroup.normalizer ((Work.GW2.pCoreIn 2 M : Subgroup G) : Set G)) :
    Work.GW2.pCoreIn 2 M = ⊥ := by
  -- `O₂(M) ⊴ M`
  have hMle : M ≤ Subgroup.normalizer ((Work.GW2.pCoreIn 2 M : Subgroup G) : Set G) := by
    simpa [Work.GW2.pCoreIn] using
      le_normalizer_map_subtype_local M (Work.GW2.pCore 2 ↥M) (Work.GW2.pCore_normal 2 ↥M)
  -- `⟨M, Ĥ⟩ = ⊤`, because `Ĥ` is a coatom and `M ≰ Ĥ`
  have hsup : M ⊔ B.Hhat = ⊤ := by
    have hlt : B.Hhat < M ⊔ B.Hhat := by
      refine lt_of_le_of_ne le_sup_right ?_
      intro h
      exact hD.not_le (le_sup_left.trans (le_of_eq h.symm))
    exact B.Hhat_coatom.2 (M ⊔ B.Hhat) hlt
  -- so `O₂(M)` is normalized by `G`
  have hG : (⊤ : Subgroup G) ≤
      Subgroup.normalizer ((Work.GW2.pCoreIn 2 M : Subgroup G) : Set G) := by
    rw [← hsup]
    exact sup_le hMle hnorm
  haveI : (Work.GW2.pCoreIn 2 M).Normal :=
    ⟨fun n hn g => (Subgroup.mem_normalizer_iff.mp (hG (Subgroup.mem_top g)) n).mp hn⟩
  -- simplicity of `G`
  rcases hCtx.simple.eq_bot_or_eq_top_of_normal (Work.GW2.pCoreIn 2 M) with h | h
  · exact h
  · exfalso
    have hcard1 : Nat.card ↥(Work.GW2.pCoreIn 2 M) = Nat.card G := by
      rw [h, Subgroup.card_top]
    have hcard2 : Nat.card ↥(Work.GW2.pCoreIn 2 M) ≤ Nat.card M := by
      rw [Work.GW2.pCoreIn]
      exact Subgroup.card_le_of_le (Subgroup.map_subtype_le _)
    have hlt : Nat.card M < Nat.card G := by
      have hlt' : M < ⊤ := lt_of_le_of_ne le_top hD.M_ne_top
      simpa [Subgroup.card_top] using Subgroup.card_lt_of_lt (K := (⊤ : Subgroup G)) hlt'
    omega

/-! ## 5. The target -/

/-- **Reduction (verified, sorry-free):** the leaf follows from `O₂(M) = ⊥`.

Indeed `O₂(M) = ⊥` gives `⁅M,t⁆ ≤ F(M) = F_{2'}(M)`, hence `Odd |⁅M,t⁆|` (Section 3), and then the
`π`-refinement `L27_commutator_le_of_odd_crux` yields `⁅M,t⁆ ≤ F_{π'}(M)`. -/
theorem L27_commutator_le_of_O2_bot {G : Type} [Group G] [Finite G]
    (T : Work.GW2.LocalToolkit) (h23 : Work.GW2.Lemma23Prop) (h26 : Work.GW2.Thm26Prop)
    (hFT : Work.GW2.FeitThompsonProp) (hCtx : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (M : Subgroup G) (hD : L27Hyp B M)
    (hO2 : Work.GW2.pCoreIn 2 M = ⊥) :
    ⁅M, Subgroup.zpowers B.t⁆ ≤ Work.GW2.fittingPiIn B.piᶜ M :=
  L27_commutator_le_of_odd_crux h23 hFT hCtx B M hD
    (L27fin_pi_centralized T h23 h26 hFT hCtx B M hD)
    (L27fin_cent T h23 h26 hFT hCtx B M hD)
    (L27fin_KF T h23 h26 hFT hCtx B M hD)
    (L27fin_odd_of_O2_bot T h23 h26 hFT hCtx B M hD hO2)

/-! **Note.**  The theorem `L27_commutator_le_final` that used to stand here was a proof of the
leaf `L27_commutator_le` with a `sorry` for Bender's step (4); it has been removed so that no
`sorry`-tainted proof of a CORE2B deliverable circulates.  The real proof is assembled in
`Submission/Work/CORE2B/L27_v12_assembly.lean` from the leaves of the lead's design pass 12
(`c11iv_nilpotent`, `L27v12_selfcent`, `L27v12_O2_centralizes_fittingU`,
`L27v12_eq_bot_of_le_pCoreIn_Hhat`). -/

end Work.CORE2B
