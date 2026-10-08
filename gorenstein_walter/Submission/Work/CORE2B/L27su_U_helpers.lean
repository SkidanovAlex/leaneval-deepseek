import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.API
import Submission.Work.CORE2B.oddCore_odd
import Submission.Work.CORE2B.isPGroup_pCoreIn_two
import Submission.Work.CORE2B.isQuasisimple_four_dvd
import Submission.Work.CORE2B.L27_su_not_le_h22_proved
import Submission.Work.CORE2B.L27su_hnot
import Submission.Work.CORE2B.UNeBotProp_of_h22_proved
import Submission.Work.CORE2B.fittingIn_U_normalizer
-- RETIRED STUB (on disk for reference only; NOT on the delivered path): the declaration this
-- module was created for is retired because the hypothesis `O₂(M) ≤ C_G(F(U))` (Bender's `M ∩ F(U)`) is missing from `L27Hyp`: one hypothesis short as written.
-- Its corrected form, the reason, and the counterexample configuration are recorded in the
-- `RETIRED` block below and in `Submission/Work/CORE2B/NOTES_FALSE_L27su_two_core_centralizes_U.md`.
-- Nothing in the delivered closure of `Work.CORE2B.Proved` / `L27su_assembly` /
-- `L29_lemma_assembly` / `Thm210_assembly` imports this module.

/-!
# CORE2B — `[O₂(M), U] = 1` in the corrected (hypothesis-carrying) form

* `L27su_odd_card_U` — `U` has odd order; `L27su_layer_U_eq_bot` — `E(U) = 1`;
* `L27su_centralizer_fittingIn_U_le` — `C_U(F(U)) ≤ F(U)` (Bender 1.2 for the `D`-group `U`);
* `L27su_commutator_eq_bot_of_centralizes_fitting_U` — Bender 1.1(iv) with `K = U`, `K₀ = F(U)`:
  from `O₂(M) ≤ C_G(t)` and `O₂(M) ≤ C_G(F(U))`, conclude `⁅O₂(M), U⁆ = ⊥`.

These declarations used to live in `Submission/Work/CORE2B/L27su_two_core_centralizes_U.lean`, which is
kept on disk as a retired stub (its target `L27su_two_core_centralizes_U` is one hypothesis short:
the source's `F(U) ≤ M`).  They were moved here so that the retired stub is imported by nothing on
the delivered path.

Consumers: `Submission/Work/CORE2B/L27_v12_assembly.lean`,
`Submission/Work/CORE2B/L27su_two_core_eq_bot.lean`.
-/

open scoped MatrixGroups commutatorElement

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.CORE2B

open Subgroup

/-- `↥U` has odd order (`U = O(C_G(t))`). -/
theorem L27su_odd_card_U {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G) :
    Odd (Nat.card ↥B.U) := by
  rw [Work.GW2.BenderSetup.U, Work.GW2.oddCoreIn,
    Subgroup.card_map_of_injective B.H.subtype_injective]
  exact oddCore_odd (G := ↥B.H)

/-- `E(U) = 1`: `U` has odd order, while a nontrivial quasisimple group has order divisible
by `4`. -/
theorem L27su_layer_U_eq_bot {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G) :
    Work.GW2.layer ↥B.U = ⊥ := by
  have hodd : Odd (Nat.card ↥B.U) := L27su_odd_card_U B
  refine le_bot_iff.mp (sSup_le ?_)
  rintro E ⟨_hEnorm, hEquasi⟩
  by_contra hle
  have hne : E ≠ ⊥ := fun h => hle h.le
  have h4 : 4 ∣ Nat.card E := isQuasisimple_four_dvd (G := ↥B.U) E hEquasi hne
  have hdvd : 4 ∣ Nat.card ↥B.U := by
    have h1 : Nat.card ↥E ∣ Nat.card ↥(⊤ : Subgroup ↥B.U) :=
      Subgroup.card_dvd_of_le (le_top : E ≤ (⊤ : Subgroup ↥B.U))
    rw [Subgroup.card_top] at h1
    exact h4.trans h1
  exact (Nat.not_even_iff_odd.mpr hodd)
    (even_iff_two_dvd.mpr (dvd_trans (show 2 ∣ 4 by norm_num) hdvd))

/-- `C_U(F(U)) ≤ F(U)`: Bender 1.2 (`LocalToolkit.fstar`) for the `D`-group `U`, together with
`E(U) = 1`. -/
theorem L27su_centralizer_fittingIn_U_le :
    ∀ (T : Work.GW2.LocalToolkit) (G : Type) [Group G] [Finite G],
      Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
      ∀ B : Work.GW2.BenderSetup G,
        B.U ⊓ Subgroup.centralizer ((Work.GW2.fittingIn B.U : Subgroup G) : Set G) ≤
          Work.GW2.fittingIn B.U := by
  intro T G _ _ hFT hCtx B
  have hdih : Work.GW2.DihOrCycSylow ↥B.U := L27su_dihOrCycSylow_subtype hCtx.sylow B.U
  have hUleH : B.U ≤ B.H := Subgroup.map_subtype_le (Work.GW2.oddCore ↥B.H)
  have hUne : B.U ≠ ⊤ := by
    intro htop
    have htop' : (⊤ : Subgroup G) ≤ B.Hhat := htop ▸ (hUleH.trans B.H_le_Hhat)
    exact B.Hhat_coatom.ne_top (le_antisymm le_top htop')
  have hcard : Nat.card ↥B.U < Nat.card G := Subgroup.card_lt_card_of_ne_top hUne
  have hDG : Work.GW2.IsDGroup ↥B.U := hCtx.ih ↥B.U hcard hdih
  have hfstar := T.fstar ↥B.U hFT hdih hDG
  rw [Work.GW2.fstar, L27su_layer_U_eq_bot B, sup_bot_eq] at hfstar
  rintro x hx
  obtain ⟨hxU, hxc⟩ := Subgroup.mem_inf.mp hx
  have hmem : (⟨x, hxU⟩ : ↥B.U) ∈
      Subgroup.centralizer (((Work.GW2.fitting ↥B.U) : Subgroup ↥B.U) : Set ↥B.U) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxc (y : G)
      (Subgroup.mem_map_of_mem B.U.subtype hy))
  exact Subgroup.mem_map_of_mem B.U.subtype (hfstar hmem)

/-- **Bender 1.1(iv) assembly.**  If `O₂(M) ≤ C_G(F(U))` then `⁅O₂(M), U⁆ = ⊥`; this is
Bender's step `[O₂(M), U] = 1` performed with `K = U`, `K₀ = F(U)`. -/
theorem L27su_commutator_eq_bot_of_centralizes_fitting_U :
    ∀ (T : Work.GW2.LocalToolkit) (G : Type) [Group G] [Finite G],
      Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (M : Subgroup G), Work.CORE2B.L27Hyp B M →
        Work.GW2.pCoreIn 2 M ≤ Subgroup.centralizer ({B.t} : Set G) →
        Work.GW2.pCoreIn 2 M ≤
          Subgroup.centralizer ((Work.GW2.fittingIn B.U : Subgroup G) : Set G) →
        ⁅Work.GW2.pCoreIn 2 M, B.U⁆ = ⊥ := by
  intro T G _ _ hFT hCtx B M hD hPC hPCF
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- the `2`-subgroup `P` acts on `U` (through `P ≤ H ≤ N_G(U)`)
  have hPH : Work.GW2.pCoreIn 2 M ≤ B.H := hPC
  have hPnorm : Work.GW2.pCoreIn 2 M ≤ Subgroup.normalizer (B.U : Set G) :=
    hPH.trans (L27su_H_le_normalizer_U B)
  -- coprimality of `|P|` and `|U|`
  have hcop : Nat.Coprime 2 (Nat.card ↥B.U) :=
    (Nat.coprime_two_right.mpr (L27su_odd_card_U B)).symm
  -- `F(U) ≤ U` and `F(U) ◁ U`
  have hFUleU : Work.GW2.fittingIn B.U ≤ B.U := Subgroup.map_subtype_le _
  have hFUnorm : ((Work.GW2.fittingIn B.U).subgroupOf B.U).Normal := by
    rw [Work.GW2.fittingIn, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective B.U.subtype_injective]
    exact Subgroup.normalCore_normal _
  -- Bender 1.1(iv) with `K = U`, `K₀ = F(U)`
  refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr ?_
  exact T.c11iv G 2 (Work.GW2.pCoreIn 2 M) B.U (Work.GW2.fittingIn B.U)
    (isPGroup_pCoreIn_two M) hcop hPnorm hFUleU hFUnorm hPCF
    (L27su_centralizer_fittingIn_U_le T G hFT hCtx B)


end Work.CORE2B
