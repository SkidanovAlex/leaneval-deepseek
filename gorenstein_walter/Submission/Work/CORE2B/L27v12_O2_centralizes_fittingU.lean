import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.API
import Submission.Work.CORE2B.c11iv_nilpotent
import Submission.Work.CORE2B.L27v12_selfcent
import Submission.Work.CORE2B.L27_O2_centralized_by_t

namespace Work.CORE2B

open Subgroup

set_option linter.unusedVariables false

-- Leaf N3 of the lead's design pass 12 (`_design_gw/Core12L27.lean`): the step the area reported
-- missing, `O₂(M) ≤ C_G(F(U))`, under the hypotheses `L27Hyp B M`.
-- Route: `P := O₂(M) ≤ C(t) = H` (`Work.CORE2B.L27_O2_centralized_by_t`, sorry-free) normalizes
-- `F(U)` (characteristic in `U ⊴ H`) and `M ⊓ F(U)`; `M ⊓ F(U)` normalizes `P ⊴ M`; so
-- `⁅P, M ⊓ F(U)⁆ ≤ P ⊓ F(U) = ⊥` (coprime orders); then
-- `c11iv_nilpotent T 2 P (F(U)) (M ⊓ F(U))` (leaf N1, proved) with `L27v12_selfcent` (leaf N2,
-- proved: `M ⊓ F(U)` is self-centralizing in the nilpotent `F(U)`) gives `P ≤ C(F(U))`.
theorem L27v12_O2_centralizes_fittingU (T : Work.GW2.LocalToolkit) (h23 : Work.GW2.Lemma23Prop)
    (h26 : Work.GW2.Thm26Prop) (G : Type) [Group G] [Finite G]
    (hFT : Work.GW2.FeitThompsonProp) (hCtx : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (M : Subgroup G) (hD : Work.CORE2B.L27Hyp B M) :
    Work.GW2.pCoreIn 2 M ≤
      Subgroup.centralizer ((Work.GW2.fittingIn B.U : Subgroup G) : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- ## Elementary pieces
  -- `P := O₂(M)` is contained in `M`, and it is a `2`-group.
  have hPleM : Work.GW2.pCoreIn 2 M ≤ M := (in_le_self M 2 ∅).2.1
  have hPgroup : IsPGroup 2 (Work.GW2.pCoreIn 2 M) := isPGroup_pCoreIn_two M
  -- `F(U) ≤ U`, and `H` normalizes `U` (as `U = O(H) ◁ H`).
  have hFUleU : Work.GW2.fittingIn B.U ≤ B.U := (in_le_self B.U 2 ∅).2.2.1
  have hHnormU : B.H ≤ Subgroup.normalizer (B.U : Set G) := by
    simpa only [Work.GW2.BenderSetup.U, Work.GW2.oddCoreIn] using
      (le_normalizer_map_subtype_local B.H (Work.GW2.oddCore ↥B.H)
        (Work.GW2.oddCore_normal ↥B.H))
  -- ## Step 1: `P ≤ C(t) = H ≤ N_G(U) ≤ N_G(F(U))`, `F(U)` being characteristic in `U`.
  have hPH : Work.GW2.pCoreIn 2 M ≤ B.H :=
    L27_O2_centralized_by_t T h23 h26 G hFT hCtx B M hD
  have hPnormK : Work.GW2.pCoreIn 2 M ≤
      Subgroup.normalizer ((Work.GW2.fittingIn B.U : Subgroup G) : Set G) :=
    le_normalizer_fittingIn_of_le_normalizer_local (hPH.trans hHnormU)
  -- `P ≤ N_G(M ⊓ F(U))`: `P ≤ M ≤ N_G(M)` and `P ≤ N_G(F(U))`.
  have hPnormK0 : Work.GW2.pCoreIn 2 M ≤
      Subgroup.normalizer ((M ⊓ Work.GW2.fittingIn B.U : Subgroup G) : Set G) :=
    (le_inf (hPleM.trans Subgroup.le_normalizer) hPnormK).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  -- `M ⊓ F(U) ≤ N_G(P)`: `P = O₂(M) ◁ M`.
  have hK0normP : M ⊓ Work.GW2.fittingIn B.U ≤
      Subgroup.normalizer ((Work.GW2.pCoreIn 2 M : Subgroup G) : Set G) :=
    inf_le_left.trans (L27cf_le_normalizer_pCoreIn_two M)
  -- ## Step 2: `P ⊓ F(U) = ⊥`, since `P` has `2`-power order and `F(U) ≤ U` has odd order.
  have hoddU : Odd (Nat.card ↥B.U) := by
    rw [Work.GW2.BenderSetup.U, Work.GW2.oddCoreIn,
      Subgroup.card_map_of_injective B.H.subtype_injective]
    exact oddCore_odd (G := ↥B.H)
  have hoddK : Odd (Nat.card (Work.GW2.fittingIn B.U)) :=
    hoddU.of_dvd_nat (Subgroup.card_dvd_of_le hFUleU)
  have hcop : Nat.Coprime 2 (Nat.card (Work.GW2.fittingIn B.U)) :=
    Nat.coprime_two_left.mpr hoddK
  have hPKbot : Work.GW2.pCoreIn 2 M ⊓ Work.GW2.fittingIn B.U = ⊥ :=
    (IsPGroup.disjoint_of_coprime hPgroup IsPGroup.card hcop).eq_bot
  -- ## Step 3: `⁅P, M ⊓ F(U)⁆ ≤ P ⊓ (M ⊓ F(U)) ≤ P ⊓ F(U) = ⊥`.
  have hcommP : ⁅Work.GW2.pCoreIn 2 M, M ⊓ Work.GW2.fittingIn B.U⁆ ≤
      Work.GW2.pCoreIn 2 M := by
    have h := (Subgroup.le_normalizer_iff_commutator_le_right
      (H := M ⊓ Work.GW2.fittingIn B.U) (K := Work.GW2.pCoreIn 2 M)).mp hK0normP
    rwa [Subgroup.commutator_comm] at h
  have hcommK0 : ⁅Work.GW2.pCoreIn 2 M, M ⊓ Work.GW2.fittingIn B.U⁆ ≤
      M ⊓ Work.GW2.fittingIn B.U :=
    (Subgroup.le_normalizer_iff_commutator_le_right
      (H := Work.GW2.pCoreIn 2 M) (K := M ⊓ Work.GW2.fittingIn B.U)).mp hPnormK0
  have hcommbot : ⁅Work.GW2.pCoreIn 2 M, M ⊓ Work.GW2.fittingIn B.U⁆ = ⊥ := by
    rw [eq_bot_iff]
    refine (le_inf hcommP hcommK0).trans ?_
    exact (inf_le_inf_left _ inf_le_right).trans (le_of_eq hPKbot)
  -- ## Step 4: hence `P` centralizes `M ⊓ F(U)`.
  have hPK0 : Work.GW2.pCoreIn 2 M ≤
      Subgroup.centralizer ((M ⊓ Work.GW2.fittingIn B.U : Subgroup G) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommbot
  -- ## Step 5: `F(U)` is nilpotent and `M ⊓ F(U)` is self-centralizing in it.
  have hKnil : Group.IsNilpotent ↥(Work.GW2.fittingIn B.U) := by
    haveI : Group.IsNilpotent ↥(Work.GW2.fitting ↥B.U) := L27cf_isNilpotent_fitting (G := ↥B.U)
    exact (Group.isNilpotent_congr (Subgroup.equivMapOfInjective (Work.GW2.fitting ↥B.U)
      B.U.subtype B.U.subtype_injective)).mp inferInstance
  have hself : Work.GW2.fittingIn B.U ⊓
      Subgroup.centralizer ((M ⊓ Work.GW2.fittingIn B.U : Subgroup G) : Set G) ≤
      M ⊓ Work.GW2.fittingIn B.U :=
    L27v12_selfcent T h26 G hFT hCtx B M hD
  -- ## Step 6: Bender 1.1(iv) with the self-centralizing `K₀ = M ⊓ F(U)`.
  exact c11iv_nilpotent T 2 (Work.GW2.pCoreIn 2 M) (Work.GW2.fittingIn B.U)
    (M ⊓ Work.GW2.fittingIn B.U) hPgroup hcop hPnormK hKnil inf_le_right hPK0 hself

end Work.CORE2B
