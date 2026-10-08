import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.SixThree
import Submission.Work.CORE4.Case2SevenAux
import Submission.Work.CORE4.SevenX.piFU_le_pi_K0F

open scoped MatrixGroups

namespace Work.CORE4

open Work.GW2 Subgroup

set_option linter.style.haveILetI false

/-! ## Two auxiliary lemmas

`normalizer_subgroupOf_eq_inf` is the bridge between the normalizer computed inside the
subgroup `↥A` and the ambient one; `conjSub_eq_of_normal_subgroupOf` produces the
conjugation identity needed to show that `H` normalizes `F(U)`. -/

/-- The normalizer of `F.subgroupOf A` in `↥A` is `(A ⊓ N_G(F)).subgroupOf A`. -/
theorem normalizer_subgroupOf_eq_inf {G : Type} [Group G] {F A : Subgroup G} (h : F ≤ A) :
    Subgroup.normalizer ((F.subgroupOf A : Subgroup ↥A) : Set ↥A) =
      (A ⊓ Subgroup.normalizer (F : Set G)).subgroupOf A := by
  rw [← Subgroup.subgroupOf_normalizer_eq h, ← Subgroup.inf_subgroupOf_right
    (Subgroup.normalizer F) A, inf_comm]

/-- If `X ⊴ H` (as a subgroup of `H`) and `g ∈ H`, then `conjSub g X = X`. -/
theorem conjSub_eq_of_normal_subgroupOf {G : Type} [Group G] {X H : Subgroup G} (hXH : X ≤ H)
    (hn : (X.subgroupOf H).Normal) (g : G) (hg : g ∈ H) : conjSub g X = X := by
  refine le_antisymm ?_ ?_
  · intro y hy
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
    have h1 := (Subgroup.normal_subgroupOf_iff hXH).mp hn z g hz hg
    rw [← hzy]
    simpa [MulAut.conj_apply] using h1
  · intro x hx
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, ?_, ?_⟩
    · have h1 := (Subgroup.normal_subgroupOf_iff hXH).mp hn x g⁻¹ hx (H.inv_mem hg)
      simpa using h1
    · simp [MulAut.conj_apply, mul_assoc]

section

variable {G : Type} [Group G] [Finite G]

/-- `H ≤ N_G(F(U))`: `U ⊴ H` and `F(U)` is characteristic in `U` (via `conjSub_fittingIn`). -/
theorem BenderSetup.H_le_normalizer_fittingIn (B : BenderSetup G) :
    B.H ≤ Subgroup.normalizer ((fittingIn B.U : Subgroup G) : Set G) := by
  intro g hg
  have hU : conjSub g B.U = B.U := conjSub_eq_of_normal_subgroupOf B.U_le_H B.U_normal g hg
  have hA : conjSub g (fittingIn B.U) = fittingIn B.U := by
    rw [conjSub_fittingIn, hU]
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact hA

-- Bender's §4 "K₁ ≠ 1" (K₁ = F(U) ⊓ K = `Work.GW2.fittingIn B.U ⊓ h.D.K`), used on p. 228
-- ("q > 7 because K₁ ≠ 1") and needed as the hypothesis of `CORE4/Case2Numeric`.
-- Route (thanks to the referee): `SixThree` gives F(U) ⊓ M = K₁ ⊔ F.  If K₁ = ⊥ then
-- F(U) ⊓ M = F; either F(U) ≤ M (forcing F(U) = F and H ≤ N_G(F) = M, contradicting
-- `Case2Pre.not_H_le`), or F < F(U) and the normalizer condition in the nilpotent group F(U)
-- gives g ∈ N_{F(U)}(F) ∖ F; then g ∈ M = N_G(F), so g ∈ F(U) ⊓ M = F — contradiction.
-- Hence |F| ∣ |K₁| and F ≠ ⊥ gives K₁ ≠ ⊥.
-- IMPORTANT: import ONLY modules that do not declare clashing `Work.GW2.*` names:
-- `Submission.Work.CORE4.*`, `Submission.Work.FUS.*`, `Submission.Work.RED.*`,
-- `Submission.Work.Dihedral.Defs`, `Submission.OddOrder.*`.
/-- **Bender 1981, §4: `K₁ ≠ 1`.**  The formalised argument is the one above: assuming
`F(U) ⊓ K = ⊥`, Bender's (3) (`SixThree`) gives `F(U) ⊓ M = F`; `N_G(F) = M` (`Case2Pre`)
turns this into `N_{F(U)}(F) = F`, and the normalizer condition in the nilpotent group `F(U)`
(`PiFU.isNilpotent_fittingIn`, Fitting's theorem) forces `F(U) = F`; but then `H` normalizes
`F(U) = F`, so `H ≤ N_G(F) = M`, contradicting `Case2Pre.not_H_le`. -/
theorem Case2K1_ne_bot (I : Work.GW2.C4Inputs) {G : Type} [Group G] [Finite G]
    {B : Work.GW2.BenderSetup G} (hbc : Work.GW2.BenderCtx G) (h : Work.GW2.Case2Ctx B) :
    Work.GW2.fittingIn B.U ⊓ h.D.K ≠ ⊥ := by
  intro hbot
  -- §4 (3): `F(U) ⊓ M = K₀ ⊔ F`, which under `K₀ = ⊥` is `F`
  have hFU : Work.GW2.fittingIn B.U ⊓ h.D.M = h.D.F := by
    rw [SixThree I G hbc B h.D h.pre, hbot, bot_sup_eq]
  have hFA : h.D.F ≤ Work.GW2.fittingIn B.U := h.D.F_le_fitting B
  -- `N_{F(U)}(F) = F(U) ⊓ N_G(F) = F(U) ⊓ M = F`
  have hNA : Work.GW2.fittingIn B.U ⊓ Subgroup.normalizer (h.D.F : Set G) = h.D.F := by
    rw [Case2Pre.N_F B h.D h.pre]
    exact hFU
  -- so `F` is self-normalizing in the nilpotent group `F(U)`
  have hnorm : Subgroup.normalizer
      ((h.D.F.subgroupOf (Work.GW2.fittingIn B.U) :
        Subgroup ↥(Work.GW2.fittingIn B.U)) : Set ↥(Work.GW2.fittingIn B.U)) =
      h.D.F.subgroupOf (Work.GW2.fittingIn B.U) := by
    rw [normalizer_subgroupOf_eq_inf hFA, hNA]
  haveI : Group.IsNilpotent ↥(Work.GW2.fittingIn B.U) :=
    SevenX.PiFU.isNilpotent_fittingIn B.U
  -- the normalizer condition (nilpotent groups) forces `F = F(U)`
  have htop : (h.D.F.subgroupOf (Work.GW2.fittingIn B.U) :
      Subgroup ↥(Work.GW2.fittingIn B.U)) = ⊤ :=
    (normalizerCondition_iff_only_full_group_self_normalizing.mp
      (Group.normalizerCondition_of_isNilpotent (G := ↥(Work.GW2.fittingIn B.U))) _) hnorm
  have hAF : Work.GW2.fittingIn B.U ≤ h.D.F := by
    intro a ha
    have h2 : (⟨a, ha⟩ : ↥(Work.GW2.fittingIn B.U)) ∈
        h.D.F.subgroupOf (Work.GW2.fittingIn B.U) := by
      rw [htop]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp h2
  have hAeqF : Work.GW2.fittingIn B.U = h.D.F := le_antisymm hAF hFA
  -- hence `H ≤ N_G(F(U)) = N_G(F) = M`, contradicting `¬ H ≤ M`
  have h1 : B.H ≤ Subgroup.normalizer (Work.GW2.fittingIn B.U : Set G) :=
    BenderSetup.H_le_normalizer_fittingIn B
  rw [hAeqF, Case2Pre.N_F B h.D h.pre] at h1
  exact Case2Pre.not_H_le B h.D h.pre h1

end

end Work.CORE4
