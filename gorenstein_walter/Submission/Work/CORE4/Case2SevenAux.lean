import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.LayerCtx6
import Submission.Work.CORE4.SixThree

open scoped MatrixGroups

namespace Work.CORE4

open Subgroup

variable {G : Type} [Group G] [Finite G]

/-! ## The Fitting subgroup of a subgroup, and the `§4` subgroup `K`

Structural facts about the §4 objects used by Bender's (7)/(8): `F(K) ⊴ K`, and
`K = I_{U ⊓ M}(s) ⊴ U ⊓ M` (Bender 1.5(iii), via the input `I.toolkit.c15`). -/

/-- `F(X) ⊴ X` (the Fitting subgroup is normal). -/
theorem fitting_normal {X : Type*} [Group X] (K : Subgroup X) : (Work.GW2.fitting ↥K).Normal :=
  Subgroup.normalCore_normal _

/-- `F(K) ⊴ K`, viewed as a subgroup of the ambient group. -/
theorem fittingIn_subgroupOf_normal {X : Type*} [Group X] (K : Subgroup X) :
    ((Work.GW2.fittingIn K).subgroupOf K).Normal := by
  have h1 : (Work.GW2.fittingIn K).subgroupOf K = Work.GW2.fitting ↥K := by
    rw [← Subgroup.comap_subtype (Work.GW2.fittingIn K) K]
    exact Subgroup.comap_map_eq_self_of_injective Subtype.val_injective _
  rw [h1]
  exact fitting_normal K

/-- `K = I_{U ⊓ M}(s)` is normal in `U ⊓ M` (the input `I.toolkit.c15`; Bender 1.5(iii)). -/
theorem Case2Data.K_normal_in_UinfM (I : Work.GW2.C4Inputs) (B : Work.GW2.BenderSetup G)
    (D : Work.GW2.Case2Data B) :
    (D.K.subgroupOf (B.U ⊓ D.M)).Normal := by
  have hOdd : Odd (Nat.card ↥(B.U ⊓ D.M)) :=
    Odd.of_dvd_nat B.U_odd (Subgroup.card_dvd_of_le (inf_le_left : B.U ⊓ D.M ≤ B.U))
  have hsN : D.s ∈ Subgroup.normalizer (((B.U ⊓ D.M : Subgroup G)) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    have hsH : D.s ∈ B.H := B.S_le_H D.s_mem_S
    have hsM : D.s ∈ D.M := layerIn_le D.M D.s_mem_layer
    intro y
    constructor
    · intro hy
      obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.mp hy
      exact Subgroup.mem_inf.mpr
        ⟨(Subgroup.normal_subgroupOf_iff B.U_le_H).mp B.U_normal y D.s hy1 hsH,
          D.M.mul_mem (D.M.mul_mem hsM hy2) (D.M.inv_mem hsM)⟩
    · intro hy
      obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.mp hy
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have h3 := (Subgroup.normal_subgroupOf_iff B.U_le_H).mp B.U_normal
          (D.s * y * D.s⁻¹) D.s⁻¹ hy1 (B.H.inv_mem hsH)
        have heq : D.s⁻¹ * (D.s * y * D.s⁻¹) * (D.s⁻¹)⁻¹ = y := by group
        rwa [heq] at h3
      · have h2 : y = D.s⁻¹ * (D.s * y * D.s⁻¹) * D.s := by group
        rw [h2]
        exact D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hsM) hy2) hsM
  exact (I.toolkit.c15 G I.toolkit.ft (B.U ⊓ D.M) D.s D.s_order hOdd hsN).2.2 D.K D.K_def |>.2.1

/-- `K₁F = F(U) ⊓ M` (Bender §4 (3)), where `K₁ = F(U) ⊓ K`: the version of `SixThree` oriented
towards the normalizer `N_{F(U)}(F)`. -/
theorem Case2Data.K1F_eq (I : Work.GW2.C4Inputs) (hbc : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (D : Work.GW2.Case2Data B) (hpre : Work.GW2.Case2Pre B D) :
    (Work.GW2.fittingIn B.U ⊓ D.K) ⊔ D.F = Work.GW2.fittingIn B.U ⊓ D.M :=
  (SixThree I G hbc B D hpre).symm

/-- **Bender §4 (7): `K₁F = N_{F(U)}(F)`.**  Since `N_G(F) = M` (Bender's (5)), the normalizer of
`F` inside `F(U)` is `F(U) ⊓ M = K₁F`. -/
theorem Case2Data.K1F_eq_normalizer (B : Work.GW2.BenderSetup G) (D : Work.GW2.Case2Data B)
    (hpre : Work.GW2.Case2Pre B D) :
    Subgroup.normalizer (D.F : Set G) ⊓ Work.GW2.fittingIn B.U =
      Work.GW2.fittingIn B.U ⊓ D.M := by
  rw [Work.GW2.Case2Pre.N_F B D hpre, inf_comm]

/-- `K₁F ≠ ⊥` (because `F ≠ ⊥`). -/
theorem Case2Data.K1F_ne_bot (B : Work.GW2.BenderSetup G) (D : Work.GW2.Case2Data B)
    (hpre : Work.GW2.Case2Pre B D) :
    (Work.GW2.fittingIn B.U ⊓ D.K) ⊔ D.F ≠ ⊥ := by
  intro h
  have hF : D.F ≤ (⊥ : Subgroup G) := by
    have hle : D.F ≤ (Work.GW2.fittingIn B.U ⊓ D.K) ⊔ D.F := le_sup_right
    rwa [h] at hle
  exact Work.GW2.Case2Pre.F_ne B D hpre (le_bot_iff.mp hF)

end Work.CORE4
