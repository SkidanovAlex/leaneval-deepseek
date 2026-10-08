import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.SixThree
import Submission.Work.CORE4.Case2Seven
import Submission.Work.CORE4.SevenX.piF_le_pi_K0_of_witness

set_option linter.style.haveILetI false

namespace Work.CORE4.SixEmbedAux

open Work.GW2 Subgroup

/-- From Bender's §4 (6)-witness `∃ g ∉ M, F^g ≤ F(U) ∩ M = K₀F`, the divisibility `|F| ∣ |K₀|`:
`F^g` is a subgroup of `K₀ ⊔ F` with `F^g ⊓ F = ⊥`, so `↥(F^g) →* (↥(K₀ ⊔ F)) ⧸ F.subgroupOf (K₀ ⊔ F)`
is injective, while `|(↥(K₀ ⊔ F)) ⧸ F| = F.relIndex (K₀ ⊔ F) = |K₀|` (second isomorphism theorem,
using `K₀ ⊓ F = ⊥` and `F ⊴ K₀ ⊔ F` from `K₀ ⊔ F ≤ M = N_G(F)`). Exactly the content of
`Work.CORE4.SevenX.piF_le_pi_K0_of_witness`, whose proof already contains this `hdvd`. -/
theorem card_F_dvd_card_K0_of_witness (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G → ∀ (B : Work.GW2.BenderSetup G)
      (C : Work.GW2.Case2Ctx6 B),
      (∃ g : G, g ∉ C.D.M ∧ Work.GW2.conjSub g C.D.F ≤ Work.GW2.fittingIn B.U ⊓ C.D.M) →
      Nat.card C.D.F ∣ Nat.card C.D.K0 := by
  intro G _ _ hbc B C hwit
  obtain ⟨g, hgM, hgF⟩ := hwit
  -- Bender §4 (3): `F(U) ⊓ M = K₀ ⊔ F`
  have hH_eq : C.D.K0 ⊔ C.D.F = Work.GW2.fittingIn B.U ⊓ C.D.M :=
    Work.CORE4.K0_sup_F_eq I hbc B C.D C.pre
  -- the witness, reoriented: `F^g ≤ K₀ ⊔ F`
  have hYH : Work.GW2.conjSub g C.D.F ≤ C.D.K0 ⊔ C.D.F := by
    rw [hH_eq]; exact hgF
  -- §4 (6): `F^g ⊓ F = ⊥`
  have hYinf : Work.GW2.conjSub g C.D.F ⊓ C.D.F = ⊥ := by
    rw [inf_comm]; exact C.F_ti g hgM
  have hFH : C.D.F ≤ C.D.K0 ⊔ C.D.F := le_sup_right
  -- `K₀ ⊔ F ≤ M`
  have hHleM : C.D.K0 ⊔ C.D.F ≤ C.D.M :=
    sup_le (le_trans inf_le_right (C.D.K_le_M B)) (le_trans (C.D.F_le_UinfM B) inf_le_right)
  -- `K₀ ⊔ F ≤ N_G(F) = M`, hence `F ⊴ K₀ ⊔ F`
  have hHN : C.D.K0 ⊔ C.D.F ≤ Subgroup.normalizer (C.D.F : Set G) := by
    rw [Work.GW2.Case2Pre.N_F B C.D C.pre]; exact hHleM
  letI : (C.D.F.subgroupOf (C.D.K0 ⊔ C.D.F)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hHN
  -- `|(K₀ ⊔ F) ⧸ F| = |K₀|`
  have hrel : C.D.F.relIndex (C.D.K0 ⊔ C.D.F) = Nat.card ↥C.D.K0 := by
    have h1 := Subgroup.relIndex_mul_card C.D.F (C.D.K0 ⊔ C.D.F)
    rw [inf_eq_left.mpr hFH] at h1
    rw [Work.CORE4.card_K0_sup_F I hbc B C.D C.pre] at h1
    exact Nat.mul_right_cancel (Nat.card_pos (α := ↥C.D.F)) h1
  have hquot_eq :
      Nat.card ((↥(C.D.K0 ⊔ C.D.F)) ⧸ (C.D.F.subgroupOf (C.D.K0 ⊔ C.D.F))) =
        Nat.card ↥C.D.K0 := by
    rw [← Subgroup.index_eq_card]
    exact hrel
  -- `|F^g| ∣ |(K₀ ⊔ F) ⧸ F|`
  have hdvd_quot : Nat.card ↥(Work.GW2.conjSub g C.D.F) ∣
      Nat.card ((↥(C.D.K0 ⊔ C.D.F)) ⧸ (C.D.F.subgroupOf (C.D.K0 ⊔ C.D.F))) :=
    Work.CORE4.SevenX.card_dvd_card_quotient_of_inf_eq_bot (F := C.D.F) (H := C.D.K0 ⊔ C.D.F)
      (Y := Work.GW2.conjSub g C.D.F) hYH hYinf
  have hconj_card : Nat.card ↥(Work.GW2.conjSub g C.D.F) = Nat.card ↥C.D.F := by
    rw [Work.GW2.conjSub, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  rw [← hconj_card, ← hquot_eq]
  exact hdvd_quot

end Work.CORE4.SixEmbedAux
