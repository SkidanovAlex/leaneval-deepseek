import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Defs10
import Submission.Work.CORE4.API
import Submission.Work.CORE4.CountSetup
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.SixThree
import Submission.Work.CORE4.Case2Seven
import Submission.Work.CORE4.Case2K1_ne_bot
import Submission.Work.CORE4.SevenX.piF_le_pi_K0_of_witness
import Submission.Work.CORE4.SevenX.piFU_le_pi_K0F
import Submission.Work.CORE4.SixEmbedAux.card_F_dvd_card_K0_of_witness
import Submission.Work.CORE4.SixEmbedAux.exists_mem_normalizer_notMem_of_lt_of_isNilpotent

open Work.GW2 Subgroup

namespace Work.CORE4

/-- There is `g ∉ M` with `F^g ≤ F(U) ⊓ M = K₀F`: if `F(U) ≤ M`, any `h ∈ H ∖ M` works (`H`
normalises `F(U) = K₀F`); otherwise `K₀F = F(U) ⊓ M` is a proper subgroup of the nilpotent group
`F(U)`, so its normaliser grows and any `g ∈ N_{F(U)}(K₀F) ∖ K₀F` lies in `F(U)` but not in
`M = N_G(F)`. -/
theorem exists_witness_of_case2ctx6 (I : Work.GW2.C4Inputs) {G : Type} [Group G] [Finite G]
    (hbc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (C : Work.GW2.Case2Ctx6 B) :
    ∃ g : G, g ∉ C.D.M ∧ Work.GW2.conjSub g C.D.F ≤ Work.GW2.fittingIn B.U ⊓ C.D.M := by
  have hpre : Work.GW2.Case2Pre B C.D := C.pre
  -- Bender's (3): `F(U) ⊓ M = K₀ ⊔ F`
  have hT : C.D.K0 ⊔ C.D.F = Work.GW2.fittingIn B.U ⊓ C.D.M :=
    K0_sup_F_eq I hbc B C.D hpre
  by_cases hXM : Work.GW2.fittingIn B.U ≤ C.D.M
  · -- Case A: `F(U) ≤ M`, so `K₀ ⊔ F = F(U)` and any `h ∈ H ∖ M` normalises it
    obtain ⟨h, hhH, hhM⟩ : ∃ h ∈ B.H, h ∉ C.D.M := by
      by_contra hcon
      push Not at hcon
      exact Work.GW2.Case2Pre.not_H_le B C.D hpre hcon
    have hhN : h ∈ Subgroup.normalizer (Work.GW2.fittingIn B.U : Set G) :=
      BenderSetup.H_le_normalizer_fittingIn B hhH
    have hconjX : Work.GW2.conjSub h (Work.GW2.fittingIn B.U) = Work.GW2.fittingIn B.U :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hhN
    refine ⟨h, hhM, ?_⟩
    calc Work.GW2.conjSub h C.D.F
        ≤ Work.GW2.conjSub h (Work.GW2.fittingIn B.U) :=
          Subgroup.map_mono (Work.GW2.Case2Data.F_le_fitting B C.D)
      _ = Work.GW2.fittingIn B.U := hconjX
      _ = Work.GW2.fittingIn B.U ⊓ C.D.M := (inf_eq_left.mpr hXM).symm
  · -- Case B: `K₀F = F(U) ⊓ M` is proper in the nilpotent group `F(U)`
    have hTX : C.D.K0 ⊔ C.D.F ≤ Work.GW2.fittingIn B.U := by
      rw [hT]; exact inf_le_left
    have hne : C.D.K0 ⊔ C.D.F ≠ Work.GW2.fittingIn B.U := by
      intro hEq
      exact hXM (by rw [← hEq, hT]; exact inf_le_right)
    obtain ⟨g, hgX, hgN, hgT⟩ :=
      SixEmbedAux.exists_mem_normalizer_notMem_of_lt_of_isNilpotent
        (SevenX.PiFU.isNilpotent_fittingIn B.U) hTX hne
    have hconjT : Work.GW2.conjSub g (C.D.K0 ⊔ C.D.F) = C.D.K0 ⊔ C.D.F :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hgN
    refine ⟨g, ?_, ?_⟩
    · -- `g ∉ M`: `g ∈ F(U)` and `F(U) ⊓ M = K₀F`
      intro hgM
      exact hgT (by rw [hT]; exact Subgroup.mem_inf.mpr ⟨hgX, hgM⟩)
    · -- `F^g ≤ K₀F`
      calc Work.GW2.conjSub g C.D.F
          ≤ Work.GW2.conjSub g (C.D.K0 ⊔ C.D.F) := Subgroup.map_mono le_sup_right
        _ = C.D.K0 ⊔ C.D.F := hconjT
        _ = Work.GW2.fittingIn B.U ⊓ C.D.M := hT

/-- Bender's (6) in full (p. 225, the line before (6)): "As we can choose `g ∈ N_H(K₀F)`, *F is
isomorphic to a subgroup of `K₀`*".

`SixEmbedProp I` is `∀ G [Group G] [Finite G], BenderCtx G → ∀ B, C : Case2Ctx6 B,
Nat.card C.D.F ∣ Nat.card C.D.K0`, with `K₀ = C.D.K0 = F(U) ∩ K`.

This is the input that `Case2Seven` (and the `A₇` chain A1) need; the earlier claim that a
`K₀ = ⊥` configuration satisfies `Case2Ctx6` is wrong — see
`Submission/Work/CORE4/NOTES_CASE2SEVEN_FROM_OWNER.md` and `NOTES_LEAD_gw_design10.md` §3.1.

Route (design pass 10 §3.1):
1. `F(U) ∩ M = K₀ ⊔ F` (`Submission.Work.CORE4.SixThree`, proved).
2. Find `g ∈ H ∖ M` normalising `K₀F`: if `F(U) ≤ M`, any `g ∈ H ∖ M` works (H normalises `F(U)`,
   and `¬ B.H ≤ C.D.M` is `Case2Pre`'s first conjunct); otherwise normalisers grow in the
   nilpotent `F(U)`, so some `g ∈ N_{F(U)}(K₀F) ∖ K₀F` exists and lies outside `M`
   (`SixEmbedAux.exists_mem_normalizer_notMem_of_lt_of_isNilpotent`, from Mathlib's normalizer
   condition `Group.normalizerCondition_of_isNilpotent`, with nilpotency of `F(U)` from
   `Work.CORE4.SevenX.PiFU.isNilpotent_fittingIn`).
3. `F^g ≤ K₀F`, `F ∩ F^g = 1` (`C.F_ti`, as `g ∉ M`), and `F ⊴ K₀F` (from
   `Case2Pre.N_F : N_G(F) = M` and `K₀F ≤ M`), so `F ≅ F^g F / F ≤ K₀F/F ≅ K₀`, whence
   `|F| ∣ |K₀|` (`SixEmbedAux.card_F_dvd_card_K0_of_witness`).  In particular `K₀ ≠ ⊥`,
   since `F ≠ ⊥`.

Useful existing material in the area: `Submission.Work.CORE4.SixThree` (`F(U) ∩ M = K₀ ⊔ F`,
`K0_inf_F_eq_bot`, `K0_normal_in_K0supF`), `API.lean` (accessors of `Case2Data`/`Case2Pre`),
`CountSetup.lean` (`N_G(E(M)) = M`, `M = E·C_M(t)`). -/
theorem Case2SixEmbed (I : Work.GW2.C4Inputs) : Work.GW2.SixEmbedProp I := by
  intro G _ _ hbc B C
  exact SixEmbedAux.card_F_dvd_card_K0_of_witness I G hbc B C
    (exists_witness_of_case2ctx6 I hbc B C)

/-- **Corollary: `K₀ = F(U) ∩ K ≠ 1`** (Bender's `K₁ ≠ 1`), unconditionally from `Case2Ctx6`.
Indeed `|F| ∣ |K₀|` and `F ≠ 1` (`Case2Pre.F_ne`).  This is what shows that the "`K₀ = ⊥`
configuration" of `NOTES_CASE2SEVEN.md` §3–4 does not satisfy `Case2Ctx6`. -/
theorem K0_ne_bot_of_case2ctx6 (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (C : Work.GW2.Case2Ctx6 B), C.D.K0 ≠ ⊥ := by
  intro G _ _ hbc B C
  have hdvd : Nat.card C.D.F ∣ Nat.card C.D.K0 := Case2SixEmbed I G hbc B C
  intro hbot
  rw [hbot, Subgroup.card_bot] at hdvd
  have hcard : Nat.card C.D.F = 1 := Nat.dvd_one.mp hdvd
  exact Work.GW2.Case2Pre.F_ne B C.D C.pre ((Subgroup.card_eq_one (H := C.D.F)).mp hcard)

end Work.CORE4
