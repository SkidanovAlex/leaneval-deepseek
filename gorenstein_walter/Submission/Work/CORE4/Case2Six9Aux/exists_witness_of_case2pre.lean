import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.SixThree
import Submission.Work.CORE4.Case2Seven
import Submission.Work.CORE4.Case2K1_ne_bot
import Submission.Work.CORE4.SixEmbedAux.exists_mem_normalizer_notMem_of_lt_of_isNilpotent
import Submission.Work.CORE4.SevenX.piFU_le_pi_K0F

namespace Work.CORE4.Case2Six9Aux

/-! ## The witness

Bender §4 (6) (1981, p. 225): "As we can choose `g ∈ N_G(K₁F)`, `F` is isomorphic to a subgroup of
`K₁`, hence is cyclic."  The witness `g ∉ M` with `F^g ≤ F(U) ∩ M = K₁F` is produced here from
`F(U) ⊴ H` and `H ≰ M` alone, in the two cases `F(U) ≤ M` and `F(U) ≰ M`:

* if `F(U) ≤ M`, any `h ∈ H ∖ M` satisfies `F^h ≤ F(U) ≤ M` because `H` normalises `F(U)`
  (`BenderSetup.H_le_normalizer_fittingIn`, from `O(H) ⊴ H` and `F(U)` characteristic in `O(H)`);
* if `F(U) ≰ M`, the nilpotent group `F(U)` satisfies the normalizer condition, so there is
  `g ∈ F(U) ∖ (F(U) ∩ M)` normalising `T := F(U) ∩ M = K₀F`; then `g ∉ M` and
  `F^g ≤ T^g = T` (`F ≤ T`), i.e. `F^g ≤ F(U) ∩ M`.

So — contrary to the verdicts recorded in `CORE4/SixConj.lean` and `CORE4/Case2Seven.lean` — the
witness *is* a consequence of §4 (1)–(5): it needs only `F ≤ F(U)`, `H ≤ N_G(F(U))` (from
`O(H) ⊴ H` and `F(U)` characteristic in `O(H)`), `H ≰ M` and the nilpotency of `F(U)`, all of which
`Case2Pre`/`Case2Data`/`BenderSetup` provide.  In particular, combined with `SixConj_imp_K_ne_bot`,
this yields `D.K ≠ ⊥` under `Case2Pre` alone, in agreement with the proved `CORE4/Case2K1_ne_bot`
(`F(U) ⊓ D.K ≠ ⊥`); the configuration `D.K = ⊥` is therefore *not* compatible with the recorded
hypotheses, and `CORE4/Case2Seven` needs no extra hypothesis for the §4 (6) witness. -/
theorem exists_witness_of_case2pre {G : Type} [Group G] [Finite G] (I : Work.GW2.C4Inputs)
    (hbc : Work.GW2.BenderCtx G) {B : Work.GW2.BenderSetup G} (D : Work.GW2.Case2Data B)
    (hpre : Work.GW2.Case2Pre B D) :
    ∃ g : G, g ∉ D.M ∧ Work.GW2.conjSub g D.F ≤ Work.GW2.fittingIn B.U ⊓ D.M := by
  set A : Subgroup G := Work.GW2.fittingIn B.U with hA
  by_cases hAM : A ≤ D.M
  · -- `F(U) ≤ M`: an element of `H ∖ M` normalises `F(U)`, hence conjugates `F` into `F(U) ∩ M`.
    obtain ⟨h, hhH, hhM⟩ := Set.not_subset.mp (Work.GW2.Case2Pre.not_H_le B D hpre)
    refine ⟨h, hhM, ?_⟩
    have hmem : h ∈ Subgroup.normalizer ((A : Subgroup G) : Set G) :=
      Work.CORE4.BenderSetup.H_le_normalizer_fittingIn B hhH
    have hnorm : Work.GW2.conjSub h A = A := by
      rw [Work.GW2.conjSub]
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hmem
    have hAF : Work.GW2.conjSub h D.F ≤ A := by
      intro x hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
      have hyA : y ∈ A := by
        rw [hA]
        exact Work.GW2.Case2Data.F_le_fitting B D hy
      have hxA : x ∈ Work.GW2.conjSub h A := Subgroup.mem_map.mpr ⟨y, hyA, hyx⟩
      rwa [hnorm] at hxA
    exact le_inf hAF (hAF.trans hAM)
  · -- `F(U) ≰ M`: the normalizer condition in the nilpotent `F(U)` grows `F(U) ∩ M`.
    have hnil : Group.IsNilpotent ↥A := by
      rw [hA]
      exact Work.CORE4.SevenX.PiFU.isNilpotent_fittingIn B.U
    have hne : A ⊓ D.M ≠ A := fun heq => hAM (heq ▸ inf_le_right)
    obtain ⟨g, hgA, hgN, hgT⟩ :=
      Work.CORE4.SixEmbedAux.exists_mem_normalizer_notMem_of_lt_of_isNilpotent
        (X := A) (T := A ⊓ D.M) hnil inf_le_left hne
    refine ⟨g, ?_, ?_⟩
    · intro hgM
      exact hgT (Subgroup.mem_inf.mpr ⟨hgA, hgM⟩)
    · have hconj : Work.GW2.conjSub g (A ⊓ D.M) = A ⊓ D.M := by
        rw [Work.GW2.conjSub]
        exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hgN
      have hDF : D.F ≤ A ⊓ D.M :=
        le_inf (by rw [hA]; exact Work.GW2.Case2Data.F_le_fitting B D)
          ((Work.GW2.Case2Data.F_le_UinfM B D).trans inf_le_right)
      have hY : Work.GW2.conjSub g D.F ≤ Work.GW2.conjSub g (A ⊓ D.M) := by
        intro x hx
        obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
        exact Subgroup.mem_map.mpr ⟨y, hDF hy, hyx⟩
      rwa [hconj] at hY

end Work.CORE4.Case2Six9Aux
