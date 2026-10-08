import Mathlib
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.PcoreInBasic
import Submission.Work.CORE2A.dihedral_index_two
import Submission.Work.CORE2A.relIndex_le_two_of_fourGroup_normal
import Submission.Work.CORE2A.sylow_two_not_isCyclic
import Submission.Work.CORE2A.mem_of_orderOf_eq_two_pow
import Submission.Work.CORE2A.normalizer_eq_of_coatom

namespace Work.CORE2A

open Subgroup

/-- Bender's Theorem 2.6, first paragraph, second case: if `V = O₂(Ĥ)` is a four-group with
`V ⊄ S₀` then `[S : V] = 2`, i.e. `|S| = 8`.

Route.  `V ⊴ Ĥ` and `V ≤ S` (`Work.CORE2A.pCoreIn_le_S`); `S ≅ DihedralGroup n` (`n ≥ 2`,
from `BenderCtx.sylow` plus `Work.CORE2A.sylow_two_not_isCyclic`), and elements of `S - S₀`
are involutions (`Work.CORE2A.dihedral_index_two`).  So
`Work.CORE2A.relIndex_le_two_of_fourGroup_normal` gives `V.relIndex S ≤ 2`, i.e.
`[S : V] ∈ {1,2}`.  If `[S : V] = 1` then `V = S`; as `V ⊴ Ĥ` and `|V| = |S| = |Ĥ|₂` (`S` is a
Sylow `2`-subgroup of `Ĥ` because `S ≤ Ĥ` and `[Ĥ : S]` is odd), every Sylow `2`-subgroup of
`Ĥ` equals `V`, so every involution of `Ĥ` lies in `V`; since `V ⊴ Ĥ` we get
`N_G(V) = Ĥ` (if `N_G(V) = G` then `V ⊴ G`, impossible as `1 ≠ V ≠ G`) and hence, by the
second half of `Work.GW2.InvolutionFusionProp`, the three involutions of the four-group `V` are
conjugate in `Ĥ`; so `OneInvClassIn B.Hhat` holds, contradicting `h21`. -/
theorem relIndex_S_V_eq_two (T : Work.GW2.LocalToolkit) (h21 : Work.GW2.Lemma21Prop) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
      ∀ B : Work.GW2.BenderSetup G, Work.GW2.IsFourGroup (Work.GW2.pCoreIn 2 B.Hhat) →
        ¬ Work.GW2.pCoreIn 2 B.Hhat ≤ B.S0 →
        (Work.GW2.pCoreIn 2 B.Hhat).relIndex (B.S : Subgroup G) = 2 := by
  intro G _ _ hFT hctx B hV4 hnot
  classical
  haveI : IsSimpleGroup G := hctx.simple
  -- `V = O₂(Ĥ) ≤ S` and `|V| = 4`, so `4 ≤ |S|`.
  have hVS_le : Work.GW2.pCoreIn 2 B.Hhat ≤ (B.S : Subgroup G) := pCoreIn_le_S B
  have hcardV : Nat.card ↥(Work.GW2.pCoreIn 2 B.Hhat) = 4 := hV4.1
  have h4leS : 4 ≤ Nat.card ↥(B.S : Subgroup G) := by
    rw [← hcardV]
    exact Nat.card_le_card_of_injective (Subgroup.inclusion hVS_le)
      (Subgroup.inclusion_injective hVS_le)
  have h2leS : 2 ≤ Nat.card ↥(B.S : Subgroup G) := by omega
  -- `S` is not cyclic, so `S ≅ DihedralGroup n` with `n ≥ 2`.
  have hSnotcyc : ¬ IsCyclic ↥(B.S : Subgroup G) :=
    sylow_two_not_isCyclic hctx.simple hctx.nonab B.S h2leS
  rcases hctx.sylow B.S with hcyc | ⟨n, hnIso⟩
  · exact absurd hcyc hSnotcyc
  obtain ⟨e⟩ := hnIso
  have hcardS : Nat.card ↥(B.S : Subgroup G) = 2 * n := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hn2 : 2 ≤ n := by omega
  -- `[S : V] ≤ 2`.
  have hconj : ∀ r ∈ B.S0, ∀ v ∈ Work.GW2.pCoreIn 2 B.Hhat,
      r * v * r⁻¹ ∈ Work.GW2.pCoreIn 2 B.Hhat :=
    fun r hr v hv => conj_mem_pCoreIn B (bSetup_S_le_Hhat B (B.S0_le hr)) hv
  have hle2 : (Work.GW2.pCoreIn 2 B.Hhat).relIndex (B.S : Subgroup G) ≤ 2 :=
    relIndex_le_two_of_fourGroup_normal (B.S : Subgroup G) B.S0
      (Work.GW2.pCoreIn 2 B.Hhat) n hn2 ⟨e⟩ B.S0_le B.S0_cyclic B.S0_index hVS_le hconj hV4 hnot
  -- `[S : V] · |V| = |S| = 2n`.
  have hcardrel : (Work.GW2.pCoreIn 2 B.Hhat).relIndex (B.S : Subgroup G) * 4 = 2 * n := by
    have h := Subgroup.relIndex_mul_card (Work.GW2.pCoreIn 2 B.Hhat) (B.S : Subgroup G)
    rw [inf_eq_left.mpr hVS_le, hcardV, hcardS] at h
    exact h
  -- The case `[S : V] = 1` would force `V = S` and contradict `h21`.
  have hne1 : (Work.GW2.pCoreIn 2 B.Hhat).relIndex (B.S : Subgroup G) ≠ 1 := by
    intro hrel
    have hSleV : (B.S : Subgroup G) ≤ Work.GW2.pCoreIn 2 B.Hhat :=
      Subgroup.relIndex_eq_one.mp hrel
    have hSV : (B.S : Subgroup G) = Work.GW2.pCoreIn 2 B.Hhat := le_antisymm hSleV hVS_le
    -- `V = S` is normal in `Ĥ`, hence a normal Sylow `2`-subgroup of `Ĥ`.
    have hEnorm : ((Work.GW2.pCoreIn 2 B.Hhat).subgroupOf B.Hhat).Normal := by
      rw [Subgroup.normal_subgroupOf_iff (pCoreIn_le_Hhat B)]
      intro a b ha hb
      exact conj_mem_pCoreIn B hb ha
    have hVne_bot : (Work.GW2.pCoreIn 2 B.Hhat) ≠ ⊥ := by
      intro hb
      have h4 := hV4.1
      rw [hb, Subgroup.card_bot] at h4
      norm_num at h4
    have hKnorm : B.Hhat ≤ Subgroup.normalizer (Work.GW2.pCoreIn 2 B.Hhat : Set G) :=
      Subgroup.le_normalizer_iff.mpr (fun h hh k hk => conj_mem_pCoreIn B hh hk)
    have hNGeq : Subgroup.normalizer (Work.GW2.pCoreIn 2 B.Hhat : Set G) = B.Hhat :=
      normalizer_eq_of_coatom B.Hhat_coatom (pCoreIn_le_Hhat B) hVne_bot hKnorm
    -- No normal subgroup of `G` has index two.
    have hnoIdx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2 := by
      intro N hN hN2
      haveI : N.Normal := hN
      rcases hctx.simple.eq_bot_or_eq_top_of_normal N with hbot | htop
      · rw [hbot, Subgroup.index_bot] at hN2
        have hdvd : Nat.card ↥(B.S : Subgroup G) ∣ Nat.card G :=
          Subgroup.card_subgroup_dvd_card (B.S : Subgroup G)
        have hle := Nat.le_of_dvd (by omega) hdvd
        omega
      · rw [htop, Subgroup.index_top] at hN2
        exact absurd hN2 (by norm_num)
    -- Every involution of `Ĥ` lies in `V`, and `V`'s involutions are conjugate in `Ĥ`.
    have hone : Work.GW2.OneInvClassIn B.Hhat := by
      intro x hx y hy
      rw [Work.GW2.involutionSet] at hx hy
      simp only [Set.mem_ofPred_eq] at hx hy
      obtain ⟨hxH, hx2⟩ := hx
      obtain ⟨hyH, hy2⟩ := hy
      have hxV : x ∈ Work.GW2.pCoreIn 2 B.Hhat :=
        mem_of_orderOf_eq_two_pow B.S (bSetup_S_le_Hhat B) hEnorm (le_of_eq hSV) hxH
          (n := 1) (by rw [hx2]; norm_num)
      have hyV : y ∈ Work.GW2.pCoreIn 2 B.Hhat :=
        mem_of_orderOf_eq_two_pow B.S (bSetup_S_le_Hhat B) hEnorm (le_of_eq hSV) hyH
          (n := 1) (by rw [hy2]; norm_num)
      have hx1 : x ≠ 1 := by intro h; rw [h, orderOf_one] at hx2; exact absurd hx2 (by norm_num)
      have hy1 : y ≠ 1 := by intro h; rw [h, orderOf_one] at hy2; exact absurd hy2 (by norm_num)
      obtain ⟨g, hgN, hgconj⟩ :=
        (T.fus G B.S n hn2 ⟨e⟩ hnoIdx).2 (Work.GW2.pCoreIn 2 B.Hhat) hV4 x hxV y hyV hx1 hy1
      refine ⟨g, ?_, hgconj⟩
      rw [← hNGeq]
      exact hgN
    exact h21 G hFT hctx B hone
  omega

end Work.CORE2A
