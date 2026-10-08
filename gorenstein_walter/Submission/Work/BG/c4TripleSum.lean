import Mathlib
import Submission.Work.BG.ThmABCDefs
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.Thm43Defs
import Submission.Work.BG.L41Aux
import Submission.Work.BG.c4Aux
import Submission.Work.BG.c4TripleAux
import Submission.Work.BG.c4FourOrthogonal
import Submission.Work.BG.c4TripleDistinct

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Work.GW2.C23 in
theorem c4TripleSum {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hC : Work.GW2.C16.Compat D C) (hn : D.n = 2)
    {β₂ : Work.BG.quotGroup C.P →* ℂˣ} (hβ : β₂ ≠ 1)
    {κ : ClassFunction ↥C.P.H0 ℂ} (hκ : Work.GW2.C16.IsKappa D C κ)
    (h41 : Work.GW2.C16.Lemma41Prop D C)
    {μ₂ μ₃ : ClassFunction ↥C.P.H0 ℂ} {ψ₁ ψ₂ ψ₃ ψ₄ : ClassFunction G ℂ}
    (hμ₂ : μ₂ ∈ Work.GW2.C16.S4Index C) (hμ₃ : μ₃ ∈ Work.GW2.C16.S4Index C)
    (hμ₂one : μ₂ 1 = 1) (hμ₃one : μ₃ 1 = 1)
    (hψ1 : Work.BG.IsPmIrr ψ₁) (hψ2 : Work.BG.IsPmIrr ψ₂)
    (hψ3 : Work.BG.IsPmIrr ψ₃) (hψ4 : Work.BG.IsPmIrr ψ₄)
    (heq1 : Work.GW2.C16.delta C β₂ κ = ψ₁ + ψ₂ + ψ₃ + ψ₄)
    (heq2 : Work.GW2.C16.delta C β₂ μ₂ = ψ₁ - ψ₂ + ψ₃ - ψ₄)
    (heq3 : Work.GW2.C16.delta C β₂ μ₃ = ψ₁ + ψ₂ - ψ₃ - ψ₄) :
    ∃ d : ℤ, ψ₁ 1 = (d : ℂ) ∧
      (ψ₁ (C.t : G) ^ 2 / ψ₁ 1 + ψ₂ (C.t : G) ^ 2 / ψ₂ 1 +
        ψ₃ (C.t : G) ^ 2 / ψ₃ 1 + ψ₄ (C.t : G) ^ 2 / ψ₄ 1) = 8 / (d : ℂ) := by
  classical
  have h2 : Nat.card (Work.BG.quotGroup C.P) = 2 := Work.BG.quotGroup_card_two D C hC hn
  have hκS : κ ∈ Work.GW2.C16.S4Index C := Work.BG.kappa_mem_S4Index D C hC hn hκ
  -- norms of the three δ's
  have hN1 : ClassFunction.inner (delta C β₂ κ) (delta C β₂ κ) = 4 := by
    rw [Work.BG.l41_delta_inner_self C h2 hβ hκ.1]
    simp [hκ.2.2.1]
  have hN2 : ClassFunction.inner (delta C β₂ μ₂) (delta C β₂ μ₂) = 4 := by
    rw [Work.BG.l41_delta_inner_self C h2 hβ hμ₂.1]
    simp [hμ₂.2.1]
  have hN3 : ClassFunction.inner (delta C β₂ μ₃) (delta C β₂ μ₃) = 4 := by
    rw [Work.BG.l41_delta_inner_self C h2 hβ hμ₃.1]
    simp [hμ₃.2.1]
  -- distinctness of the three index characters
  have hdist : κ ≠ μ₂ ∧ κ ≠ μ₃ ∧ μ₂ ≠ μ₃ :=
    Work.BG.c4TripleDistinct D C hC hn hβ hκ hμ₂ hμ₃ hψ1 hψ2 hψ3 hψ4 heq1 heq2 heq3
  obtain ⟨hdκμ2, hdκμ3, hdμ2μ3⟩ := hdist
  have ho12 : ClassFunction.inner (delta C β₂ κ) (delta C β₂ μ₂) = 0 :=
    Work.BG.delta_orth D C hC hn hβ hκS hμ₂ hdκμ2.symm
  have ho13 : ClassFunction.inner (delta C β₂ κ) (delta C β₂ μ₃) = 0 :=
    Work.BG.delta_orth D C hC hn hβ hκS hμ₃ hdκμ3.symm
  have ho23 : ClassFunction.inner (delta C β₂ μ₂) (delta C β₂ μ₃) = 0 :=
    Work.BG.delta_orth D C hC hn hβ hμ₂ hμ₃ hdμ2μ3.symm
  -- pairwise orthogonality of ψ₁ … ψ₄
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ :=
    Work.BG.c4FourOrthogonal (delta C β₂ κ) (delta C β₂ μ₂) (delta C β₂ μ₃)
      hψ1 hψ2 hψ3 hψ4 heq1 heq2 heq3 hN1 hN2 hN3 ho12 ho13 ho23
  have hba : ClassFunction.inner ψ₂ ψ₁ = 0 := by
    rw [ClassFunction.inner_star_comm, hab, star_zero]
  have hca : ClassFunction.inner ψ₃ ψ₁ = 0 := by
    rw [ClassFunction.inner_star_comm, hac, star_zero]
  have hda : ClassFunction.inner ψ₄ ψ₁ = 0 := by
    rw [ClassFunction.inner_star_comm, had, star_zero]
  have hcb : ClassFunction.inner ψ₃ ψ₂ = 0 := by
    rw [ClassFunction.inner_star_comm, hbc, star_zero]
  have hdb : ClassFunction.inner ψ₄ ψ₂ = 0 := by
    rw [ClassFunction.inner_star_comm, hbd, star_zero]
  have hdc : ClassFunction.inner ψ₄ ψ₃ = 0 := by
    rw [ClassFunction.inner_star_comm, hcd, star_zero]
  -- the twelve inner products ⟨ψᵢ, δ_ν⟩
  have hi1k : ClassFunction.inner ψ₁ (delta C β₂ κ) = 1 := by
    simp only [heq1, ClassFunction.inner_add_right, IsPmIrr.inner_self hψ1,
      hab, hac, had, add_zero, zero_add]
  have hi1two : ClassFunction.inner ψ₁ (delta C β₂ μ₂) = 1 := by
    simp only [heq2, ClassFunction.inner_sub_right, ClassFunction.inner_add_right,
      IsPmIrr.inner_self hψ1, hab, hac, had, sub_zero, zero_sub, add_zero, zero_add]
  have hi1three : ClassFunction.inner ψ₁ (delta C β₂ μ₃) = 1 := by
    simp only [heq3, ClassFunction.inner_sub_right, ClassFunction.inner_add_right,
      IsPmIrr.inner_self hψ1, hab, hac, had, sub_zero, zero_sub, add_zero, zero_add]
  have hi2k : ClassFunction.inner ψ₂ (delta C β₂ κ) = 1 := by
    simp only [heq1, ClassFunction.inner_add_right, IsPmIrr.inner_self hψ2,
      hba, hbc, hbd, add_zero, zero_add]
  have hi2two : ClassFunction.inner ψ₂ (delta C β₂ μ₂) = -1 := by
    simp only [heq2, ClassFunction.inner_sub_right, ClassFunction.inner_add_right,
      IsPmIrr.inner_self hψ2, hba, hbc, hbd, sub_zero, zero_sub, add_zero, zero_add]
  have hi2three : ClassFunction.inner ψ₂ (delta C β₂ μ₃) = 1 := by
    simp only [heq3, ClassFunction.inner_sub_right, ClassFunction.inner_add_right,
      IsPmIrr.inner_self hψ2, hba, hbc, hbd, sub_zero, zero_sub, add_zero, zero_add]
  have hi3k : ClassFunction.inner ψ₃ (delta C β₂ κ) = 1 := by
    simp only [heq1, ClassFunction.inner_add_right, IsPmIrr.inner_self hψ3,
      hca, hcb, hcd, add_zero, zero_add]
  have hi3two : ClassFunction.inner ψ₃ (delta C β₂ μ₂) = 1 := by
    simp only [heq2, ClassFunction.inner_sub_right, ClassFunction.inner_add_right,
      IsPmIrr.inner_self hψ3, hca, hcb, hcd, sub_zero, zero_sub, add_zero, zero_add]
  have hi3three : ClassFunction.inner ψ₃ (delta C β₂ μ₃) = -1 := by
    simp only [heq3, ClassFunction.inner_sub_right, ClassFunction.inner_add_right,
      IsPmIrr.inner_self hψ3, hca, hcb, hcd, sub_zero, zero_sub, add_zero, zero_add]
  have hi4k : ClassFunction.inner ψ₄ (delta C β₂ κ) = 1 := by
    simp only [heq1, ClassFunction.inner_add_right, IsPmIrr.inner_self hψ4,
      hda, hdb, hdc, add_zero, zero_add]
  have hi4two : ClassFunction.inner ψ₄ (delta C β₂ μ₂) = -1 := by
    simp only [heq2, ClassFunction.inner_sub_right, ClassFunction.inner_add_right,
      IsPmIrr.inner_self hψ4, hda, hdb, hdc, sub_zero, zero_sub, add_zero, zero_add]
  have hi4three : ClassFunction.inner ψ₄ (delta C β₂ μ₃) = -1 := by
    simp only [heq3, ClassFunction.inner_sub_right, ClassFunction.inner_add_right,
      IsPmIrr.inner_self hψ4, hda, hdb, hdc, sub_zero, zero_sub, add_zero, zero_add]
  -- `{κ, μ₂, μ₃} ⊆ bset' …`
  have hmem1k : κ ∈ bset' C β₂ ψ₁ := ⟨hκS, by rw [hi1k]; norm_num⟩
  have hmem1two : μ₂ ∈ bset' C β₂ ψ₁ := ⟨hμ₂, by rw [hi1two]; norm_num⟩
  have hmem1three : μ₃ ∈ bset' C β₂ ψ₁ := ⟨hμ₃, by rw [hi1three]; norm_num⟩
  have hsub1 : ({κ, μ₂, μ₃} : Set (ClassFunction ↥C.P.H0 ℂ)) ⊆ bset' C β₂ ψ₁ := by
    intro ν hν
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hν
    rcases hν with h | h | h
    · rw [h]; exact hmem1k
    · rw [h]; exact hmem1two
    · rw [h]; exact hmem1three
  have hcard3 : ({κ, μ₂, μ₃} : Set (ClassFunction ↥C.P.H0 ℂ)).ncard = 3 := by
    rw [show ({κ, μ₂, μ₃} : Set (ClassFunction ↥C.P.H0 ℂ)) = insert κ (insert μ₂ {μ₃})
        from rfl,
      Set.ncard_insert_of_notMem (by simp [hdκμ2, hdκμ3])
        ((Set.finite_insert).mpr (Set.finite_singleton _)),
      Set.ncard_insert_of_notMem (by simp [hdμ2μ3]) (Set.finite_singleton _),
      Set.ncard_singleton]
  have hn1 : (bset' C β₂ ψ₁).ncard = 1 ∨ (bset' C β₂ ψ₁).ncard = 3 :=
    (h41 hC hn β₂ hβ ψ₁ hψ1 ⟨κ, hmem1k⟩).1
  have hfin1 : (bset' C β₂ ψ₁).Finite := by
    rcases hn1 with h | h
    · exact Set.finite_of_ncard_ne_zero (by rw [h]; norm_num)
    · exact Set.finite_of_ncard_ne_zero (by rw [h]; norm_num)
  have hbset1 : bset' C β₂ ψ₁ = ({κ, μ₂, μ₃} : Set (ClassFunction ↥C.P.H0 ℂ)) := by
    have hn3 : (bset' C β₂ ψ₁).ncard = 3 := by
      rcases hn1 with h | h
      · exfalso
        have hle : ({κ, μ₂, μ₃} : Set (ClassFunction ↥C.P.H0 ℂ)).ncard ≤ (bset' C β₂ ψ₁).ncard :=
          Set.ncard_le_ncard hsub1 hfin1
        rw [hcard3, h] at hle
        norm_num at hle
      · exact h
    exact (Set.eq_of_subset_of_ncard_le hsub1 (by rw [hcard3, hn3]) hfin1).symm
  have hval1 : ψ₁ (C.t : G) = 3 := by
    have h := (h41 hC hn β₂ hβ ψ₁ hψ1 ⟨κ, hmem1k⟩).2.1
    rw [hbset1] at h
    rw [c4TripleAux_finsum_mem_three κ μ₂ μ₃
      (fun ν => ClassFunction.inner ψ₁ (delta C β₂ ν) * ν 1) hdκμ2 hdκμ3 hdμ2μ3] at h
    rw [hi1k, hi1two, hi1three, hκ.2.1, hμ₂one, hμ₃one] at h
    norm_num at h
    exact h
  have hmem2k : κ ∈ bset' C β₂ ψ₂ := ⟨hκS, by rw [hi2k]; norm_num⟩
  have hmem2two : μ₂ ∈ bset' C β₂ ψ₂ := ⟨hμ₂, by rw [hi2two]; norm_num⟩
  have hmem2three : μ₃ ∈ bset' C β₂ ψ₂ := ⟨hμ₃, by rw [hi2three]; norm_num⟩
  have hsub2 : ({κ, μ₂, μ₃} : Set (ClassFunction ↥C.P.H0 ℂ)) ⊆ bset' C β₂ ψ₂ := by
    intro ν hν
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hν
    rcases hν with h | h | h
    · rw [h]; exact hmem2k
    · rw [h]; exact hmem2two
    · rw [h]; exact hmem2three
  have hn2 : (bset' C β₂ ψ₂).ncard = 1 ∨ (bset' C β₂ ψ₂).ncard = 3 :=
    (h41 hC hn β₂ hβ ψ₂ hψ2 ⟨κ, hmem2k⟩).1
  have hfin2 : (bset' C β₂ ψ₂).Finite := by
    rcases hn2 with h | h
    · exact Set.finite_of_ncard_ne_zero (by rw [h]; norm_num)
    · exact Set.finite_of_ncard_ne_zero (by rw [h]; norm_num)
  have hbset2 : bset' C β₂ ψ₂ = ({κ, μ₂, μ₃} : Set (ClassFunction ↥C.P.H0 ℂ)) := by
    have hn3 : (bset' C β₂ ψ₂).ncard = 3 := by
      rcases hn2 with h | h
      · exfalso
        have hle : ({κ, μ₂, μ₃} : Set (ClassFunction ↥C.P.H0 ℂ)).ncard ≤ (bset' C β₂ ψ₂).ncard :=
          Set.ncard_le_ncard hsub2 hfin2
        rw [hcard3, h] at hle
        norm_num at hle
      · exact h
    exact (Set.eq_of_subset_of_ncard_le hsub2 (by rw [hcard3, hn3]) hfin2).symm
  have hval2 : ψ₂ (C.t : G) = 1 := by
    have h := (h41 hC hn β₂ hβ ψ₂ hψ2 ⟨κ, hmem2k⟩).2.1
    rw [hbset2] at h
    rw [c4TripleAux_finsum_mem_three κ μ₂ μ₃
      (fun ν => ClassFunction.inner ψ₂ (delta C β₂ ν) * ν 1) hdκμ2 hdκμ3 hdμ2μ3] at h
    rw [hi2k, hi2two, hi2three, hκ.2.1, hμ₂one, hμ₃one] at h
    norm_num at h
    exact h
  have hmem3k : κ ∈ bset' C β₂ ψ₃ := ⟨hκS, by rw [hi3k]; norm_num⟩
  have hmem3two : μ₂ ∈ bset' C β₂ ψ₃ := ⟨hμ₂, by rw [hi3two]; norm_num⟩
  have hmem3three : μ₃ ∈ bset' C β₂ ψ₃ := ⟨hμ₃, by rw [hi3three]; norm_num⟩
  have hsub3 : ({κ, μ₂, μ₃} : Set (ClassFunction ↥C.P.H0 ℂ)) ⊆ bset' C β₂ ψ₃ := by
    intro ν hν
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hν
    rcases hν with h | h | h
    · rw [h]; exact hmem3k
    · rw [h]; exact hmem3two
    · rw [h]; exact hmem3three
  have hn3' : (bset' C β₂ ψ₃).ncard = 1 ∨ (bset' C β₂ ψ₃).ncard = 3 :=
    (h41 hC hn β₂ hβ ψ₃ hψ3 ⟨κ, hmem3k⟩).1
  have hfin3 : (bset' C β₂ ψ₃).Finite := by
    rcases hn3' with h | h
    · exact Set.finite_of_ncard_ne_zero (by rw [h]; norm_num)
    · exact Set.finite_of_ncard_ne_zero (by rw [h]; norm_num)
  have hbset3 : bset' C β₂ ψ₃ = ({κ, μ₂, μ₃} : Set (ClassFunction ↥C.P.H0 ℂ)) := by
    have hn3 : (bset' C β₂ ψ₃).ncard = 3 := by
      rcases hn3' with h | h
      · exfalso
        have hle : ({κ, μ₂, μ₃} : Set (ClassFunction ↥C.P.H0 ℂ)).ncard ≤ (bset' C β₂ ψ₃).ncard :=
          Set.ncard_le_ncard hsub3 hfin3
        rw [hcard3, h] at hle
        norm_num at hle
      · exact h
    exact (Set.eq_of_subset_of_ncard_le hsub3 (by rw [hcard3, hn3]) hfin3).symm
  have hval3 : ψ₃ (C.t : G) = 1 := by
    have h := (h41 hC hn β₂ hβ ψ₃ hψ3 ⟨κ, hmem3k⟩).2.1
    rw [hbset3] at h
    rw [c4TripleAux_finsum_mem_three κ μ₂ μ₃
      (fun ν => ClassFunction.inner ψ₃ (delta C β₂ ν) * ν 1) hdκμ2 hdκμ3 hdμ2μ3] at h
    rw [hi3k, hi3two, hi3three, hκ.2.1, hμ₂one, hμ₃one] at h
    norm_num at h
    exact h
  have hmem4k : κ ∈ bset' C β₂ ψ₄ := ⟨hκS, by rw [hi4k]; norm_num⟩
  have hmem4two : μ₂ ∈ bset' C β₂ ψ₄ := ⟨hμ₂, by rw [hi4two]; norm_num⟩
  have hmem4three : μ₃ ∈ bset' C β₂ ψ₄ := ⟨hμ₃, by rw [hi4three]; norm_num⟩
  have hsub4 : ({κ, μ₂, μ₃} : Set (ClassFunction ↥C.P.H0 ℂ)) ⊆ bset' C β₂ ψ₄ := by
    intro ν hν
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hν
    rcases hν with h | h | h
    · rw [h]; exact hmem4k
    · rw [h]; exact hmem4two
    · rw [h]; exact hmem4three
  have hn4 : (bset' C β₂ ψ₄).ncard = 1 ∨ (bset' C β₂ ψ₄).ncard = 3 :=
    (h41 hC hn β₂ hβ ψ₄ hψ4 ⟨κ, hmem4k⟩).1
  have hfin4 : (bset' C β₂ ψ₄).Finite := by
    rcases hn4 with h | h
    · exact Set.finite_of_ncard_ne_zero (by rw [h]; norm_num)
    · exact Set.finite_of_ncard_ne_zero (by rw [h]; norm_num)
  have hbset4 : bset' C β₂ ψ₄ = ({κ, μ₂, μ₃} : Set (ClassFunction ↥C.P.H0 ℂ)) := by
    have hn3 : (bset' C β₂ ψ₄).ncard = 3 := by
      rcases hn4 with h | h
      · exfalso
        have hle : ({κ, μ₂, μ₃} : Set (ClassFunction ↥C.P.H0 ℂ)).ncard ≤ (bset' C β₂ ψ₄).ncard :=
          Set.ncard_le_ncard hsub4 hfin4
        rw [hcard3, h] at hle
        norm_num at hle
      · exact h
    exact (Set.eq_of_subset_of_ncard_le hsub4 (by rw [hcard3, hn3]) hfin4).symm
  have hval4 : ψ₄ (C.t : G) = -1 := by
    have h := (h41 hC hn β₂ hβ ψ₄ hψ4 ⟨κ, hmem4k⟩).2.1
    rw [hbset4] at h
    rw [c4TripleAux_finsum_mem_three κ μ₂ μ₃
      (fun ν => ClassFunction.inner ψ₄ (delta C β₂ ν) * ν 1) hdκμ2 hdκμ3 hdμ2μ3] at h
    rw [hi4k, hi4two, hi4three, hκ.2.1, hμ₂one, hμ₃one] at h
    norm_num at h
    exact h
  -- degrees
  have hdeg1 : ψ₁ 1 + ψ₂ 1 + ψ₃ 1 + ψ₄ 1 = 0 := by
    have h := congrArg (fun φ : ClassFunction G ℂ => φ (1 : G)) heq1
    rw [Work.BG.l41_delta_apply_one C hκ.1] at h
    simp only [ClassFunction.add_apply] at h
    exact h.symm
  have hdeg2 : ψ₁ 1 - ψ₂ 1 + ψ₃ 1 - ψ₄ 1 = 0 := by
    have h := congrArg (fun φ : ClassFunction G ℂ => φ (1 : G)) heq2
    rw [Work.BG.l41_delta_apply_one C hμ₂.1] at h
    simp only [ClassFunction.add_apply, ClassFunction.sub_apply] at h
    exact h.symm
  have hdeg3 : ψ₁ 1 + ψ₂ 1 - ψ₃ 1 - ψ₄ 1 = 0 := by
    have h := congrArg (fun φ : ClassFunction G ℂ => φ (1 : G)) heq3
    rw [Work.BG.l41_delta_apply_one C hμ₃.1] at h
    simp only [ClassFunction.add_apply, ClassFunction.sub_apply] at h
    exact h.symm
  have he4 : ψ₄ 1 = -ψ₂ 1 := by
    linear_combination (1 / 2 : ℂ) * hdeg1 - (1 / 2 : ℂ) * hdeg2
  have hc3 : ψ₃ 1 = -ψ₄ 1 := by
    linear_combination (1 / 2 : ℂ) * hdeg1 - (1 / 2 : ℂ) * hdeg3
  have hb2 : ψ₂ 1 = -ψ₁ 1 := by
    have h := hdeg1
    rw [hc3, he4] at h
    linear_combination h
  -- extract `d` and finish
  obtain ⟨d, _hdodd, hdval⟩ := (h41 hC hn β₂ hβ ψ₁ hψ1 ⟨κ, hmem1k⟩).2.2
  refine ⟨d, hdval, ?_⟩
  have hden : (d : ℂ) ≠ 0 := by
    rw [← hdval]; exact IsPmIrr.apply_one_ne_zero hψ1
  have e2 : ψ₂ 1 = -(d : ℂ) := by rw [hb2, hdval]
  have e3 : ψ₃ 1 = -(d : ℂ) := by rw [hc3, he4, hb2, hdval]; ring
  have e4v : ψ₄ 1 = (d : ℂ) := by rw [he4, hb2, hdval]; ring
  rw [hval1, hval2, hval3, hval4, hdval, e2, e3, e4v]
  field_simp
  ring

end Work.BG
