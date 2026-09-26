import Submission.Commons.Topology.Strip.barrier_bottom_top_of_no_left_right

namespace Commons.Topology.Strip

open Set

/-- Auxiliary: the "transpose" map `(x,y) ↦ (y,x)` is continuous. -/
private lemma continuous_swap_prod : Continuous (fun q : ℝ × ℝ => (q.2, q.1)) := by fun_prop

theorem exists_preconnected_wall_of_not_joinedIn {F : Set (ℝ × ℝ)}
    (hF : IsClosed (F ∪ {q : ℝ × ℝ | q.2 ≤ 0 ∨ 1 ≤ q.2}))
    (hstrip : F ⊆ {q : ℝ × ℝ | 0 < q.2 ∧ q.2 < 1})
    {M : ℝ} (hM : 0 < M)
    (hsep : ¬ JoinedIn ((({q : ℝ × ℝ | 0 ≤ q.2 ∧ q.2 ≤ 1}) \ F))
      ((0:ℝ), (0:ℝ)) ((0:ℝ), (1:ℝ))) :
    ∃ C : Set (ℝ × ℝ),
      C ⊆ closure F ∧
      C ⊆ {q : ℝ × ℝ | 0 ≤ q.1 ∧ q.1 ≤ M ∧ 0 ≤ q.2 ∧ q.2 ≤ 1} ∧
      IsClosed C ∧ IsPreconnected C ∧
      (C ∩ {q : ℝ × ℝ | q.1 = 0}).Nonempty ∧
      (C ∩ {q : ℝ × ℝ | q.1 = M}).Nonempty := by
  -- The rectangle `[0,M] × [0,1]`.
  set S : Set (ℝ × ℝ) := {q : ℝ × ℝ | 0 ≤ q.1 ∧ q.1 ≤ M ∧ 0 ≤ q.2 ∧ q.2 ≤ 1} with hS
  have hS_closed : IsClosed S := by
    have hEq : S = Set.Icc (0:ℝ) M ×ˢ Set.Icc (0:ℝ) 1 := by
      rw [hS]; ext q; simp only [Set.mem_prod, Set.mem_Icc, Set.mem_ofPred_eq]; tauto
    rw [hEq]; exact isClosed_Icc.prod isClosed_Icc
  -- The closed set `K = closure F ∩ S`.
  set K : Set (ℝ × ℝ) := closure F ∩ S with hK
  have hK_closed : IsClosed K := by rw [hK]; exact isClosed_closure.inter hS_closed
  -- The transpose `K'` of `K`.
  set sw : (ℝ × ℝ) → (ℝ × ℝ) := fun q => (q.2, q.1) with hsw
  have hsw_cont : Continuous sw := by rw [hsw]; exact continuous_swap_prod
  set K' : Set (ℝ × ℝ) := sw ⁻¹' K with hK'
  have hK'_closed : IsClosed K' := by rw [hK']; exact hK_closed.preimage hsw_cont
  have hK'_sub : K' ⊆ {q : ℝ × ℝ | 0 ≤ q.1 ∧ q.1 ≤ 1 ∧ 0 ≤ q.2 ∧ q.2 ≤ M} := by
    intro q hq
    have hqK : sw q ∈ K := by rwa [hK'] at hq
    have hqS : sw q ∈ S := by rw [hK] at hqK; exact hqK.2
    rw [hS] at hqS
    rw [hsw] at hqS
    simp only [Set.mem_ofPred_eq] at hqS
    exact ⟨hqS.2.2.1, hqS.2.2.2, hqS.1, hqS.2.1⟩
  -- The key obstruction property: no path in the transposed rectangle joins the two vertical edges.
  have hno' : ∀ γ : C(Set.Icc (0:ℝ) 1, ℝ × ℝ),
      (∀ t, γ t ∈ {q : ℝ × ℝ | 0 ≤ q.1 ∧ q.1 ≤ 1 ∧ 0 ≤ q.2 ∧ q.2 ≤ M}) →
      (γ 0 ∈ ({q : ℝ × ℝ | q.1 = 0} : Set (ℝ × ℝ))) →
      (γ 1 ∈ ({q : ℝ × ℝ | q.1 = 1} : Set (ℝ × ℝ))) →
      (∀ t, γ t ∉ K') → False := by
    intro γ hγ hγ0 hγ1 hγK'
    have hγb : ∀ t, (0:ℝ) ≤ (γ t).1 ∧ (γ t).1 ≤ 1 ∧ 0 ≤ (γ t).2 ∧ (γ t).2 ≤ M := by
      intro t
      have h := hγ t
      simp only [Set.mem_ofPred_eq] at h
      exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
    have hg0 : (γ 0).1 = 0 := by simpa only [Set.mem_ofPred_eq] using hγ0
    have hg1 : (γ 1).1 = 1 := by simpa only [Set.mem_ofPred_eq] using hγ1
    -- The transposed path
    let δc : C(Set.Icc (0:ℝ) 1, ℝ × ℝ) := ⟨fun t => ((γ t).2, (γ t).1), by fun_prop⟩
    let hδpath : Path ((γ 0).2, (γ 0).1) ((γ 1).2, (γ 1).1) := ⟨δc, rfl, rfl⟩
    have hδmem : ∀ t, δc t ∈ (({q : ℝ × ℝ | 0 ≤ q.2 ∧ q.2 ≤ 1}) \ F) := by
      intro t
      refine ⟨⟨(hγb t).1, (hγb t).2.1⟩, ?_⟩
      intro hFmem
      apply hγK' t
      rw [hK']
      show sw (γ t) ∈ K
      rw [hK]
      refine ⟨subset_closure hFmem, ?_⟩
      rw [hS]
      exact ⟨(hγb t).2.2.1, (hγb t).2.2.2, (hγb t).1, (hγb t).2.1⟩
    -- The bottom leg
    have hA : JoinedIn (({q : ℝ × ℝ | 0 ≤ q.2 ∧ q.2 ≤ 1}) \ F)
        ((0:ℝ), (0:ℝ)) ((γ 0).2, (γ 0).1) := by
      apply JoinedIn.ofLine (f := fun t : ℝ => (t * (γ 0).2, (0:ℝ)))
      · fun_prop
      · simp
      · show (1 * (γ 0).2, (0:ℝ)) = ((γ 0).2, (γ 0).1)
        rw [hg0]; simp
      · rintro z ⟨t, ht, rfl⟩
        refine ⟨⟨le_refl 0, zero_le_one⟩, ?_⟩
        intro hmem
        exact absurd (hstrip hmem).1 (lt_irrefl 0)
    -- The top leg
    have hC : JoinedIn (({q : ℝ × ℝ | 0 ≤ q.2 ∧ q.2 ≤ 1}) \ F)
        ((γ 1).2, (γ 1).1) ((0:ℝ), (1:ℝ)) := by
      apply JoinedIn.ofLine (f := fun t : ℝ => ((1 - t) * (γ 1).2, (1:ℝ)))
      · fun_prop
      · show ((1 - 0) * (γ 1).2, (1:ℝ)) = ((γ 1).2, (γ 1).1)
        rw [hg1]; simp
      · simp
      · rintro z ⟨t, ht, rfl⟩
        refine ⟨⟨zero_le_one, le_refl 1⟩, ?_⟩
        intro hmem
        exact absurd (hstrip hmem).2 (lt_irrefl 1)
    exact hsep ((hA.trans ⟨hδpath, hδmem⟩).trans hC)
  obtain ⟨C', hC'K', hC'pre, hC'bot, hC'top⟩ :=
    barrier_bottom_top_of_no_left_right (p := 1) (a := 0) (b := M)
      (by norm_num) hM hK'_sub hK'_closed hno'
  -- Transport back.
  set C : Set (ℝ × ℝ) := sw '' C' with hC
  have hCpre : IsPreconnected C := by
    rw [hC]; exact hC'pre.image sw hsw_cont.continuousOn
  have hCK : C ⊆ K := by
    rintro q ⟨r, hrC', rfl⟩
    have h : r ∈ K' := hC'K' hrC'
    rwa [hK'] at h
  have hCsubF : C ⊆ closure F := by
    intro q hq
    have hqK := hCK hq
    rw [hK] at hqK
    exact hqK.1
  have hCsubS : C ⊆ S := by
    intro q hq
    have hqK := hCK hq
    rw [hK] at hqK
    exact hqK.2
  have hCmeet0 : (C ∩ {q : ℝ × ℝ | q.1 = 0}).Nonempty := by
    obtain ⟨r, hrC', hr0⟩ := hC'bot
    have hr0' : r.2 = 0 := by simpa only [Set.mem_ofPred_eq] using hr0
    refine ⟨sw r, ⟨⟨r, hrC', rfl⟩, ?_⟩⟩
    show (sw r).1 = 0
    simpa [hsw] using hr0'
  have hCmeetM : (C ∩ {q : ℝ × ℝ | q.1 = M}).Nonempty := by
    obtain ⟨r, hrC', hrM⟩ := hC'top
    have hrM' : r.2 = M := by simpa only [Set.mem_ofPred_eq] using hrM
    refine ⟨sw r, ⟨⟨r, hrC', rfl⟩, ?_⟩⟩
    show (sw r).1 = M
    simpa [hsw] using hrM'
  refine ⟨closure C, ?_, ?_, isClosed_closure, hCpre.closure, ?_, ?_⟩
  · exact closure_minimal hCsubF isClosed_closure
  · exact closure_minimal hCsubS hS_closed
  · obtain ⟨q, hq1, hq2⟩ := hCmeet0
    exact ⟨q, subset_closure hq1, hq2⟩
  · obtain ⟨q, hq1, hq2⟩ := hCmeetM
    exact ⟨q, subset_closure hq1, hq2⟩

end Commons.Topology.Strip
