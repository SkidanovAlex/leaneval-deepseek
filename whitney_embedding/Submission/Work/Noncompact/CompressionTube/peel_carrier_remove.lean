import Mathlib
import Submission.Work.Noncompact.CompressionTube.exists_level_arc_of_collar_shell
import Submission.Work.Noncompact.CompressionTube.isPreconnected_sdiff_iUnion_slits_union_finite
import Submission.Work.Noncompact.CompressionTube.level_step_aux
import Submission.Work.Noncompact.Routing.arcs_removal

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

namespace Work.Noncompact.CompressionTube

open Set Topology

/-- A single slit with a free end outside `C`: `C \ γ '' Ioc 0 1 = C \ γ '' Icc 0 1`. -/
lemma sdiff_image_Ioc_eq_sdiff_image_Icc {M : Type*} [TopologicalSpace M] {C : Set M} {γ : ℝ → M}
    (h0 : γ 0 ∉ C) : C \ γ '' Set.Ioc (0:ℝ) 1 = C \ γ '' Set.Icc (0:ℝ) 1 := by
  ext x
  constructor
  · rintro ⟨hxC, hx⟩
    refine ⟨hxC, ?_⟩
    rintro ⟨t, ht, rfl⟩
    rcases eq_or_lt_of_le ht.1 with h | h
    · exact h0 (h ▸ hxC)
    · exact hx ⟨t, ⟨h, ht.2⟩, rfl⟩
  · rintro ⟨hxC, hx⟩
    exact ⟨hxC, fun h => hx (Set.image_mono Set.Ioc_subset_Icc_self h)⟩

/-- **Removing finitely many arcs, each of which is either a compact arc lying in `C` or a slit
with its free end outside `C`.** -/
theorem isPreconnected_sdiff_iUnion_arcs_or_slits {n : ℕ} (hn : 2 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] :
    ∀ (k : ℕ) {γ : Fin k → ℝ → M}, (∀ i, Continuous (γ i)) →
      (∀ i, Set.InjOn (γ i) (Set.Icc (0:ℝ) 1)) →
      ∀ {C : Set M}, IsOpen C → IsPreconnected C →
      (∀ i, γ i '' Set.Icc (0:ℝ) 1 ⊆ C ∨
        (γ i 0 ∉ C ∧ γ i '' Set.Ioc (0:ℝ) 1 ⊆ C) ∨
        Disjoint (γ i '' Set.Icc (0:ℝ) 1) C) →
      (∀ i j, i ≠ j → Disjoint (γ i '' Set.Icc (0:ℝ) 1) (γ j '' Set.Icc (0:ℝ) 1)) →
      IsPreconnected (C \ ⋃ i, γ i '' Set.Icc (0:ℝ) 1) := by
  intro k
  induction k with
  | zero =>
    intro γ _ _ C _ hCc _ _
    simpa using hCc
  | succ k ih =>
    intro γ hγc hγinj C hCo hCc hcond hdisj
    have hdisj0 : ∀ i : Fin k,
        Disjoint (γ i.succ '' Set.Icc (0:ℝ) 1) (γ 0 '' Set.Icc (0:ℝ) 1) :=
      fun i => hdisj i.succ 0 (Fin.succ_ne_zero i)
    have transfer : ∀ (D : Set M), D ⊆ γ 0 '' Set.Icc (0:ℝ) 1 →
        ∀ i : Fin k, γ i.succ '' Set.Icc (0:ℝ) 1 ⊆ C \ D ∨
          (γ i.succ 0 ∉ C \ D ∧ γ i.succ '' Set.Ioc (0:ℝ) 1 ⊆ C \ D) ∨
          Disjoint (γ i.succ '' Set.Icc (0:ℝ) 1) (C \ D) := by
      intro D hD i
      have hdD : Disjoint (γ i.succ '' Set.Icc (0:ℝ) 1) D :=
        Disjoint.mono_right hD (hdisj0 i)
      rcases hcond i.succ with h1 | ⟨h2, h3⟩ | h4
      · left
        intro x hx
        exact ⟨h1 hx, fun hxD => (Set.disjoint_left.mp hdD) hx hxD⟩
      · right; left
        refine ⟨fun h => h2 h.1, ?_⟩
        intro x hx
        exact ⟨h3 hx, fun hxD => (Set.disjoint_left.mp hdD)
          (Set.mem_of_subset_of_mem (Set.image_mono Set.Ioc_subset_Icc_self) hx) hxD⟩
      · right; right
        exact Disjoint.mono_right Set.sdiff_subset h4
    rcases hcond 0 with h0in | ⟨h00, h0Ioc⟩ | h0disj
    · -- a compact arc inside `C`
      set C' : Set M := C \ γ 0 '' Set.Icc (0:ℝ) 1 with hC'def
      have hCo' : IsOpen C' :=
        hCo.sdiff (isCompact_Icc.image (hγc 0)).isClosed
      have hCc' : IsPreconnected C' :=
        Work.Noncompact.Routing.isPreconnected_sdiff_image_arc hn hCo hCc (hγc 0) (hγinj 0)
          (fun t ht => h0in ⟨t, ht, rfl⟩)
      have hmain := ih (fun i : Fin k => hγc i.succ) (fun i : Fin k => hγinj i.succ) hCo' hCc'
        (transfer (γ 0 '' Set.Icc (0:ℝ) 1) subset_rfl)
        (fun i j hij => hdisj i.succ j.succ (fun h => hij (Fin.succ_injective k h)))
      rw [Set.iUnion_fin_add_one_eq_iUnion_succ (fun i => γ i '' Set.Icc (0:ℝ) 1)]
      simp only [Function.comp_def]
      have heq : C \ (γ 0 '' Set.Icc (0:ℝ) 1 ∪
            ⋃ i : Fin k, γ i.succ '' Set.Icc (0:ℝ) 1)
          = C' \ ⋃ i : Fin k, γ i.succ '' Set.Icc (0:ℝ) 1 := by
        rw [hC'def]
        ext x
        simp only [Set.mem_sdiff, Set.mem_union, Set.mem_iUnion]
        constructor
        · rintro ⟨hxC, hnot⟩
          exact ⟨⟨hxC, fun h => hnot (Or.inl h)⟩, fun ⟨i, hi⟩ => hnot (Or.inr ⟨i, hi⟩)⟩
        · rintro ⟨⟨hxC, h1⟩, h2⟩
          refine ⟨hxC, ?_⟩
          rintro (h | ⟨i, hi⟩)
          · exact h1 h
          · exact h2 ⟨i, hi⟩
      rw [heq]
      exact hmain
    · -- a slit with a free end outside `C`
      set C' : Set M := C \ γ 0 '' Set.Ioc (0:ℝ) 1 with hC'def
      have hCo' : IsOpen C' := by
        rw [hC'def, sdiff_image_Ioc_eq_sdiff_image_Icc h00]
        exact hCo.sdiff (isCompact_Icc.image (hγc 0)).isClosed
      have hCc' : IsPreconnected C' := by
        rw [hC'def]
        exact spike_removal (n := n) hn hCo hCc (hγc 0) (hγinj 0) h0Ioc h00
      have hmain := ih (fun i : Fin k => hγc i.succ) (fun i : Fin k => hγinj i.succ) hCo' hCc'
        (transfer (γ 0 '' Set.Ioc (0:ℝ) 1) (Set.image_mono Set.Ioc_subset_Icc_self))
        (fun i j hij => hdisj i.succ j.succ (fun h => hij (Fin.succ_injective k h)))
      rw [Set.iUnion_fin_add_one_eq_iUnion_succ (fun i => γ i '' Set.Icc (0:ℝ) 1)]
      simp only [Function.comp_def]
      have heq : C \ (γ 0 '' Set.Icc (0:ℝ) 1 ∪
            ⋃ i : Fin k, γ i.succ '' Set.Icc (0:ℝ) 1)
          = C' \ ⋃ i : Fin k, γ i.succ '' Set.Icc (0:ℝ) 1 := by
        rw [hC'def, sdiff_image_Ioc_eq_sdiff_image_Icc h00]
        ext x
        simp only [Set.mem_sdiff, Set.mem_union, Set.mem_iUnion]
        constructor
        · rintro ⟨hxC, hnot⟩
          exact ⟨⟨hxC, fun h => hnot (Or.inl h)⟩, fun ⟨i, hi⟩ => hnot (Or.inr ⟨i, hi⟩)⟩
        · rintro ⟨⟨hxC, h1⟩, h2⟩
          refine ⟨hxC, ?_⟩
          rintro (h | ⟨i, hi⟩)
          · exact h1 h
          · exact h2 ⟨i, hi⟩
      rw [heq]
      exact hmain
    · -- the first arc misses `C` altogether
      have hmain := ih (fun i : Fin k => hγc i.succ) (fun i : Fin k => hγinj i.succ) hCo hCc
        (fun i => hcond i.succ)
        (fun i j hij => hdisj i.succ j.succ (fun h => hij (Fin.succ_injective k h)))
      rw [Set.iUnion_fin_add_one_eq_iUnion_succ (fun i => γ i '' Set.Icc (0:ℝ) 1)]
      simp only [Function.comp_def]
      have heq : C \ (γ 0 '' Set.Icc (0:ℝ) 1 ∪
            ⋃ i : Fin k, γ i.succ '' Set.Icc (0:ℝ) 1)
          = C \ ⋃ i : Fin k, γ i.succ '' Set.Icc (0:ℝ) 1 := by
        ext x
        simp only [Set.mem_sdiff, Set.mem_union, Set.mem_iUnion]
        constructor
        · rintro ⟨hxC, hnot⟩
          exact ⟨hxC, fun h => hnot (Or.inr h)⟩
        · rintro ⟨hxC, hnot⟩
          refine ⟨hxC, ?_⟩
          rintro (h | h)
          · exact (Set.disjoint_left.mp h0disj h) hxC
          · exact hnot h
      rw [heq]
      exact hmain

theorem peel_carrier_remove {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {P : Set M} (hPc : IsClosed P) {p : M} (hpP : p ∈ Pᶜ)
    (hnt : ¬ IsCompact (closure (connectedComponentIn (Pᶜ) p)))
    {k : ℕ} {α : Fin k → ℝ → M} {σ : Fin k → ℝ}
    (hαc : ∀ i, Continuous (α i)) (hαi : ∀ i, Set.InjOn (α i) (Set.Icc (0:ℝ) 1))
    (hσ : ∀ i, σ i ∈ Set.Ioo (0:ℝ) 1)
    (hins : ∀ i u, u ∈ Set.Icc (0:ℝ) (σ i) → α i u ∈ connectedComponentIn (Pᶜ) (α i 0))
    (hdisj : ∀ i i', i ≠ i' →
      Disjoint (α i '' Set.Icc (0:ℝ) (σ i)) (α i' '' Set.Icc (0:ℝ) (σ i')))
    {r : ℕ} {slt : Fin r → ℝ → M} (hsltc : ∀ j, Continuous (slt j))
    (hsltinj : ∀ j, Set.InjOn (slt j) (Set.Icc (0:ℝ) 1))
    (hsltbody : ∀ j, slt j '' Set.Ioc (0:ℝ) 1 ⊆ Pᶜ)
    (hsltroot : ∀ j, slt j 0 ∉ Pᶜ)
    (hsltdisj : ∀ j j', j ≠ j' →
      Disjoint (slt j '' Set.Icc (0:ℝ) 1) (slt j' '' Set.Icc (0:ℝ) 1))
    (havoid : ∀ i u, u ∈ Set.Icc (0:ℝ) 1 → ∀ j, slt j 1 ≠ α i 0 →
      α i u ∉ slt j '' Set.Icc (0:ℝ) 1)
    (hown : ∀ i u, u ∈ Set.Ioo (0:ℝ) 1 → ∀ j, slt j 1 = α i 0 →
      α i u ∉ slt j '' Set.Icc (0:ℝ) 1) :
    IsOpen (connectedComponentIn (Pᶜ) p \
        ((⋃ i : Fin k, α i '' Set.Icc (0:ℝ) (σ i)) ∪ (⋃ j : Fin r, slt j '' Set.Ioc (0:ℝ) 1))) ∧
      IsPreconnected (connectedComponentIn (Pᶜ) p \
        ((⋃ i : Fin k, α i '' Set.Icc (0:ℝ) (σ i)) ∪ (⋃ j : Fin r, slt j '' Set.Ioc (0:ℝ) 1))) ∧
      ¬ IsCompact (closure (connectedComponentIn (Pᶜ) p \
        ((⋃ i : Fin k, α i '' Set.Icc (0:ℝ) (σ i)) ∪ (⋃ j : Fin r, slt j '' Set.Ioc (0:ℝ) 1))))
    := by
  classical
  haveI : LocallyPathConnectedSpace M :=
    Work.Whitney.PathTools.locallyPathConnectedSpace_chartedSpace (n := n)
  haveI : LocallyConnectedSpace M := inferInstance
  set C : Set M := connectedComponentIn (Pᶜ) p with hCdef
  have hpC : p ∈ C := by rw [hCdef]; exact mem_connectedComponentIn hpP
  have hCopen : IsOpen C := by rw [hCdef]; exact hPc.isOpen_compl.connectedComponentIn
  have hCpre : IsPreconnected C := by rw [hCdef]; exact isPreconnected_connectedComponentIn
  have hCsub : C ⊆ Pᶜ := by rw [hCdef]; exact connectedComponentIn_subset (Pᶜ) p
  have hor : ∀ {D : Set M}, IsPreconnected D → D ⊆ Pᶜ → D ⊆ C ∨ Disjoint D C := by
    intro D hDpre hDsub
    by_cases h : (D ∩ C).Nonempty
    · left
      obtain ⟨y, hyD, hyC⟩ := h
      have hunion : IsPreconnected (D ∪ C) := IsPreconnected.union' ⟨y, hyD, hyC⟩ hDpre hCpre
      have hsub : D ∪ C ⊆ Pᶜ := Set.union_subset hDsub hCsub
      have hres : D ∪ C ⊆ connectedComponentIn (Pᶜ) p :=
        hunion.subset_connectedComponentIn (Or.inr hpC) hsub
      intro x hx
      rw [hCdef]
      exact hres (Or.inl hx)
    · right
      exact Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp h)
  have hσIoc : ∀ i, σ i ∈ Set.Ioc (0:ℝ) 1 := fun i => ⟨(hσ i).1, (hσ i).2.le⟩
  have hpiece_sub : ∀ i, α i '' Set.Icc (0:ℝ) (σ i) ⊆ Pᶜ := by
    intro i x hx
    obtain ⟨u, hu, rfl⟩ := hx
    exact connectedComponentIn_subset (Pᶜ) (α i 0) (hins i u hu)
  have hpiece_or : ∀ i, α i '' Set.Icc (0:ℝ) (σ i) ⊆ C ∨
      Disjoint (α i '' Set.Icc (0:ℝ) (σ i)) C :=
    fun i => hor (isPreconnected_Icc.image (α i) (hαc i).continuousOn) (hpiece_sub i)
  have hbody_or : ∀ j, slt j '' Set.Ioc (0:ℝ) 1 ⊆ C ∨
      Disjoint (slt j '' Set.Ioc (0:ℝ) 1) C :=
    fun j => hor (isPreconnected_Ioc.image (slt j) (hsltc j).continuousOn) (hsltbody j)
  have hav : ∀ i u, u ∈ Set.Ioo (0:ℝ) 1 → ∀ j, α i u ∉ slt j '' Set.Icc (0:ℝ) 1 := by
    intro i u hu j hmem
    by_cases hh : slt j 1 = α i 0
    · exact hown i u hu j hh hmem
    · exact havoid i u ⟨hu.1.le, hu.2.le⟩ j hh hmem
  have hmemb : ∀ i, α i 0 ∈ (⋃ j : Fin r, slt j '' Set.Ioc (0:ℝ) 1) →
      ∃ j : Fin r, slt j 1 = α i 0 := by
    intro i h
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp h
    obtain ⟨u, hu, hju⟩ := hj
    refine ⟨j, ?_⟩
    by_contra hne
    exact havoid i 0 ⟨le_rfl, zero_le_one⟩ j hne ⟨u, ⟨hu.1.le, hu.2⟩, hju⟩
  have hroot : ∀ j, slt j 0 ∉ C := fun j h => hsltroot j (hCsub h)
  -- Stage 1: remove the slit bodies.
  have hC2pre : IsPreconnected (C \ ⋃ j : Fin r, slt j '' Set.Ioc (0:ℝ) 1) :=
    spike_removal_finite_or (n := n) hn hCopen hCpre (fun j => hsltc j) (fun j => hsltinj j)
      hbody_or hroot hsltdisj
  have hC2open : IsOpen (C \ ⋃ j : Fin r, slt j '' Set.Ioc (0:ℝ) 1) := by
    rw [sdiff_iUnion_Ioc_eq_sdiff_iUnion_Icc (C := C) (σ := slt) (fun j => hroot j)]
    exact hCopen.sdiff (isCompact_iUnion fun j : Fin r => isCompact_Icc.image (hsltc j)).isClosed
  -- Stage 2: remove the inside pieces of the `α`'s.
  have hEimg : ∀ i, (fun u : ℝ => α i (u * σ i)) '' Set.Icc (0:ℝ) 1
      = α i '' Set.Icc (0:ℝ) (σ i) := by
    intro i
    refine Set.Subset.antisymm (isArc_inside_piece (hαc i) (hαi i) (hσIoc i)).2.2 ?_
    rintro x ⟨u, hu, rfl⟩
    refine ⟨u / σ i, ⟨div_nonneg hu.1 (hσIoc i).1.le, ?_⟩, ?_⟩
    · rw [div_le_one (hσIoc i).1]; exact hu.2
    · show α i (u / σ i * σ i) = α i u
      rw [div_mul_cancel₀ u (ne_of_gt (hσIoc i).1)]
  have hEimgIoc : ∀ i, (fun u : ℝ => α i (u * σ i)) '' Set.Ioc (0:ℝ) 1
      = α i '' Set.Ioc (0:ℝ) (σ i) := by
    intro i
    refine Set.Subset.antisymm ?_ ?_
    · rintro x ⟨u, hu, rfl⟩
      exact ⟨u * σ i, ⟨mul_pos hu.1 (hσ i).1, by nlinarith [hu.2, (hσ i).1]⟩, rfl⟩
    · rintro x ⟨v, hv, rfl⟩
      exact ⟨v / σ i, ⟨div_pos hv.1 (hσ i).1, by rw [div_le_one (hσ i).1]; exact hv.2⟩,
        by show α i (v / σ i * σ i) = α i v
           rw [div_mul_cancel₀ v (ne_of_gt (hσ i).1)]⟩
  have hγdisj : ∀ i i', i ≠ i' →
      Disjoint ((fun u : ℝ => α i (u * σ i)) '' Set.Icc (0:ℝ) 1)
        ((fun u : ℝ => α i' (u * σ i')) '' Set.Icc (0:ℝ) 1) := by
    intro i i' hne
    rw [hEimg i, hEimg i']
    exact hdisj i i' hne
  have hγcond : ∀ i, (fun u : ℝ => α i (u * σ i)) '' Set.Icc (0:ℝ) 1 ⊆
        (C \ ⋃ j : Fin r, slt j '' Set.Ioc (0:ℝ) 1) ∨
      ((fun u : ℝ => α i (u * σ i)) 0 ∉ (C \ ⋃ j : Fin r, slt j '' Set.Ioc (0:ℝ) 1) ∧
        (fun u : ℝ => α i (u * σ i)) '' Set.Ioc (0:ℝ) 1 ⊆
          (C \ ⋃ j : Fin r, slt j '' Set.Ioc (0:ℝ) 1)) ∨
      Disjoint ((fun u : ℝ => α i (u * σ i)) '' Set.Icc (0:ℝ) 1)
        (C \ ⋃ j : Fin r, slt j '' Set.Ioc (0:ℝ) 1) := by
    intro i
    by_cases hpair : ∃ j : Fin r, slt j 1 = α i 0
    · rcases hpiece_or i with hsub | hdis
      · right; left
        refine ⟨?_, ?_⟩
        · obtain ⟨j, hj⟩ := hpair
          intro hc
          refine hc.2 (Set.mem_iUnion.mpr ⟨j, ⟨1, ⟨zero_lt_one, le_rfl⟩, ?_⟩⟩)
          show slt j 1 = α i (0 * σ i)
          rw [zero_mul]
          exact hj
        · rw [hEimgIoc i]
          intro x hx
          refine ⟨hsub (Set.image_mono Set.Ioc_subset_Icc_self hx), ?_⟩
          obtain ⟨v, hv, rfl⟩ := hx
          intro hxB
          obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxB
          exact hav i v ⟨hv.1, lt_of_le_of_lt hv.2 (hσ i).2⟩ j
            (Set.mem_of_subset_of_mem (Set.image_mono Set.Ioc_subset_Icc_self) hj)
      · right; right
        rw [hEimg i]
        exact Disjoint.mono_right Set.sdiff_subset hdis
    · rcases hpiece_or i with hsub | hdis
      · left
        rw [hEimg i]
        intro x hx
        refine ⟨hsub hx, ?_⟩
        obtain ⟨v, hv, rfl⟩ := hx
        intro hxB
        rcases eq_or_lt_of_le hv.1 with h0 | hpos
        · rw [← h0] at hxB
          exact hpair (hmemb i hxB)
        · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxB
          exact hav i v ⟨hpos, lt_of_le_of_lt hv.2 (hσ i).2⟩ j
            (Set.mem_of_subset_of_mem (Set.image_mono Set.Ioc_subset_Icc_self) hj)
      · right; right
        rw [hEimg i]
        exact Disjoint.mono_right Set.sdiff_subset hdis
  have hmain : IsPreconnected ((C \ ⋃ j : Fin r, slt j '' Set.Ioc (0:ℝ) 1) \
      ⋃ i : Fin k, (fun u : ℝ => α i (u * σ i)) '' Set.Icc (0:ℝ) 1) :=
    isPreconnected_sdiff_iUnion_arcs_or_slits (n := n) hn k
      (fun i => (isArc_inside_piece (hαc i) (hαi i) (hσIoc i)).1)
      (fun i => (isArc_inside_piece (hαc i) (hαi i) (hσIoc i)).2.1)
      hC2open hC2pre hγcond hγdisj
  have hUnion : (⋃ i : Fin k, (fun u : ℝ => α i (u * σ i)) '' Set.Icc (0:ℝ) 1)
      = ⋃ i : Fin k, α i '' Set.Icc (0:ℝ) (σ i) := by
    ext x
    simp only [Set.mem_iUnion]
    exact ⟨fun ⟨i, hi⟩ => ⟨i, (hEimg i) ▸ hi⟩, fun ⟨i, hi⟩ => ⟨i, (hEimg i).symm ▸ hi⟩⟩
  have hgoal_pre : IsPreconnected (C \ ((⋃ i : Fin k, α i '' Set.Icc (0:ℝ) (σ i)) ∪
      (⋃ j : Fin r, slt j '' Set.Ioc (0:ℝ) 1))) := by
    have heq : (C \ ⋃ j : Fin r, slt j '' Set.Ioc (0:ℝ) 1) \
        ⋃ i : Fin k, (fun u : ℝ => α i (u * σ i)) '' Set.Icc (0:ℝ) 1
        = C \ ((⋃ i : Fin k, α i '' Set.Icc (0:ℝ) (σ i)) ∪
            (⋃ j : Fin r, slt j '' Set.Ioc (0:ℝ) 1)) := by
      rw [hUnion]
      ext x
      simp only [Set.mem_sdiff, Set.mem_union, Set.mem_iUnion]
      constructor
      · rintro ⟨⟨hxC, h1⟩, h2⟩
        exact ⟨hxC, fun h => h.elim h2 h1⟩
      · rintro ⟨hxC, hnot⟩
        exact ⟨⟨hxC, fun ⟨j, hj⟩ => hnot (Or.inr ⟨j, hj⟩)⟩,
          fun ⟨i, hi⟩ => hnot (Or.inl ⟨i, hi⟩)⟩
    rw [← heq]
    exact hmain
  have hgoal_open : IsOpen (C \ ((⋃ i : Fin k, α i '' Set.Icc (0:ℝ) (σ i)) ∪
      (⋃ j : Fin r, slt j '' Set.Ioc (0:ℝ) 1))) := by
    have hB : C \ (⋃ j : Fin r, slt j '' Set.Ioc (0:ℝ) 1)
        = C \ ⋃ j : Fin r, slt j '' Set.Icc (0:ℝ) 1 :=
      sdiff_iUnion_Ioc_eq_sdiff_iUnion_Icc (C := C) (σ := slt) (fun j => hroot j)
    have e1 : C \ ((⋃ i : Fin k, α i '' Set.Icc (0:ℝ) (σ i)) ∪
          (⋃ j : Fin r, slt j '' Set.Ioc (0:ℝ) 1))
        = (C \ (⋃ j : Fin r, slt j '' Set.Ioc (0:ℝ) 1)) \
          (⋃ i : Fin k, α i '' Set.Icc (0:ℝ) (σ i)) := by
      ext x
      simp only [Set.mem_sdiff, Set.mem_union, Set.mem_iUnion]
      constructor
      · rintro ⟨hxC, hnot⟩
        exact ⟨⟨hxC, fun ⟨j, hj⟩ => hnot (Or.inr ⟨j, hj⟩)⟩,
          fun ⟨i, hi⟩ => hnot (Or.inl ⟨i, hi⟩)⟩
      · rintro ⟨⟨hxC, h1⟩, h2⟩
        exact ⟨hxC, fun h => h.elim h2 h1⟩
    have e2 : C \ ((⋃ i : Fin k, α i '' Set.Icc (0:ℝ) (σ i)) ∪
          (⋃ j : Fin r, slt j '' Set.Icc (0:ℝ) 1))
        = (C \ (⋃ j : Fin r, slt j '' Set.Icc (0:ℝ) 1)) \
          (⋃ i : Fin k, α i '' Set.Icc (0:ℝ) (σ i)) := by
      ext x
      simp only [Set.mem_sdiff, Set.mem_union, Set.mem_iUnion]
      constructor
      · rintro ⟨hxC, hnot⟩
        exact ⟨⟨hxC, fun ⟨j, hj⟩ => hnot (Or.inr ⟨j, hj⟩)⟩,
          fun ⟨i, hi⟩ => hnot (Or.inl ⟨i, hi⟩)⟩
      · rintro ⟨⟨hxC, h1⟩, h2⟩
        exact ⟨hxC, fun h => h.elim h2 h1⟩
    rw [e1, hB, ← e2]
    exact hCopen.sdiff
      ((isCompact_iUnion fun i : Fin k => isCompact_Icc.image (hαc i)).isClosed.union
        (isCompact_iUnion fun j : Fin r => isCompact_Icc.image (hsltc j)).isClosed)
  have hgoal_nc : ¬ IsCompact (closure (C \ ((⋃ i : Fin k, α i '' Set.Icc (0:ℝ) (σ i)) ∪
      (⋃ j : Fin r, slt j '' Set.Ioc (0:ℝ) 1)))) := by
    have hAcomp : IsCompact (⋃ i : Fin k, α i '' Set.Icc (0:ℝ) (σ i)) :=
      isCompact_iUnion fun i : Fin k => isCompact_Icc.image (hαc i)
    have hBcc : IsCompact (⋃ j : Fin r, slt j '' Set.Icc (0:ℝ) 1) :=
      isCompact_iUnion fun j : Fin r => isCompact_Icc.image (hsltc j)
    have h1 : ¬ IsCompact (closure (C \ ⋃ i : Fin k, α i '' Set.Icc (0:ℝ) (σ i))) :=
      not_isCompact_closure_sdiff_of_isCompact hnt hAcomp
    have h2 : ¬ IsCompact (closure ((C \ ⋃ i : Fin k, α i '' Set.Icc (0:ℝ) (σ i)) \
        ⋃ j : Fin r, slt j '' Set.Icc (0:ℝ) 1)) :=
      not_isCompact_closure_sdiff_of_isCompact h1 hBcc
    have hsub : (C \ ⋃ i : Fin k, α i '' Set.Icc (0:ℝ) (σ i)) \
          (⋃ j : Fin r, slt j '' Set.Icc (0:ℝ) 1)
        ⊆ C \ ((⋃ i : Fin k, α i '' Set.Icc (0:ℝ) (σ i)) ∪
            (⋃ j : Fin r, slt j '' Set.Ioc (0:ℝ) 1)) := by
      intro x hx
      refine ⟨hx.1.1, ?_⟩
      rintro (hA | hBj)
      · exact hx.1.2 hA
      · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hBj
        exact hx.2 (Set.mem_iUnion.mpr ⟨j,
          Set.mem_of_subset_of_mem (Set.image_mono Set.Ioc_subset_Icc_self) hj⟩)
    intro hc
    exact h2 (hc.of_isClosed_subset isClosed_closure (closure_mono hsub))
  exact ⟨hgoal_open, hgoal_pre, hgoal_nc⟩

end Work.Noncompact.CompressionTube
