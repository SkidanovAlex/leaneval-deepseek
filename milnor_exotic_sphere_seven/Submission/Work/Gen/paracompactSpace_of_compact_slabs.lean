import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Gen

open Set Filter Topology

/-- **A space with a family of compact-fibred "slabs" which escapes to infinity is paracompact.**

This adapts `Work.LerayHirsch.paracompactSpace_of_compact_fibres`
(`Submission/Work/LerayHirsch/paracompactSpace_projSpace.lean`): instead of asking that every fibre
`π ⁻¹' {b}` be compact, one only asks that the *slab* `K m ∩ π ⁻¹' {b}` be compact for all `m, b`,
that each slab sit in the open enlargement `O m`, that the slabs cover `X`, and that the enlargements
*escape to infinity* (every point has a neighbourhood meeting only finitely many of them).  The
family is indexed by `ℤ` so that the slabs may accumulate neither at `0` nor at `∞`.

Proof (adapt the proof of `paracompactSpace_of_compact_fibres`): given an open cover `s : α → Set X`,
use `hm` to pick a finite `t m b : Finset α` covering `K m ∩ π ⁻¹' {b}`, and `htube` to fatten it to
`W m b ∈ 𝓝 b` with `π ⁻¹' (W m b) ∩ K m ⊆ ⋃ a ∈ t m b, s a`.  For each `m`, `precise_refinement` in
the paracompact base `B` refines `{W m b}_b` by a locally finite open cover `{w m b}_b`; take the
refinement of the cover of `X` indexed by `(m, b, a)` with pieces
`π ⁻¹' (w m b) ∩ O m ∩ s a` for `a ∈ t m b` (and `∅` otherwise) — using `O m` rather than `K m`
so that the pieces are open, which is harmless for the covering step because `K m ⊆ O m`.
Covering follows from `hcov`, `hKO` and the construction; local finiteness at `x` from `hescape`
(finitely many `m` matter, since each piece is contained in `O m`), from the local finiteness of
`{w m b}_b` at `π x`, and from the finiteness of the `t m b`.  The refinement family is indexed by
`ℤ × (B × α)`, a type possibly in a larger universe than `X`; it is reindexed by its range, which
always lives in the universe of `Set X`. -/
theorem paracompactSpace_of_compact_slabs {X : Type*} [TopologicalSpace X] {B : Type*}
    [TopologicalSpace B] [ParacompactSpace B] (π : ContinuousMap X B) (K O : ℤ → Set X)
    (hOopen : ∀ m : ℤ, IsOpen (O m)) (hKO : ∀ m : ℤ, K m ⊆ O m)
    (hcov : ∀ x : X, ∃ m : ℤ, x ∈ K m)
    (hescape : ∀ x : X, ∃ U ∈ nhds x, {m : ℤ | (U ∩ O m).Nonempty}.Finite)
    (hm : ∀ (m : ℤ) (b : B), IsCompact (K m ∩ π ⁻¹' {b}))
    (htube : ∀ (m : ℤ) (b : B) (P : Set X), IsOpen P → K m ∩ π ⁻¹' {b} ⊆ P →
      ∃ W ∈ nhds b, π ⁻¹' W ∩ K m ⊆ P) :
    ParacompactSpace X := by
  classical
  refine ⟨fun α s hs hscov => ?_⟩
  -- finitely many members of the cover already cover each slab over each point of the base
  have hfin : ∀ (m : ℤ) (b : B), ∃ t : Finset α, K m ∩ π ⁻¹' {b} ⊆ ⋃ a ∈ t, s a := by
    intro m b
    refine (hm m b).elim_finite_subcover s hs ?_
    intro x hx
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp (by rw [hscov]; exact Set.mem_univ x)
    exact Set.mem_iUnion.mpr ⟨a, ha⟩
  choose tt ht using hfin
  -- the tube around each slab-fibre
  have htub : ∀ (m : ℤ) (b : B), ∃ W : Set B, W ∈ 𝓝 b ∧ π ⁻¹' W ∩ K m ⊆ ⋃ a ∈ tt m b, s a := by
    intro m b
    exact htube m b _ (isOpen_biUnion fun a _ => hs a) (ht m b)
  choose WW hW hWsub using htub
  -- open neighbourhoods inside the tubes
  have hV : ∀ (m : ℤ) (b : B), ∃ V : Set B, IsOpen V ∧ b ∈ V ∧ V ⊆ WW m b := by
    intro m b
    obtain ⟨V, ⟨hbV, hVopen⟩, hVW⟩ := (nhds_basis_opens b).mem_iff.mp (hW m b)
    exact ⟨V, hVopen, hbV, hVW⟩
  choose vv hvopen hbv hvW using hV
  -- the locally finite refinement of each of the base covers `{V m b}_b`
  have hprec : ∀ m : ℤ, ∃ w : B → Set B, (∀ b, IsOpen (w b)) ∧ (⋃ b, w b = univ) ∧
      LocallyFinite w ∧ ∀ b, w b ⊆ vv m b := by
    intro m
    exact precise_refinement (vv m) (fun b => hvopen m b) (by
      rw [Set.eq_univ_iff_forall]; exact fun b => Set.mem_iUnion.mpr ⟨b, hbv m b⟩)
  choose ww hwopen hwcov hwfin hwsub using hprec
  -- the refinement family
  let F : ℤ × (B × α) → Set X := fun γ =>
    if γ.2.2 ∈ tt γ.1 γ.2.1 then π ⁻¹' (ww γ.1 γ.2.1) ∩ O γ.1 ∩ s γ.2.2 else ∅
  have hFdef : ∀ (m : ℤ) (b : B) (a : α),
      F (m, b, a) = if a ∈ tt m b then π ⁻¹' (ww m b) ∩ O m ∩ s a else ∅ := fun m b a => rfl
  have hFopen : ∀ γ, IsOpen (F γ) := by
    rintro ⟨m, b, a⟩
    rw [hFdef m b a]
    by_cases h : a ∈ tt m b
    · rw [if_pos h]
      exact (((hwopen m b).preimage π.continuous).inter (hOopen m)).inter (hs a)
    · rw [if_neg h]; exact isOpen_empty
  have hFcov : (⋃ γ, F γ) = univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    obtain ⟨m, hmK⟩ := hcov x
    have hxw : π x ∈ ⋃ b, ww m b := by rw [hwcov m]; exact Set.mem_univ _
    obtain ⟨b, hbw⟩ := Set.mem_iUnion.mp hxw
    have hxW : x ∈ π ⁻¹' (WW m b) ∩ K m :=
      ⟨by rw [Set.mem_preimage]; exact hvW m b (hwsub m b hbw), hmK⟩
    obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp (hWsub m b hxW)
    refine Set.mem_iUnion.mpr ⟨(m, b, a), ?_⟩
    rw [hFdef m b a, if_pos ha]
    exact ⟨⟨by rw [Set.mem_preimage]; exact hbw, hKO m hmK⟩, hxa⟩
  have hFsub : ∀ γ, ∃ a, F γ ⊆ s a := by
    rintro ⟨m, b, a⟩
    rw [hFdef m b a]
    by_cases h : a ∈ tt m b
    · rw [if_pos h]; exact ⟨a, Set.inter_subset_right⟩
    · rw [if_neg h]; exact ⟨a, Set.empty_subset _⟩
  have hFfin : LocallyFinite F := by
    intro x
    obtain ⟨U, hU, hUfin⟩ := hescape x
    have hM : ∀ m : ℤ, ∃ M : Set B, M ∈ 𝓝 (π x) ∧ {b : B | (ww m b ∩ M).Nonempty}.Finite :=
      fun m => hwfin m (π x)
    choose MM hMM hMMfin using hM
    set S : Finset ℤ := hUfin.toFinset with hSdef
    have hSmem : ∀ m : ℤ, m ∈ S ↔ (U ∩ O m).Nonempty := fun m => hUfin.mem_toFinset
    have hMbig : (⋂ m ∈ S, MM m) ∈ 𝓝 (π x) := by
      rw [Filter.biInter_finset_mem]
      exact fun m _ => hMM m
    refine ⟨U ∩ π ⁻¹' (⋂ m ∈ S, MM m),
      Filter.inter_mem hU ((π.continuous.continuousAt).preimage_mem_nhds hMbig), ?_⟩
    have hBbig : (⋃ m ∈ (S : Set ℤ), {b : B | (ww m b ∩ MM m).Nonempty}).Finite :=
      Set.Finite.biUnion S.finite_toSet fun m _ => hMMfin m
    have hD : (⋃ m ∈ (S : Set ℤ), ⋃ b ∈ {b : B | (ww m b ∩ MM m).Nonempty},
        (tt m b : Set α)).Finite := by
      refine Set.Finite.biUnion S.finite_toSet fun m _ => ?_
      exact Set.Finite.biUnion (hMMfin m) fun b _ => (tt m b).finite_toSet
    have hbig : ((S : Set ℤ) ×ˢ
        ((⋃ m ∈ (S : Set ℤ), {b : B | (ww m b ∩ MM m).Nonempty}) ×ˢ
        (⋃ m ∈ (S : Set ℤ), ⋃ b ∈ {b : B | (ww m b ∩ MM m).Nonempty},
          (tt m b : Set α)))).Finite :=
      S.finite_toSet.prod (hBbig.prod hD)
    refine hbig.subset fun γ hγ => ?_
    obtain ⟨m, b, a⟩ := γ
    obtain ⟨y, hyF, hyU, hyM⟩ := hγ
    have ha_t : a ∈ tt m b := by
      by_contra h
      have h0 := hyF
      rw [hFdef m b a, if_neg h] at h0
      exact h0
    have hyF' : y ∈ π ⁻¹' (ww m b) ∩ O m ∩ s a := by
      have h0 := hyF
      rw [hFdef m b a, if_pos ha_t] at h0
      exact h0
    have hpre : π y ∈ ww m b := hyF'.1.1
    have hyO : y ∈ O m := hyF'.1.2
    have hmS : m ∈ S := (hSmem m).mpr ⟨y, hyU, hyO⟩
    have hMMm : π y ∈ MM m := Set.mem_iInter₂.mp hyM m hmS
    have hbne : (ww m b ∩ MM m).Nonempty := ⟨π y, hpre, hMMm⟩
    refine ⟨hmS, ?_, ?_⟩
    · exact Set.mem_iUnion₂.mpr ⟨m, hmS, hbne⟩
    · exact Set.mem_iUnion₂.mpr ⟨m, hmS, Set.mem_iUnion₂.mpr ⟨b, hbne, ha_t⟩⟩
  -- reindex the family by its range, so that the index type lies in the universe of `X`
  refine ⟨Set.range F, Subtype.val, ?_, ?_, ?_, ?_⟩
  · rintro ⟨t', ht'⟩
    obtain ⟨γ, rfl⟩ := ht'
    exact hFopen γ
  · rw [Set.eq_univ_iff_forall]
    intro x
    obtain ⟨γ, hγ⟩ := Set.mem_iUnion.mp (by rw [hFcov]; exact Set.mem_univ x)
    exact Set.mem_iUnion.mpr ⟨⟨F γ, Set.mem_range_self γ⟩, hγ⟩
  · exact hFfin.on_range
  · rintro ⟨t', ht'⟩
    obtain ⟨γ, rfl⟩ := ht'
    obtain ⟨a, ha⟩ := hFsub γ
    exact ⟨a, ha⟩

end Work.Gen
