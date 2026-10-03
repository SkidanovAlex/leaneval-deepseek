import Mathlib
import Submission.Lib.Unif2.Commons.Topology.Surface.exists_locallyFinite_disk_tiling
import Submission.Lib.Unif2.Work.Topology.Engulf.engulf_precompact_connected_superset
import Submission.Lib.Unif2.Work.Topology.Engulf.exists_finset_tiles_engulfing
import Submission.Lib.Unif2.Work.Topology.Engulf.filling_of_finite_closed_cover

/-!
# Engulfing a compact set by a precompact open set with no bounded complementary component

Let `X` be a connected, locally compact, locally connected, locally path connected, second countable
`ℂ`-charted `C¹` surface and `K ⊆ X` compact.  We construct an open connected `Ω ⊇ K` with compact
closure such that **no** connected component of `Ωᶜ` is relatively compact.

## Route

Work with the locally finite closed tiling `D` of `X` by closed discs with pairwise disjoint interiors
(`Commons.Topology.Surface.exists_locallyFinite_disk_tiling`).

1. `subset_interior_biUnion_of_forall_inter_nonempty`: if a finite set `s` of tiles contains every tile
   meeting a set `B`, then `B ⊆ int (⋃ i ∈ s, D i)`.  (The tiles *containing* a point of `B` cover a
   neighbourhood of it — the local structure of the tiling.)  The special case
   `mem_interior_biUnion_of_mem_all_tiles`: a point whose every tile lies in `s` is interior to the
   union.
2. Start with an open connected precompact `Ω₀ ⊇ K`
   (`exists_isOpen_isConnected_isCompact_closure_superset`), let `s₁` be the (finite) set of tiles
   meeting `closure Ω₀`, so that `closure Ω₀ ⊆ int (⋃ i ∈ s₁, D i)`.
3. Apply the filling lemma `exists_finset_tiles_engulfing` to the compact set `⋃ i ∈ s₁, D i`: this
   gives a finite `s ⊇ s₁` with `L := ⋃ i ∈ s, D i` such that **every** component of `Lᶜ` has
   non-compact closure.
4. Take `Ω` to be the connected component of `int L` containing `x₀ ∈ Ω₀`.  Then `Ω` is open and
   connected, `K ⊆ Ω₀ ⊆ Ω`, and `closure Ω ⊆ L` is compact.
5. Two facts finish the proof, and both are *elementary* once the tiling is in hand (no tameness of
   the tiles is needed):
   * `not_isCompact_closure_componentIn_compl_interior`: every component of `(int L)ᶜ` has non-compact
     closure.  If such a component `Z` met `Lᶜ` we would be done (it contains a component of `Lᶜ`);
     if `Z ∩ Lᶜ = ∅` then `Z ⊆ ∂L`; but a point `x ∈ Z` lies in some tile `D j` with `j ∉ s` (else `x`
     would be interior to `L`), and the whole tile `D j` is connected and contained in `(int L)ᶜ`, so
     it lies in `Z`, giving `int (D j) ⊆ Z ∩ Lᶜ ≠ ∅` — a contradiction.
   * `not_isCompact_closure_componentIn_compl_of_mem_interior_component`: the same argument applied to
     a point `x ∈ int L` lying in a *different* component `W` of `int L`: `∂W ≠ ∅` (otherwise `W` is
     clopen, hence all of `X`, which is non-compact), a point `x' ∈ ∂W` lies in the `Ωᶜ`-component `Cx`
     of `x`, and as before `x'` lies in a tile outside `s`, whose interior is contained in `Cx ∩ Lᶜ`.
-/

namespace Work.Topology.Engulf

open Set Filter

variable {X : Type*} [TopologicalSpace X]

/-! ## The local structure of the tiling -/

/-- A set homeomorphic to the closed unit disc is preconnected. -/
lemma isPreconnected_of_homeomorph_closedBall' {D : Set X}
    (h : Nonempty (Metric.closedBall (0 : ℂ) 1 ≃ₜ ↥D)) : IsPreconnected D := by
  obtain ⟨e⟩ := h
  haveI : ConnectedSpace ↥(Metric.closedBall (0 : ℂ) 1) :=
    isConnected_iff_connectedSpace.mp
      ((convex_closedBall (0 : ℂ) 1).isConnected ⟨0, Metric.mem_closedBall_self (by norm_num)⟩)
  exact (isConnected_iff_connectedSpace.mpr (e.connectedSpace_iff.mp inferInstance)).isPreconnected

/-- Two connected components of the same set that meet are equal. -/
lemma eq_of_inter_nonempty_connectedComponentIn {F : Set X} {x y z : X}
    (hzx : z ∈ connectedComponentIn F x) (hzy : z ∈ connectedComponentIn F y) :
    connectedComponentIn F x = connectedComponentIn F y :=
  (connectedComponentIn_eq hzx).trans (connectedComponentIn_eq hzy).symm

/-- **The one-step neighbourhood.**  If a finite set `s` of tiles contains every tile meeting a set
`B`, then `B` is contained in the interior of `⋃ i ∈ s, D i`.

This is the local structure of a locally finite tiling by closed discs: at a point of `B` only
finitely many tiles can meet a small neighbourhood, and those tiles not containing the point are at
positive distance from it. -/
theorem subset_interior_biUnion_of_forall_inter_nonempty {ι : Type*} {D : ι → Set X}
    (hlf : LocallyFinite D) (hcover : ⋃ i, D i = Set.univ) (hclosed : ∀ i, IsClosed (D i))
    {B : Set X} {s : Finset ι} (hs : ∀ i, (D i ∩ B).Nonempty → i ∈ s) :
    B ⊆ interior (⋃ i ∈ s, D i) := by
  intro x hxB
  obtain ⟨W, hWmem, hWfin⟩ := hlf x
  classical
  set F : Finset ι := hWfin.toFinset with hFdef
  have hFmem : ∀ i, i ∈ F ↔ (D i ∩ W).Nonempty := fun i => hWfin.mem_toFinset
  set E : Set X := ⋃ i ∈ F, (if i ∈ s then ∅ else D i) with hEdef
  have hEcl : IsClosed E := by
    rw [hEdef]
    exact isClosed_biUnion_finset fun i _ => by
      by_cases his : i ∈ s
      · simp [his]
      · simpa [his] using hclosed i
  have hxE : x ∉ E := by
    intro hxEin
    rw [hEdef] at hxEin
    obtain ⟨i, hiF, hxi⟩ := Set.mem_iUnion₂.mp hxEin
    by_cases his : i ∈ s
    · exact absurd (by simpa [his] using hxi) (Set.notMem_empty x)
    · have hdisj : D i ∩ B = ∅ := by
        by_contra hcon
        exact his (hs i (Set.nonempty_iff_ne_empty.mpr hcon))
      exact (Set.eq_empty_iff_forall_notMem.mp hdisj) x ⟨by simpa [his] using hxi, hxB⟩
  have hUsub : W ∩ Eᶜ ⊆ ⋃ i ∈ s, D i := by
    intro y hy
    obtain ⟨hyW, hyE⟩ := hy
    obtain ⟨i, hyi⟩ := Set.mem_iUnion.mp (by rw [hcover]; exact Set.mem_univ y)
    by_cases his : i ∈ s
    · exact Set.mem_iUnion₂.mpr ⟨i, his, hyi⟩
    · exact absurd (show y ∈ E from by
        rw [hEdef]
        exact Set.mem_iUnion₂.mpr ⟨i, (hFmem i).mpr ⟨y, hyi, hyW⟩, by simpa [his] using hyi⟩) hyE
  have hUmem : W ∩ Eᶜ ∈ nhds x :=
    Filter.inter_mem hWmem (hEcl.isOpen_compl.mem_nhds hxE)
  exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset hUmem hUsub)

/-- **A point all of whose tiles lie in `s` is interior to the union.** -/
theorem mem_interior_biUnion_of_mem_all_tiles {ι : Type*} {D : ι → Set X}
    (hlf : LocallyFinite D) (hcover : ⋃ i, D i = Set.univ) (hclosed : ∀ i, IsClosed (D i))
    {s : Finset ι} {x : X} (hx : ∀ i, x ∈ D i → i ∈ s) :
    x ∈ interior (⋃ i ∈ s, D i) := by
  classical
  have hfin := hlf.finite_nonempty_inter_compact (isCompact_singleton (x := x))
  have h1 : ({x} : Set X) ⊆ interior (⋃ i ∈ hfin.toFinset, D i) :=
    subset_interior_biUnion_of_forall_inter_nonempty hlf hcover hclosed
      (fun i hi => hfin.mem_toFinset.mpr hi)
  have h2 : (⋃ i ∈ hfin.toFinset, D i) ⊆ (⋃ i ∈ s, D i) := by
    intro y hy
    obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp hy
    refine Set.mem_iUnion₂.mpr ⟨i, hx i ?_, hyi⟩
    obtain ⟨z, hz1, hz2⟩ := hfin.mem_toFinset.mp hi
    rw [Set.mem_singleton_iff] at hz2
    exact hz2 ▸ hz1
  exact interior_mono h2 (h1 (Set.mem_singleton x))

/-- **A tile outside a finite subunion is disjoint from the interior of that subunion.** -/
theorem tile_subset_compl_interior_of_not_mem {ι : Type*} {D : ι → Set X}
    (hdense : ∀ i, closure (interior (D i)) = D i)
    (hdisj : ∀ i j, i ≠ j → interior (D i) ∩ interior (D j) = ∅)
    {s : Finset ι} {j : ι} (hj : j ∉ s) :
    D j ⊆ (interior (⋃ i ∈ s, D i))ᶜ := by
  intro y hy hyint
  have hinter : interior (D j) ∩ (⋃ i ∈ s, D i) = ∅ :=
    interior_inter_biUnion_eq_empty hdisj hdense hj
  have hycl : y ∈ closure (interior (D j)) := by rw [hdense j]; exact hy
  obtain ⟨z, hzU, hzDj⟩ := mem_closure_iff.mp hycl (interior (⋃ i ∈ s, D i)) isOpen_interior hyint
  exact (Set.eq_empty_iff_forall_notMem.mp hinter) z ⟨hzDj, interior_subset hzU⟩

/-! ## Components of the complement of the interior of a filled subunion -/

/-- **Every component of `(int L)ᶜ` has non-compact closure**, where `L` is a finite subunion of a
locally finite disc tiling all of whose complementary components (`Lᶜ`) have non-compact closure. -/
theorem not_isCompact_closure_componentIn_compl_interior {ι : Type*} {D : ι → Set X}
    (hlf : LocallyFinite D) (hcover : ⋃ i, D i = Set.univ) (hclosed : ∀ i, IsClosed (D i))
    (hdense : ∀ i, closure (interior (D i)) = D i)
    (hdisj : ∀ i j, i ≠ j → interior (D i) ∩ interior (D j) = ∅)
    (hintne : ∀ i, (interior (D i)).Nonempty)
    (hpre : ∀ i, IsPreconnected (D i))
    {s : Finset ι}
    (H : ∀ x : X, x ∉ ⋃ i ∈ s, D i →
      ¬ IsCompact (closure (connectedComponentIn ((⋃ i ∈ s, D i)ᶜ) x))) :
    ∀ x : X, x ∉ interior (⋃ i ∈ s, D i) →
      ¬ IsCompact (closure (connectedComponentIn ((interior (⋃ i ∈ s, D i))ᶜ) x)) := by
  classical
  set L : Set X := ⋃ i ∈ s, D i with hLdef
  intro x hx
  set Z : Set X := connectedComponentIn ((interior L)ᶜ) x with hZdef
  have hxZ : x ∈ (interior L)ᶜ := hx
  have hkey : ∃ y ∈ Z, y ∉ L := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨j, hxj, hjs⟩ : ∃ j, x ∈ D j ∧ j ∉ s := by
      by_contra hc
      push_neg at hc
      refine hx ?_
      have hmem := mem_interior_biUnion_of_mem_all_tiles hlf hcover hclosed (s := s) (x := x) hc
      simpa only [← hLdef] using hmem
    have hDjZ : D j ⊆ Z := by
      have hsub : D j ⊆ (interior L)ᶜ := tile_subset_compl_interior_of_not_mem hdense hdisj hjs
      exact (hpre j).subset_connectedComponentIn hxj hsub
    obtain ⟨y, hyint⟩ := hintne j
    have hyZ : y ∈ Z := hDjZ (interior_subset hyint)
    have hyLc : y ∈ Lᶜ := by
      intro hyL
      have hinter : interior (D j) ∩ L = ∅ := by
        rw [hLdef]
        exact interior_inter_biUnion_eq_empty hdisj hdense hjs
      exact (Set.eq_empty_iff_forall_notMem.mp hinter) y ⟨hyint, hyL⟩
    exact hyLc (hcon y hyZ)
  obtain ⟨y, hyZ, hyLc⟩ := hkey
  intro hZc
  have hD'y : connectedComponentIn (Lᶜ) y ⊆ Z := by
    have hle : connectedComponentIn (Lᶜ) y ⊆ connectedComponentIn ((interior L)ᶜ) y :=
      (isPreconnected_connectedComponentIn).subset_connectedComponentIn
        (mem_connectedComponentIn hyLc)
        (fun z hz hzint => (connectedComponentIn_subset (Lᶜ) y hz) (interior_subset hzint))
    rwa [show connectedComponentIn ((interior L)ᶜ) y = Z from by
      rw [hZdef]; exact (connectedComponentIn_eq hyZ).symm] at hle
  exact H y hyLc (hZc.of_isClosed_subset isClosed_closure (closure_mono hD'y))

/-- **The same for a point of `int L` lying in another component of `int L`.** -/
theorem not_isCompact_closure_componentIn_compl_of_mem_interior_component {ι : Type*}
    {D : ι → Set X} [T2Space X] [LocallyConnectedSpace X] [ConnectedSpace X]
    (hlf : LocallyFinite D) (hcover : ⋃ i, D i = Set.univ) (hclosed : ∀ i, IsClosed (D i))
    (hdense : ∀ i, closure (interior (D i)) = D i)
    (hdisj : ∀ i j, i ≠ j → interior (D i) ∩ interior (D j) = ∅)
    (hintne : ∀ i, (interior (D i)).Nonempty)
    (hpre : ∀ i, IsPreconnected (D i))
    {s : Finset ι} (hLc : IsCompact (⋃ i ∈ s, D i)) (hX : ¬ CompactSpace X)
    (H : ∀ x : X, x ∉ ⋃ i ∈ s, D i →
      ¬ IsCompact (closure (connectedComponentIn ((⋃ i ∈ s, D i)ᶜ) x)))
    {x₀ x : X} (hx₀ : x₀ ∈ interior (⋃ i ∈ s, D i)) (hx : x ∈ interior (⋃ i ∈ s, D i))
    (hxnot : x ∉ connectedComponentIn (interior (⋃ i ∈ s, D i)) x₀) :
    ¬ IsCompact (closure (connectedComponentIn ((connectedComponentIn (interior (⋃ i ∈ s, D i)) x₀)ᶜ) x)) := by
  classical
  set L : Set X := ⋃ i ∈ s, D i with hLdef
  set Ω : Set X := connectedComponentIn (interior L) x₀ with hΩdef
  set W : Set X := connectedComponentIn (interior L) x with hWdef
  set Cx : Set X := connectedComponentIn (Ωᶜ) x with hCxdef
  have hzL : interior L ⊆ L := interior_subset
  have hLk : IsCompact L := by rw [hLdef]; exact hLc
  have hLcl : IsClosed L := isClosed_biUnion_of_locallyFinite hlf hclosed s
  have hΩo : IsOpen Ω := isOpen_interior.connectedComponentIn
  have hCxcl : IsClosed Cx :=
    isClosed_connectedComponentIn_of_isClosed (isClosed_compl_iff.mpr hΩo) x
  -- `W` is a component of `int L`, open and different from `Ω`
  have hWo : IsOpen W := isOpen_interior.connectedComponentIn
  have hxW : x ∈ W := mem_connectedComponentIn hx
  have hWneΩ : W ≠ Ω := by
    intro hEq
    exact hxnot (by rw [← hEq, hWdef]; exact hxW)
  have hWsubΩc : W ⊆ Ωᶜ := by
    intro y hyW hyΩ
    exact hWneΩ (by
      rw [hWdef, hΩdef]
      exact eq_of_inter_nonempty_connectedComponentIn hyW hyΩ)
  have hWCx : W ⊆ Cx :=
    (isPreconnected_connectedComponentIn).subset_connectedComponentIn (mem_connectedComponentIn hx)
      hWsubΩc
  -- `W ≠ univ`
  have hWL : W ⊆ L := (connectedComponentIn_subset (interior L) x).trans hzL
  have hWne : W ≠ Set.univ := by
    intro hEq
    have hLuniv : L = Set.univ := Set.eq_univ_of_univ_subset (hEq ▸ hWL)
    exact hX (isCompact_univ_iff.mp (hLuniv ▸ hLk))
  -- hence `∂W ≠ ∅`
  have hfront : (frontier W).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    have hcl : IsClosed W := by
      rw [← closure_subset_iff_isClosed]
      intro y hy
      by_contra hyW
      have hmem : y ∈ frontier W := by rw [hWo.frontier_eq]; exact ⟨hy, hyW⟩
      exact (Set.eq_empty_iff_forall_notMem.mp hcon) y hmem
    exact hWne (IsClopen.eq_univ ⟨hcl, hWo⟩ ⟨x, hxW⟩)
  obtain ⟨x', hx'⟩ := hfront
  have hx'cl : x' ∈ closure W := by
    rw [hWo.frontier_eq] at hx'
    exact hx'.1
  have hx'nW : x' ∉ W := by
    rw [hWo.frontier_eq] at hx'
    exact hx'.2
  have hx'Cx : x' ∈ Cx := by
    rw [← hCxcl.closure_eq]
    exact closure_mono hWCx hx'cl
  have hx'L : x' ∈ L := by
    have hcl : closure W ⊆ L := (closure_mono hWL).trans (by rw [hLcl.closure_eq])
    exact hcl hx'cl
  -- `x' ∉ int L`
  have hcomplWo : IsOpen (interior L \ W) := by
    have hEq : interior L \ W =
        ⋃ y : ↥(interior L \ W), connectedComponentIn (interior L) (y : X) := by
      ext z
      constructor
      · intro hz
        exact Set.mem_iUnion.mpr ⟨⟨z, hz⟩, mem_connectedComponentIn hz.1⟩
      · intro hz
        obtain ⟨y, hy⟩ := Set.mem_iUnion.mp hz
        have hyW : (y : X) ∉ W := y.2.2
        refine ⟨connectedComponentIn_subset (interior L) (y : X) hy, ?_⟩
        intro hzW
        exact hyW (by
          have h1 : connectedComponentIn (interior L) (y : X) = connectedComponentIn (interior L) x :=
            (connectedComponentIn_eq hy).trans
              (connectedComponentIn_eq (show z ∈ connectedComponentIn (interior L) x from hzW)).symm
          change (y : X) ∈ connectedComponentIn (interior L) x
          rw [← h1]
          exact mem_connectedComponentIn y.2.1)
    rw [hEq]
    exact isOpen_iUnion fun y => isOpen_interior.connectedComponentIn
  have hx'int : x' ∉ interior L := by
    intro hx'int
    have hmem : x' ∈ interior L \ W := ⟨hx'int, hx'nW⟩
    obtain ⟨V, hVsub, hVopen, hx'V⟩ := mem_nhds_iff.mp (hcomplWo.mem_nhds hmem)
    obtain ⟨w, hwV, hwW⟩ := mem_closure_iff.mp hx'cl V hVopen hx'V
    exact (hVsub hwV).2 hwW
  -- some tile containing `x'` is outside `s`
  obtain ⟨j, hx'j, hjs⟩ : ∃ j, x' ∈ D j ∧ j ∉ s := by
    by_contra hc
    push_neg at hc
    refine hx'int ?_
    have hmem := mem_interior_biUnion_of_mem_all_tiles hlf hcover hclosed (s := s) (x := x') hc
    simpa only [← hLdef] using hmem
  -- its interior is inside `Cx ∩ Lᶜ`
  have hΩintL : Ω ⊆ interior L := by rw [hΩdef]; exact connectedComponentIn_subset (interior L) x₀
  have hDjCx : D j ⊆ Cx := by
    have hsub : D j ⊆ Ωᶜ := fun y hy => by
      have h1 : y ∈ (interior L)ᶜ := tile_subset_compl_interior_of_not_mem hdense hdisj hjs hy
      exact fun hyΩ => h1 (hΩintL hyΩ)
    have h3 : D j ⊆ connectedComponentIn (Ωᶜ) x' := (hpre j).subset_connectedComponentIn hx'j hsub
    rwa [show connectedComponentIn (Ωᶜ) x' = Cx from (connectedComponentIn_eq hx'Cx).symm] at h3
  obtain ⟨y, hyint⟩ := hintne j
  have hyCx : y ∈ Cx := hDjCx (interior_subset hyint)
  have hyLc : y ∉ L := by
    intro hyL
    have hinter : interior (D j) ∩ L = ∅ := by
      rw [hLdef]
      exact interior_inter_biUnion_eq_empty hdisj hdense hjs
    exact (Set.eq_empty_iff_forall_notMem.mp hinter) y ⟨hyint, hyL⟩
  intro hCxc
  have hD'y : connectedComponentIn (Lᶜ) y ⊆ Cx := by
    have hle : connectedComponentIn (Lᶜ) y ⊆ connectedComponentIn (Ωᶜ) y :=
      (isPreconnected_connectedComponentIn).subset_connectedComponentIn
        (mem_connectedComponentIn hyLc)
        (fun z hz hzΩ => (connectedComponentIn_subset (Lᶜ) y hz) (interior_subset (hΩintL hzΩ)))
    rwa [show connectedComponentIn (Ωᶜ) y = Cx from (connectedComponentIn_eq hyCx).symm] at hle
  exact H y hyLc (hCxc.of_isClosed_subset isClosed_closure (closure_mono hD'y))

/-! ## The engulfing -/

theorem exists_isOpen_isConnected_isCompact_closure_no_bounded_component {X : Type*}
    [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [LocallyCompactSpace X]
    [LocallyConnectedSpace X] [LocallyPathConnectedSpace X] [SecondCountableTopology X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {K : Set X} (hK : IsCompact K) :
    ∃ Ω : Set X, IsOpen Ω ∧ IsConnected Ω ∧ IsCompact (closure Ω) ∧ K ⊆ Ω ∧
      ∀ x ∉ Ω, ¬ IsCompact (closure (connectedComponentIn Ωᶜ x)) := by
  classical
  by_cases hXc : CompactSpace X
  · exact ⟨Set.univ, isOpen_univ, isConnected_univ, by rw [closure_univ]; exact isCompact_univ,
      subset_univ K, fun x hx => absurd (Set.mem_univ x) hx⟩
  · obtain ⟨ι, D, hlf, hcover, hclosed, hdisk, hdisj⟩ :
        ∃ (ι : Type) (D : ι → Set X), LocallyFinite D ∧ (⋃ i, D i) = Set.univ ∧
          (∀ i, IsClosed (D i)) ∧
          (∀ i, Nonempty (Metric.closedBall (0 : ℂ) 1 ≃ₜ (D i : Set X))) ∧
          (∀ i j, i ≠ j → interior (D i) ∩ interior (D j) = ∅) :=
      Commons.Topology.Surface.exists_locallyFinite_disk_tiling (X := X)
    have hdense : ∀ i, closure (interior (D i)) = D i :=
      fun i => closure_interior_eq_of_homeomorph_closedBall (hdisk i)
    have hcmp : ∀ i, IsCompact (D i) := fun i => isCompact_of_homeomorph_closedBall (hdisk i)
    have hintne : ∀ i, (interior (D i)).Nonempty :=
      fun i => interior_nonempty_of_homeomorph_closedBall (hdisk i)
    have hpre : ∀ i, IsPreconnected (D i) :=
      fun i => isPreconnected_of_homeomorph_closedBall' (hdisk i)
    -- a first relatively compact neighbourhood of `K`
    obtain ⟨Ω₀, hΩ₀o, hΩ₀c, hΩ₀k, hKΩ₀⟩ :=
      exists_isOpen_isConnected_isCompact_closure_superset (X := X) hK
    -- the tiles meeting `closure Ω₀`, and the interior of their union
    set s₁ : Finset ι := (hlf.finite_nonempty_inter_compact hΩ₀k).toFinset with hs₁def
    have hΩ₀sub : closure Ω₀ ⊆ interior (⋃ i ∈ s₁, D i) :=
      subset_interior_biUnion_of_forall_inter_nonempty hlf hcover hclosed
        (fun i hi => (hlf.finite_nonempty_inter_compact hΩ₀k).mem_toFinset.mpr hi)
    -- fill the relatively compact complements of that union
    obtain ⟨s, hCs, hH⟩ := exists_finset_tiles_engulfing (X := X) hlf hcover hclosed hdisk hdisj
      (K := ⋃ i ∈ s₁, D i) (Finset.isCompact_biUnion s₁ fun i _ => hcmp i)
    set L : Set X := ⋃ i ∈ s, D i with hLdef
    have hLcl : IsClosed L := isClosed_biUnion_of_locallyFinite hlf hclosed s
    have hLk : IsCompact L := Finset.isCompact_biUnion s fun i _ => hcmp i
    have hs₁s : (⋃ i ∈ s₁, D i) ⊆ L := by rw [hLdef]; exact hCs
    obtain ⟨x₀, hx₀Ω₀⟩ := hΩ₀c.nonempty
    have hΩ₀L : Ω₀ ⊆ interior L := fun y hy => interior_mono hs₁s (hΩ₀sub (subset_closure hy))
    have hx₀ : x₀ ∈ interior L := hΩ₀L hx₀Ω₀
    refine ⟨connectedComponentIn (interior L) x₀, isOpen_interior.connectedComponentIn,
      isConnected_connectedComponentIn_iff.mpr hx₀, ?_, ?_, ?_⟩
    · refine hLk.of_isClosed_subset isClosed_closure ?_
      exact ((closure_mono (connectedComponentIn_subset (interior L) x₀)).trans
        (closure_mono interior_subset)).trans (le_of_eq hLcl.closure_eq)
    · intro x hx
      exact (hΩ₀c.isPreconnected).subset_connectedComponentIn hx₀Ω₀ hΩ₀L (hKΩ₀ hx)
    · intro x hxΩ
      by_cases hxint : x ∈ interior L
      · exact not_isCompact_closure_componentIn_compl_of_mem_interior_component hlf hcover hclosed
          hdense hdisj hintne hpre hLk hXc hH hx₀ hxint hxΩ
      · have h1 := not_isCompact_closure_componentIn_compl_interior hlf hcover hclosed hdense
          hdisj hintne hpre hH x hxint
        intro hc
        refine h1 (hc.of_isClosed_subset isClosed_closure (closure_mono ?_))
        exact (isPreconnected_connectedComponentIn).subset_connectedComponentIn
          (mem_connectedComponentIn hxint)
          (fun z hz hzΩ => (connectedComponentIn_subset ((interior L)ᶜ) x hz)
            (connectedComponentIn_subset (interior L) x₀ hzΩ))

end Work.Topology.Engulf
