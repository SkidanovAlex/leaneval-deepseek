import Mathlib

/-!
# Building blocks of the ABS engulfing (the filling construction)

(Anghel--Bruin--Stan, *Uniformization of Riemann surfaces revisited*, Theorem 12.)

The ABS engulfing of a compact set `K` in a connected non-compact surface proceeds by taking a
proper smooth function `g`, a **regular value** `a`, filling the relatively compact components of
`X \ {g ≤ a}` and retracting.  This file contains the parts of that construction that are
*independent of the taming problem* and that are proved with elementary topology only:

* `exists_isCompact_isConnected_mem_nhds` — in a locally compact, locally connected space every
  point has a compact connected neighbourhood;
* `isPreconnected_union_of_inter_closure_nonempty` — a preconnected set meeting the closure of
  another has preconnected union;
* `biUnion_insert_eq`, `isPreconnected_biUnion_finset` — a finite family of preconnected sets with a
  common point has preconnected union;
* `exists_isCompact_isConnected_superset` — **every compact set of a connected, locally compact,
  locally connected, locally path connected space is contained in a *compact connected* set**
  (together with any prescribed point);
* `eq_of_mem_closure_connectedComponentIn` — a connected component of a closed set is closed in the
  ambient space.

## The obstruction to the naive filling (recorded here for the next session)

The obvious filling of a compact set `C` — replacing `int C` by
`int C ∪ {y | the component of y in (int C)ᶜ is relatively compact}` — is **not open** when a
component of `(int C)ᶜ` is a wild continuum: its points need not be interior points of the filled
set.  Concretely, the lemma `eq_of_mem_closure_connectedComponentIn` proves only that a component
cannot be approached *through a sequence in a single other component*; the stronger statement
`closure (F \ C) ∩ C = ∅` is **false** (Cantor set).  In ABS the difficulty disappears because the
pieces are smooth manifolds with boundary obtained at a *regular value* of a proper smooth function
(Sard); formalising this requires Sard for smooth maps, which Mathlib does not have.  See
`NOTES_engulfs_isCompact_analysis.md` in this directory for the full analysis and for the routes
that were checked and rejected.
-/

open Set Filter
open scoped Topology

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.SimplyConnected.ABS

variable {X : Type*} [TopologicalSpace X]

/-- **In a locally compact, locally connected space every point has a compact connected
neighbourhood.**  Take a compact `C` with `x ∈ interior C` and the closure of the connected
component of `x` in `interior C`: it is a neighbourhood of `x` (local connectedness), connected,
and contained in `C`. -/
lemma exists_isCompact_isConnected_mem_nhds [T2Space X] [LocallyCompactSpace X]
    [LocallyConnectedSpace X] (x : X) :
    ∃ Q : Set X, IsCompact Q ∧ IsConnected Q ∧ Q ∈ 𝓝 x := by
  obtain ⟨C, hC, hsub⟩ := exists_compact_superset (isCompact_singleton (x := x))
  have hxC : x ∈ interior C := hsub (mem_singleton x)
  refine ⟨closure (connectedComponentIn (interior C) x), ?_, ?_, ?_⟩
  · refine hC.of_isClosed_subset isClosed_closure ?_
    calc closure (connectedComponentIn (interior C) x) ⊆ closure (interior C) :=
          closure_mono (connectedComponentIn_subset _ _)
      _ ⊆ C := (IsClosed.closure_subset_iff hC.isClosed).mpr interior_subset
  · exact ⟨⟨x, subset_closure (mem_connectedComponentIn hxC)⟩,
      isPreconnected_connectedComponentIn.closure⟩
  · refine mem_of_superset (connectedComponentIn_mem_nhds (isOpen_interior.mem_nhds hxC)) ?_
    exact subset_closure


/-- **A preconnected set meeting the closure of another: the union is preconnected.**
If `S` and `T` are preconnected and `S ∩ closure T ≠ ∅`, then `S ∪ T` is preconnected. -/
lemma isPreconnected_union_of_inter_closure_nonempty {S T : Set X} (hS : IsPreconnected S)
    (hT : IsPreconnected T) (h : (S ∩ closure T).Nonempty) : IsPreconnected (S ∪ T) := by
  rw [isPreconnected_iff_subset_of_disjoint_closed] at hS hT ⊢
  intro u v hu hv huv huv'
  have hSuv : S ⊆ u ∪ v := subset_union_left.trans huv
  have hTuv : T ⊆ u ∪ v := subset_union_right.trans huv
  have hS' : S ∩ (u ∩ v) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    exact (show x ∉ (S ∪ T) ∩ (u ∩ v) from by rw [huv']; exact notMem_empty x)
      ⟨Or.inl hx.1, hx.2⟩
  have hT' : T ∩ (u ∩ v) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    exact (show x ∉ (S ∪ T) ∩ (u ∩ v) from by rw [huv']; exact notMem_empty x)
      ⟨Or.inr hx.1, hx.2⟩
  rcases hS u v hu hv hSuv hS' with hSu | hSv <;> rcases hT u v hu hv hTuv hT' with hTu | hTv
  · exact Or.inl (union_subset hSu hTu)
  · obtain ⟨y, hyS, hyT⟩ := h
    exact absurd (show y ∈ (S ∪ T) ∩ (u ∩ v) from
      ⟨Or.inl hyS, hSu hyS, (hv.closure_subset_iff).mpr hTv hyT⟩)
      (by rw [huv']; exact notMem_empty y)
  · obtain ⟨y, hyS, hyT⟩ := h
    exact absurd (show y ∈ (S ∪ T) ∩ (u ∩ v) from
      ⟨Or.inl hyS, (hu.closure_subset_iff).mpr hTu hyT, hSv hyS⟩)
      (by rw [huv']; exact notMem_empty y)
  · exact Or.inr (union_subset hSv hTv)

/-- Splitting off the inserted index in a `Finset`-indexed union of sets. -/
lemma biUnion_insert_eq {ι : Type*} [DecidableEq ι] (t : Finset ι) (P : ι → Set X) (a : ι) :
    (⋃ i ∈ insert a t, P i) = P a ∪ ⋃ i ∈ t, P i := by
  ext x
  simp only [mem_iUnion, Finset.mem_insert, mem_union]
  constructor
  · rintro ⟨i, rfl | hi, hx⟩
    · exact Or.inl hx
    · exact Or.inr ⟨i, hi, hx⟩
  · rintro (hx | ⟨i, hi, hx⟩)
    · exact ⟨a, Or.inl rfl, hx⟩
    · exact ⟨i, Or.inr hi, hx⟩

/-- **The union of a finite family of preconnected sets with a common point is preconnected.** -/
lemma isPreconnected_biUnion_finset {ι : Type*} [DecidableEq ι] (t : Finset ι) (P : ι → Set X)
    (p : X) (hp : ∀ i ∈ t, p ∈ P i) (hP : ∀ i ∈ t, IsPreconnected (P i)) :
    IsPreconnected (⋃ i ∈ t, P i) := by
  classical
  induction t using Finset.induction with
  | empty =>
      simp only [Finset.notMem_empty, iUnion_false, iUnion_empty]
      exact isPreconnected_empty (α := X)
  | insert a s ha ih =>
      rw [biUnion_insert_eq]
      rcases s.eq_empty_or_nonempty with rfl | hs
      · simp only [Finset.notMem_empty, iUnion_false, iUnion_empty, union_empty]
        exact hP a (Finset.mem_insert_self a ∅)
      · obtain ⟨b, hb⟩ := hs
        have hp' : p ∈ ⋃ i ∈ s, P i :=
          mem_biUnion hb (hp b (Finset.mem_insert_of_mem hb))
        exact IsPreconnected.union p (hp a (Finset.mem_insert_self a s)) hp'
          (hP a (Finset.mem_insert_self a s))
          (ih (fun i hi => hp i (Finset.mem_insert_of_mem hi))
              (fun i hi => hP i (Finset.mem_insert_of_mem hi)))

/-- **Every compact set is contained in a compact connected set (together with a prescribed
point).**  Cover `K ∪ {x₀}` by finitely many compact connected neighbourhoods `Q y` and join a point
of each of them to `x₀` by a path; the union of the `Q y` with these paths is compact, connected and
contains `K ∪ {x₀}`. -/
lemma exists_isCompact_isConnected_superset [T2Space X] [ConnectedSpace X] [LocallyCompactSpace X]
    [LocallyConnectedSpace X] [LocallyPathConnectedSpace X]
    {K : Set X} (hK : IsCompact K) (x₀ : X) :
    ∃ L : Set X, IsCompact L ∧ IsConnected L ∧ K ∪ {x₀} ⊆ L := by
  classical
  haveI : PathConnectedSpace X := PathConnectedSpace.of_locallyPathConnectedSpace
  -- compact connected neighbourhoods, chosen with an interior point
  have hnhds : ∀ y : X, ∃ Q : Set X, IsCompact Q ∧ IsConnected Q ∧ y ∈ interior Q := by
    intro y
    obtain ⟨Q, hQc, hQconn, hQn⟩ := exists_isCompact_isConnected_mem_nhds y
    exact ⟨Q, hQc, hQconn, mem_interior_iff_mem_nhds.mpr hQn⟩
  choose Q hQc hQconn hQint using hnhds
  -- finitely many of them cover `K ∪ {x₀}`
  obtain ⟨t, ht⟩ := (hK.union isCompact_singleton).elim_finite_subcover
    (fun y : X => interior (Q y)) (fun y => isOpen_interior) (by
      intro y hy
      exact mem_iUnion.mpr ⟨y, hQint y⟩)
  -- a point of each `Q y` and a path from it to `x₀`
  have hne : ∀ y : X, (Q y).Nonempty := fun y => (hQconn y).nonempty
  choose q hq using hne
  let γ : (y : X) → Path (q y) x₀ := fun y => Classical.choice (PathConnectedSpace.joined (q y) x₀)
  -- the pieces: each `Q y` with the path to `x₀`
  set P : X → Set X := fun y => Q y ∪ range (γ y) with hPdef
  have hPconn : ∀ y : X, IsConnected (P y) := by
    intro y
    exact (hQconn y).union ⟨q y, hq y, ⟨0, (γ y).source⟩⟩ (isConnected_range (γ y).continuous)
  have hx₀P : ∀ y : X, x₀ ∈ P y := fun y => Or.inr ⟨1, (γ y).target⟩
  have htne : t.Nonempty := by
    obtain ⟨y, hy⟩ := mem_iUnion.mp (ht (Or.inr (mem_singleton x₀)))
    obtain ⟨hyt, -⟩ := mem_iUnion.mp hy
    exact ⟨y, hyt⟩
  refine ⟨⋃ y ∈ t, P y, ?_, ?_, ?_⟩
  · refine Finset.isCompact_biUnion t fun y _ => ?_
    exact (hQc y).union (isCompact_range (γ y).continuous)
  · exact ⟨⟨x₀, mem_biUnion htne.choose_spec (hx₀P _)⟩,
      isPreconnected_biUnion_finset t P x₀ (fun y _ => hx₀P y)
        (fun y _ => (hPconn y).isPreconnected)⟩
  · intro z hz
    rcases hz with hzK | hz0
    · obtain ⟨y, hy⟩ := mem_iUnion.mp (ht (Or.inl hzK))
      obtain ⟨hyt, hzy⟩ := mem_iUnion.mp hy
      exact mem_biUnion hyt (Or.inl (interior_subset hzy))
    · rw [mem_singleton_iff] at hz0
      rw [hz0]
      exact mem_biUnion htne.choose_spec (hx₀P _)

/-- **The components of a closed set do not accumulate at one another.**  If `C` is the connected
component in `F` of a point `y ∈ F` and `x ∈ F` lies in the closure of `C`, then `x ∈ C`. -/
lemma eq_of_mem_closure_connectedComponentIn {F : Set X} {x y : X}
    (hx : x ∈ F) (h : x ∈ closure (connectedComponentIn F y)) :
    x ∈ connectedComponentIn F y := by
  by_cases hy : y ∈ F
  · have hC : connectedComponentIn F y ⊆ F := connectedComponentIn_subset F y
    have hpre : IsPreconnected ({x} ∪ connectedComponentIn F y) :=
      isPreconnected_union_of_inter_closure_nonempty isPreconnected_singleton
        isPreconnected_connectedComponentIn ⟨x, mem_singleton x, h⟩
    have hsub : ({x} ∪ connectedComponentIn F y) ⊆ connectedComponentIn F y :=
      IsPreconnected.subset_connectedComponentIn (F := F) (x := y) hpre
        (Or.inr (mem_connectedComponentIn hy))
        (union_subset (by rintro z rfl; exact hx) hC)
    exact hsub (Or.inl (mem_singleton x))
  · rw [connectedComponentIn_eq_empty hy, closure_empty] at h
    exact absurd h (notMem_empty x)
