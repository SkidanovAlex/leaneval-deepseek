import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.exists_ballPiece_of_closedDisc

/-!
# Engulfing a compact set by finitely many tiles of a locally finite disc tiling

Let `D : ι → Set X` be a locally finite closed cover of a connected Riemann surface `X` by sets
homeomorphic to the closed unit disc, with pairwise disjoint interiors.  For every compact `K ⊆ X`
there is a finite `s` of tile indices with

* `K ⊆ ⋃ i ∈ s, D i`, and
* every connected component of the complement of `⋃ i ∈ s, D i` has non-compact closure.

This is the *filling* step of the engulfing argument (ABS, Theorem 12 / Hubbard, Chapter 1): start
from the finitely many tiles meeting `K` and add all the tiles contained in a relatively compact
complementary component.

## Route of the proof

Write `s₀` for the (finite) set of tiles meeting `K`, `C = ⋃ i ∈ s₀, D i` (closed and compact).

*The crux is that the complement of `C` has only finitely many relatively compact components.*  It
is proved here without any tameness hypothesis on the tiles, using only the local finiteness of the
tiling:

* (`closure_componentIn_inter_compl_subset`) a component of the complement of a closed set is closed
  *in* that complement;
* (`tile_subset_closure_componentIn`) a tile meeting a component of `Cᶜ` is contained in the closure
  of that component — for a tile `D j ∉ s₀`, its interior is disjoint from `C` and hence lies in the
  component it meets;
* (`eq_of_tile_subset_closure_componentIn`) consequently a tile lies in the closure of at most one
  component of `Cᶜ`;
* hence the family of closures of complementary components is locally finite: at a point of `C` a
  neighbourhood meets finitely many tiles, and each component whose closure meets that neighbourhood
  contains one of them; away from `C` the component itself is a neighbourhood meeting only its own
  closure;
* (`closure_componentIn_inter_ne_empty`) a relatively compact component of `Cᶜ` meets the compact set
  `C` (otherwise it would be clopen in the connected, non-compact `X`);
* so only finitely many components of `Cᶜ` are relatively compact
  (`finite_relativelyCompact_components`, `finite_closure_components_relativelyCompact`).

Finally (`closure_componentIn_subset_biUnion_tiles`) the closure of a component of `Cᶜ` is covered by
the tiles contained in it, so adding all the tiles lying in the closures of the (finitely many)
relatively compact components — finitely many, since each such closure is compact and the tiling is
locally finite — gives the required finite `s`: the tiles added are disjoint from every
non-relatively-compact component of `Cᶜ`, and those components survive as exactly the components of
the complement of `⋃ i ∈ s, D i`.

The theorem `exists_finset_tiles_engulfing` below is the requested statement; the lemmas above are
independent of it and are meant to be reusable (in particular
`finite_relativelyCompact_components` is the finiteness of the relatively compact complementary
components of a subunion of a locally finite disc tiling).
-/

open Set

namespace Work.Topology.Engulf

variable {X : Type*} [TopologicalSpace X]

/-! ## A single tile -/

/-- A set homeomorphic to the closed unit disc is compact. -/
lemma isCompact_of_homeomorph_closedBall [T2Space X] [ChartedSpace ℂ X] {D : Set X}
    (h : Nonempty (Metric.closedBall (0 : ℂ) 1 ≃ₜ ↥D)) : IsCompact D :=
  h.elim fun e => Work.SimplyConnected.ABS.isCompact_discDisc e

/-- The closure of the interior of a set homeomorphic to the closed unit disc is the set itself. -/
lemma closure_interior_eq_of_homeomorph_closedBall [T2Space X] [ChartedSpace ℂ X] {D : Set X}
    (h : Nonempty (Metric.closedBall (0 : ℂ) 1 ≃ₜ ↥D)) : closure (interior D) = D := by
  obtain ⟨e⟩ := h
  rw [(Work.SimplyConnected.ABS.disc_interior_invariance e).1]
  exact Work.SimplyConnected.ABS.closure_discMap_image_ball e

/-- The interior of a set homeomorphic to the closed unit disc is preconnected. -/
lemma isPreconnected_interior_of_homeomorph_closedBall [T2Space X] [ChartedSpace ℂ X] {D : Set X}
    (h : Nonempty (Metric.closedBall (0 : ℂ) 1 ≃ₜ ↥D)) : IsPreconnected (interior D) := by
  obtain ⟨e⟩ := h
  obtain ⟨φ⟩ := (Work.SimplyConnected.ABS.disc_interior_invariance e).2
  haveI : ConnectedSpace ↥(Metric.ball (0 : ℂ) 1) :=
    isConnected_iff_connectedSpace.mp (Metric.isConnected_ball (by norm_num : (0 : ℝ) < 1))
  haveI : ConnectedSpace ↥(interior D) := φ.connectedSpace_iff.mp inferInstance
  exact (isConnected_iff_connectedSpace.mpr inferInstance).isPreconnected

/-- The interior of a set homeomorphic to the closed unit disc is nonempty. -/
lemma interior_nonempty_of_homeomorph_closedBall [T2Space X] [ChartedSpace ℂ X] {D : Set X}
    (h : Nonempty (Metric.closedBall (0 : ℂ) 1 ≃ₜ ↥D)) : (interior D).Nonempty := by
  obtain ⟨e⟩ := h
  rw [(Work.SimplyConnected.ABS.disc_interior_invariance e).1]
  exact ⟨Work.SimplyConnected.ABS.discMap e 0, 0, Metric.mem_ball_self (by norm_num), rfl⟩

/-! ## Point-set lemmas for a locally finite closed cover with disjoint interiors -/

/-- **Any subunion of a locally finite family of closed sets is closed.** -/
lemma isClosed_biUnion_of_locallyFinite {ι : Type*} {D : ι → Set X} (hlf : LocallyFinite D)
    (hclosed : ∀ i, IsClosed (D i)) (S : Set ι) : IsClosed (⋃ i ∈ S, D i) := by
  have hlf' : LocallyFinite fun i : S => D i.1 := hlf.comp_injective Subtype.val_injective
  have h : IsClosed (⋃ i : S, D i.1) := hlf'.isClosed_iUnion fun i => hclosed i.1
  simpa only [Set.iUnion_subtype] using h

/-- The interior of a tile misses every *other* member of a finite subfamily. -/
lemma interior_inter_biUnion_eq_empty {ι : Type*} {D : ι → Set X}
    (hdisj : ∀ i j, i ≠ j → interior (D i) ∩ interior (D j) = ∅)
    (hdense : ∀ i, closure (interior (D i)) = D i) {s : Finset ι} {j : ι} (hjs : j ∉ s) :
    interior (D j) ∩ (⋃ i ∈ s, D i) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro y ⟨hyint, hyC⟩
  obtain ⟨i, his, hyDi⟩ := Set.mem_iUnion₂.mp hyC
  have hycl : y ∈ closure (interior (D i)) := by rw [hdense i]; exact hyDi
  have hne : (interior (D j) ∩ interior (D i)).Nonempty :=
    mem_closure_iff.mp hycl (interior (D j)) isOpen_interior hyint
  have hij : i = j := by
    by_contra h
    obtain ⟨z, hz1, hz2⟩ := hne
    exact (Set.eq_empty_iff_forall_notMem.mp (hdisj i j h) z ⟨hz2, hz1⟩)
  exact hjs (hij ▸ his)

/-- **A component of the complement of a closed set is closed in the complement**: no limit point of
a component that lies outside the closed set is outside the component. -/
lemma closure_componentIn_inter_compl_subset {C : Set X} (hC : IsClosed C) (x : X) :
    closure (connectedComponentIn Cᶜ x) ∩ Cᶜ ⊆ connectedComponentIn Cᶜ x := by
  intro y hy
  by_cases hx : x ∈ Cᶜ
  · have hpre : IsPreconnected (connectedComponentIn Cᶜ x ∪ {y}) :=
      isPreconnected_connectedComponentIn.subset_closure
        (by intro z hz; exact Or.inl hz)
        (by
          intro z hz
          rcases hz with hz | rfl
          · exact subset_closure hz
          · exact hy.1)
    have hsub : connectedComponentIn Cᶜ x ∪ {y} ⊆ Cᶜ := by
      rintro z (hz | rfl)
      · exact connectedComponentIn_subset Cᶜ x hz
      · exact hy.2
    exact hpre.subset_connectedComponentIn (Or.inl (mem_connectedComponentIn hx)) hsub (Or.inr rfl)
  · have hF : connectedComponentIn Cᶜ x = ∅ := connectedComponentIn_eq_empty hx
    rw [hF, closure_empty] at hy
    exact absurd hy.1 (Set.notMem_empty y)

/-- **A relatively compact component of the complement of a closed set meets the closed set** (in a
connected non-compact space): otherwise it would be clopen. -/
lemma closure_componentIn_inter_ne_empty {C : Set X} [LocallyConnectedSpace X]
    [ConnectedSpace X] (hC : IsClosed C) (hX : ¬ CompactSpace X) {x : X} (hx : x ∈ Cᶜ)
    (hc : IsCompact (closure (connectedComponentIn Cᶜ x))) :
    (closure (connectedComponentIn Cᶜ x) ∩ C).Nonempty := by
  by_contra hcon
  rw [Set.not_nonempty_iff_eq_empty] at hcon
  set F : Set X := connectedComponentIn Cᶜ x with hFdef
  have hc' : IsCompact (closure F) := hc
  have hFcl : IsClosed F := by
    rw [← closure_subset_iff_isClosed]
    intro y hy
    have hyc : y ∈ Cᶜ := by
      by_contra hyC
      exact Set.eq_empty_iff_forall_notMem.mp hcon y ⟨hy, by simpa using hyC⟩
    exact closure_componentIn_inter_compl_subset hC x ⟨hy, hyc⟩
  have hFop : IsOpen F := hC.isOpen_compl.connectedComponentIn
  have huniv : F = Set.univ :=
    IsClopen.eq_univ ⟨hFcl, hFop⟩ ⟨x, mem_connectedComponentIn hx⟩
  rw [huniv, closure_univ] at hc'
  exact hX (isCompact_univ_iff.mp hc')

/-! ## Tiles and components of the complement of a subunion -/

/-- **A tile meeting a component of the complement of a subunion is contained in the closure of that
component.**  (This is `int D_j ⊆ Cᶜ` for a tile not in the subunion, plus density of the
interior.) -/
lemma tile_subset_closure_componentIn {ι : Type*} {D : ι → Set X} [LocallyConnectedSpace X]
    (hlf : LocallyFinite D) (hclosed : ∀ i, IsClosed (D i))
    (hdisj : ∀ i j, i ≠ j → interior (D i) ∩ interior (D j) = ∅)
    (hdense : ∀ i, closure (interior (D i)) = D i)
    (hpre : ∀ i, IsPreconnected (interior (D i)))
    {s : Finset ι} {x : X} (hx : x ∈ (⋃ i ∈ s, D i)ᶜ) {j : ι}
    (hj : (D j ∩ connectedComponentIn ((⋃ i ∈ s, D i)ᶜ) x).Nonempty) :
    D j ⊆ closure (connectedComponentIn ((⋃ i ∈ s, D i)ᶜ) x) := by
  classical
  set C : Set X := ⋃ i ∈ s, D i with hCdef
  set F : Set X := connectedComponentIn Cᶜ x with hFdef
  have hCcl : IsClosed C := isClosed_biUnion_of_locallyFinite hlf hclosed s
  have hFop : IsOpen F := hCcl.isOpen_compl.connectedComponentIn
  have hFsub : F ⊆ Cᶜ := connectedComponentIn_subset Cᶜ x
  have hjs : j ∉ s := by
    rintro hjs
    obtain ⟨y, hyD, hyF⟩ := hj
    exact hFsub hyF (Set.mem_iUnion₂.mpr ⟨j, hjs, hyD⟩)
  have hintC : interior (D j) ∩ C = ∅ := by
    rw [hCdef]
    exact interior_inter_biUnion_eq_empty hdisj hdense hjs
  have hintsub : interior (D j) ⊆ Cᶜ := fun y hy hyC =>
    (Set.eq_empty_iff_forall_notMem.mp hintC y) ⟨hy, hyC⟩
  obtain ⟨y, hyD, hyF⟩ := hj
  have hycl : y ∈ closure (interior (D j)) := by rw [hdense j]; exact hyD
  obtain ⟨z, hzF, hzint⟩ := mem_closure_iff.mp hycl F hFop hyF
  have hzF' : z ∈ F := hzF
  have hsubF : interior (D j) ⊆ F := by
    have h2 : connectedComponentIn Cᶜ z = F := by
      rw [hFdef]
      exact (connectedComponentIn_eq hzF').symm
    rw [← h2]
    exact (hpre j).subset_connectedComponentIn hzint (by
      intro w hw
      exact hintsub hw)
  calc D j = closure (interior (D j)) := (hdense j).symm
    _ ⊆ closure F := closure_mono hsubF

/-- **A tile is contained in the closure of at most one component** of the complement of a
subunion. -/
lemma eq_of_tile_subset_closure_componentIn {ι : Type*} {D : ι → Set X}
    [LocallyConnectedSpace X]
    (hdisj : ∀ i j, i ≠ j → interior (D i) ∩ interior (D j) = ∅)
    (hdense : ∀ i, closure (interior (D i)) = D i)
    (hpre : ∀ i, IsPreconnected (interior (D i))) (hne : ∀ i, (D i).Nonempty)
    {s : Finset ι} {j : ι} {Y Y' : Set X}
    (hY : ∃ x ∈ (⋃ i ∈ s, D i)ᶜ, Y = closure (connectedComponentIn ((⋃ i ∈ s, D i)ᶜ) x))
    (hY' : ∃ x' ∈ (⋃ i ∈ s, D i)ᶜ, Y' = closure (connectedComponentIn ((⋃ i ∈ s, D i)ᶜ) x'))
    (h1 : D j ⊆ Y) (h2 : D j ⊆ Y') : Y = Y' := by
  classical
  set C : Set X := ⋃ i ∈ s, D i with hCdef
  obtain ⟨a, haC, rfl⟩ := hY
  obtain ⟨b, hbC, rfl⟩ := hY'
  have hintne : (interior (D j)).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hDj : D j = ∅ := by rw [← hdense j, h, closure_empty]
    exact (hne j).ne_empty hDj
  obtain ⟨z, hzint⟩ := hintne
  have hzD : z ∈ D j := interior_subset hzint
  obtain ⟨w, hwint, hwZa⟩ := mem_closure_iff.mp (h1 hzD) (interior (D j)) isOpen_interior hzint
  obtain ⟨w', hwint', hwZb⟩ := mem_closure_iff.mp (h2 hzD) (interior (D j)) isOpen_interior hzint
  have hwD : w ∈ D j := interior_subset hwint
  -- the tile is not one of the members of the subunion, so its interior lies in the complement
  have hjs : j ∉ s := by
    rintro hjs
    exact connectedComponentIn_subset Cᶜ a hwZa (Set.mem_iUnion₂.mpr ⟨j, hjs, hwD⟩)
  have hintC : interior (D j) ∩ C = ∅ := by
    rw [hCdef]
    exact interior_inter_biUnion_eq_empty hdisj hdense hjs
  have hintsub : interior (D j) ⊆ Cᶜ := fun y hy hyC =>
    (Set.eq_empty_iff_forall_notMem.mp hintC y) ⟨hy, hyC⟩
  have hZa : interior (D j) ⊆ connectedComponentIn Cᶜ a := by
    have h3 : connectedComponentIn Cᶜ w = connectedComponentIn Cᶜ a :=
      (connectedComponentIn_eq hwZa).symm
    rw [← h3]
    exact (hpre j).subset_connectedComponentIn hwint hintsub
  have hZb : interior (D j) ⊆ connectedComponentIn Cᶜ b := by
    have h3 : connectedComponentIn Cᶜ w' = connectedComponentIn Cᶜ b :=
      (connectedComponentIn_eq hwZb).symm
    rw [← h3]
    exact (hpre j).subset_connectedComponentIn hwint' hintsub
  have hwZb' : w ∈ connectedComponentIn Cᶜ b := hZb hwint
  have hEq : connectedComponentIn Cᶜ a = connectedComponentIn Cᶜ b := by
    rw [connectedComponentIn_eq hwZa, ← connectedComponentIn_eq hwZb']
  rw [hEq]

/-- **The closure of a component of the complement of a subunion is covered by the tiles contained
in it.** -/
lemma closure_componentIn_subset_biUnion_tiles {ι : Type*} {D : ι → Set X}
    [LocallyConnectedSpace X] (hlf : LocallyFinite D) (hclosed : ∀ i, IsClosed (D i))
    (hcover : (⋃ i, D i) = Set.univ)
    (hdisj : ∀ i j, i ≠ j → interior (D i) ∩ interior (D j) = ∅)
    (hdense : ∀ i, closure (interior (D i)) = D i)
    (hpre : ∀ i, IsPreconnected (interior (D i)))
    {s : Finset ι} {x : X} (hx : x ∈ (⋃ i ∈ s, D i)ᶜ) :
    closure (connectedComponentIn ((⋃ i ∈ s, D i)ᶜ) x)
      ⊆ ⋃ j ∈ {j : ι | D j ⊆ closure (connectedComponentIn ((⋃ i ∈ s, D i)ᶜ) x)}, D j := by
  classical
  set C : Set X := ⋃ i ∈ s, D i with hCdef
  set F : Set X := connectedComponentIn Cᶜ x with hFdef
  have hstep : F ⊆ ⋃ j ∈ {j : ι | D j ⊆ closure F}, D j := by
    intro y hyF
    have hycov : y ∈ ⋃ i, D i := by rw [hcover]; trivial
    obtain ⟨j, hyj⟩ := Set.mem_iUnion.mp hycov
    refine Set.mem_iUnion₂.mpr ⟨j, ?_, hyj⟩
    exact tile_subset_closure_componentIn hlf hclosed hdisj hdense hpre hx ⟨y, hyj, hyF⟩
  have hcl : IsClosed (⋃ j ∈ {j : ι | D j ⊆ closure F}, D j) :=
    isClosed_biUnion_of_locallyFinite hlf hclosed _
  exact closure_minimal hstep hcl


/-- Two components of a set that meet are equal. -/
lemma eq_of_inter_nonempty_componentIn {C : Set X} {Z Z' : Set X} {y : X}
    (hZ : ∃ x, Z = connectedComponentIn Cᶜ x) (hZ' : ∃ x', Z' = connectedComponentIn Cᶜ x')
    (hyZ : y ∈ Z) (hyZ' : y ∈ Z') : Z = Z' := by
  obtain ⟨x, rfl⟩ := hZ
  obtain ⟨x', rfl⟩ := hZ'
  rw [connectedComponentIn_eq hyZ, connectedComponentIn_eq hyZ']

/-- Distinct components of the complement of a closed set have disjoint closures. -/
lemma closure_inter_eq_empty_of_ne_componentIn {C : Set X} (hC : IsClosed C) {Z Z' : Set X}
    (hZ : ∃ x, Z = connectedComponentIn Cᶜ x) (hZ' : ∃ x', Z' = connectedComponentIn Cᶜ x')
    (hne : Z ≠ Z') : closure Z ∩ Z' = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro y ⟨hyZ, hyZ'⟩
  obtain ⟨x, rfl⟩ := hZ
  obtain ⟨x', rfl⟩ := hZ'
  have hyCc : y ∈ Cᶜ := connectedComponentIn_subset Cᶜ x' hyZ'
  exact hne (eq_of_inter_nonempty_componentIn ⟨x, rfl⟩ ⟨x', rfl⟩
    (closure_componentIn_inter_compl_subset hC x ⟨hyZ, hyCc⟩) hyZ')

/-- The tiles contained in the closure of one of finitely many compact sets are finitely many. -/
lemma finite_setOf_tile_subset_closure {ι : Type*} {D : ι → Set X} (hlf : LocallyFinite D)
    (hne : ∀ i, (D i).Nonempty) {T : Set (Set X)} (hT : T.Finite)
    (hTk : ∀ Z ∈ T, IsCompact (closure Z)) :
    {j : ι | ∃ Z ∈ T, D j ⊆ closure Z}.Finite := by
  have h1 : (⋃ Z ∈ T, {j : ι | D j ⊆ closure Z}).Finite :=
    Set.Finite.biUnion (t := fun Z : Set X => {j : ι | D j ⊆ closure Z}) hT fun Z hZ => by
      refine (hlf.finite_nonempty_inter_compact (hTk Z hZ)).subset ?_
      rintro j hj
      exact ⟨(hne j).some, (hne j).some_mem, hj ((hne j).some_mem)⟩
  exact h1.subset fun j ⟨Z, hZ, hjZ⟩ => Set.mem_iUnion₂.mpr ⟨Z, hZ, hjZ⟩

/-- **Finiteness of the closures of the relatively compact components** of the complement of a
subunion of a locally finite disc tiling. -/
lemma finite_closure_components_relativelyCompact {ι : Type*} {D : ι → Set X} [T2Space X]
    [ConnectedSpace X] [LocallyConnectedSpace X] (hlf : LocallyFinite D)
    (hclosed : ∀ i, IsClosed (D i)) (hcover : (⋃ i, D i) = Set.univ)
    (hdisj : ∀ i j, i ≠ j → interior (D i) ∩ interior (D j) = ∅)
    (hdense : ∀ i, closure (interior (D i)) = D i)
    (hpre : ∀ i, IsPreconnected (interior (D i))) (hne : ∀ i, (D i).Nonempty)
    (hcmp : ∀ i, IsCompact (D i)) (hX : ¬ CompactSpace X) (s : Finset ι) :
    {Y : Set X | (∃ x ∈ (⋃ i ∈ s, D i)ᶜ, Y = closure (connectedComponentIn ((⋃ i ∈ s, D i)ᶜ) x))
      ∧ IsCompact Y}.Finite := by
  classical
  set C : Set X := ⋃ i ∈ s, D i with hCdef
  have hCcl : IsClosed C := isClosed_biUnion_of_locallyFinite hlf hclosed s
  have hCk : IsCompact C := Finset.isCompact_biUnion s (fun i _ => hcmp i)
  have hlocal : ∀ p : X, ∃ W : Set X, IsOpen W ∧ p ∈ W ∧
      {Y : Set X | ((∃ x ∈ (⋃ i ∈ s, D i)ᶜ,
          Y = closure (connectedComponentIn ((⋃ i ∈ s, D i)ᶜ) x)) ∧ IsCompact Y)
        ∧ (Y ∩ W).Nonempty}.Finite := by
    intro p
    by_cases hp : p ∈ C
    · obtain ⟨W₀, hW₀, hW₀fin⟩ := hlf p
      refine ⟨interior W₀, isOpen_interior, mem_interior_iff_mem_nhds.mpr hW₀, ?_⟩
      have hB : {i : ι | (D i ∩ interior W₀).Nonempty}.Finite :=
        hW₀fin.subset fun i ⟨y, hy1, hy2⟩ => ⟨y, hy1, interior_subset hy2⟩
      have hsub : {Y : Set X | ((∃ x ∈ (⋃ i ∈ s, D i)ᶜ,
            Y = closure (connectedComponentIn ((⋃ i ∈ s, D i)ᶜ) x)) ∧ IsCompact Y)
              ∧ (Y ∩ interior W₀).Nonempty}
          ⊆ ⋃ i ∈ {i : ι | (D i ∩ interior W₀).Nonempty},
              {Y : Set X | ((∃ x ∈ (⋃ i ∈ s, D i)ᶜ,
                Y = closure (connectedComponentIn ((⋃ i ∈ s, D i)ᶜ) x)) ∧ IsCompact Y)
                ∧ D i ⊆ Y} := by
        rintro Y ⟨⟨⟨x, hx, rfl⟩, hYk⟩, hYW⟩
        obtain ⟨y, hyY, hyW⟩ := hYW
        obtain ⟨j, hj, hyj⟩ := Set.mem_iUnion₂.mp
          (closure_componentIn_subset_biUnion_tiles hlf hclosed hcover hdisj hdense hpre hx hyY)
        exact Set.mem_iUnion₂.mpr ⟨j, ⟨y, hyj, hyW⟩, ⟨⟨x, hx, rfl⟩, hYk⟩, hj⟩
      refine Set.Finite.subset (Set.Finite.biUnion (t := fun i : ι => {Y : Set X |
          ((∃ x ∈ (⋃ i ∈ s, D i)ᶜ, Y = closure (connectedComponentIn ((⋃ i ∈ s, D i)ᶜ) x))
            ∧ IsCompact Y) ∧ D i ⊆ Y}) hB (fun i _ => ?_)) hsub
      exact Set.Subsingleton.finite fun Y hY Y' hY' =>
        eq_of_tile_subset_closure_componentIn hdisj hdense hpre hne hY.1.1 hY'.1.1 hY.2 hY'.2
    · refine ⟨connectedComponentIn Cᶜ p, hCcl.isOpen_compl.connectedComponentIn,
        mem_connectedComponentIn hp, ?_⟩
      refine Set.Finite.subset (Set.finite_singleton (closure (connectedComponentIn Cᶜ p))) ?_
      rintro Y ⟨⟨⟨x, hx, rfl⟩, -⟩, hYW⟩
      obtain ⟨y, hyY, hyW⟩ := hYW
      have hyCc : y ∈ Cᶜ := connectedComponentIn_subset Cᶜ p hyW
      have hyZ : y ∈ connectedComponentIn Cᶜ x :=
        closure_componentIn_inter_compl_subset hCcl x ⟨hyY, hyCc⟩
      have hEq : connectedComponentIn Cᶜ x = connectedComponentIn Cᶜ p :=
        eq_of_inter_nonempty_componentIn ⟨x, rfl⟩ ⟨p, rfl⟩ hyZ hyW
      simpa only [Set.mem_singleton_iff] using congrArg closure hEq
  choose W hWopen hWmem hWfin using hlocal
  obtain ⟨t, ht⟩ := hCk.elim_finite_subcover W hWopen fun x _ =>
    Set.mem_iUnion.mpr ⟨x, hWmem x⟩
  refine Set.Finite.subset (Set.Finite.biUnion t.finite_toSet fun p _ => hWfin p) ?_
  rintro Y ⟨⟨x, hx, rfl⟩, hYk⟩
  have hinter : (closure (connectedComponentIn Cᶜ x) ∩ C).Nonempty :=
    closure_componentIn_inter_ne_empty hCcl hX hx hYk
  obtain ⟨y, hyY, hyC⟩ := hinter
  obtain ⟨p, hpt, hyp⟩ := Set.mem_iUnion₂.mp (ht hyC)
  exact Set.mem_iUnion₂.mpr ⟨p, hpt, ⟨⟨x, hx, rfl⟩, hYk⟩, ⟨y, hyY, hyp⟩⟩

/-- **Finiteness of the relatively compact components** of the complement of a subunion of a
locally finite disc tiling, in the form of components (not their closures). -/
lemma finite_relativelyCompact_components {ι : Type*} {D : ι → Set X} [T2Space X]
    [ConnectedSpace X] [LocallyConnectedSpace X] (hlf : LocallyFinite D)
    (hclosed : ∀ i, IsClosed (D i)) (hcover : (⋃ i, D i) = Set.univ)
    (hdisj : ∀ i j, i ≠ j → interior (D i) ∩ interior (D j) = ∅)
    (hdense : ∀ i, closure (interior (D i)) = D i)
    (hpre : ∀ i, IsPreconnected (interior (D i))) (hne : ∀ i, (D i).Nonempty)
    (hcmp : ∀ i, IsCompact (D i)) (hX : ¬ CompactSpace X) (s : Finset ι) :
    {Z : Set X | (∃ x : X, Z = connectedComponentIn ((⋃ i ∈ s, D i)ᶜ) x)
      ∧ IsCompact (closure Z)}.Finite := by
  classical
  set C : Set X := ⋃ i ∈ s, D i with hCdef
  have hR :=
    finite_closure_components_relativelyCompact hlf hclosed hcover hdisj hdense hpre hne hcmp hX s
  have hR' : ({Y : Set X | (∃ x, Y = closure (connectedComponentIn Cᶜ x))
      ∧ IsCompact Y} : Set (Set X)).Finite := by
    refine Set.Finite.subset (hR.union (Set.finite_singleton (∅ : Set X))) ?_
    rintro Y ⟨⟨x, rfl⟩, hYk⟩
    by_cases hx : x ∈ Cᶜ
    · exact Or.inl ⟨⟨x, hx, rfl⟩, hYk⟩
    · exact Or.inr (by rw [connectedComponentIn_eq_empty hx, closure_empty]; rfl)
  refine Set.Finite.of_finite_image (f := fun Z : Set X => closure Z) ?_ ?_
  · refine Set.Finite.subset hR' ?_
    rintro Y ⟨Z, ⟨⟨x, rfl⟩, hZk⟩, rfl⟩
    exact ⟨⟨x, rfl⟩, hZk⟩
  · rintro Z ⟨⟨x, rfl⟩, -⟩ Z' ⟨⟨x', rfl⟩, -⟩ hEq
    have hEq' : closure (connectedComponentIn ((⋃ i ∈ s, D i)ᶜ) x)
        = closure (connectedComponentIn ((⋃ i ∈ s, D i)ᶜ) x') := hEq
    have hCcl : IsClosed (⋃ i ∈ s, D i) := isClosed_biUnion_of_locallyFinite hlf hclosed s
    by_cases hx : x ∈ (⋃ i ∈ s, D i)ᶜ
    · have hx' : x' ∈ (⋃ i ∈ s, D i)ᶜ := by
        by_contra hx''
        rw [connectedComponentIn_eq_empty hx'', closure_empty] at hEq'
        exact (Set.not_nonempty_iff_eq_empty.mpr hEq') ⟨x, subset_closure (mem_connectedComponentIn hx)⟩
      have hmem : x ∈ closure (connectedComponentIn ((⋃ i ∈ s, D i)ᶜ) x) :=
        subset_closure (mem_connectedComponentIn hx)
      rw [hEq'] at hmem
      have hmem' : x ∈ connectedComponentIn ((⋃ i ∈ s, D i)ᶜ) x' :=
        closure_componentIn_inter_compl_subset hCcl x' ⟨hmem, hx⟩
      exact eq_of_inter_nonempty_componentIn ⟨x, rfl⟩ ⟨x', rfl⟩ (mem_connectedComponentIn hx) hmem'
    · have hx'empty : connectedComponentIn ((⋃ i ∈ s, D i)ᶜ) x' = ∅ := by
        rw [connectedComponentIn_eq_empty hx, closure_empty] at hEq'
        rw [Set.eq_empty_iff_forall_notMem]
        intro y hy
        exact Set.notMem_empty y (hEq' ▸ subset_closure hy)
      rw [connectedComponentIn_eq_empty hx, hx'empty]

theorem exists_finset_tiles_engulfing {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [LocallyConnectedSpace X] [SecondCountableTopology X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {ι : Type*} {D : ι → Set X} (hlf : LocallyFinite D) (hcover : ⋃ i, D i = Set.univ)
    (hclosed : ∀ i, IsClosed (D i))
    (hdisk : ∀ i, Nonempty (Metric.closedBall (0:ℂ) 1 ≃ₜ (D i : Set X)))
    (hdisj : ∀ i j, i ≠ j → interior (D i) ∩ interior (D j) = ∅)
    {K : Set X} (hK : IsCompact K) :
    ∃ s : Finset ι, K ⊆ ⋃ i ∈ s, D i ∧
      ∀ x : X, x ∉ ⋃ i ∈ s, D i →
        ¬ IsCompact (closure (connectedComponentIn (⋃ i ∈ s, D i)ᶜ x)) := by
  classical
  have hcmp : ∀ i, IsCompact (D i) := fun i => isCompact_of_homeomorph_closedBall (hdisk i)
  have hdense : ∀ i, closure (interior (D i)) = D i :=
    fun i => closure_interior_eq_of_homeomorph_closedBall (hdisk i)
  have hpre : ∀ i, IsPreconnected (interior (D i)) :=
    fun i => isPreconnected_interior_of_homeomorph_closedBall (hdisk i)
  have hne : ∀ i, (D i).Nonempty := fun i => by
    obtain ⟨e⟩ := hdisk i
    exact ⟨e ⟨0, by simp [Metric.mem_closedBall]⟩, (e ⟨0, by simp [Metric.mem_closedBall]⟩).2⟩
  -- a finite subfamily covering `K`
  obtain ⟨s₀, hs₀⟩ : ∃ s : Finset ι, K ⊆ ⋃ i ∈ s, D i := by
    refine ⟨(hlf.finite_nonempty_inter_compact hK).toFinset, ?_⟩
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (by rw [hcover]; trivial : x ∈ ⋃ i, D i)
    exact Set.mem_iUnion₂.mpr ⟨i, (Set.Finite.mem_toFinset _).mpr ⟨x, hi, hx⟩, hi⟩
  by_cases hXc : CompactSpace X
  · -- if `X` is compact, the (finitely many) tiles themselves cover `X`
    have hAll : {i : ι | (D i).Nonempty}.Finite := by
      simpa using hlf.finite_nonempty_inter_compact (isCompact_univ)
    have hU : ⋃ i ∈ hAll.toFinset, D i = Set.univ := by
      rw [Set.eq_univ_iff_forall]
      intro x
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (by rw [hcover]; trivial : x ∈ ⋃ i, D i)
      exact Set.mem_iUnion₂.mpr ⟨i, (Set.Finite.mem_toFinset hAll).mpr ⟨x, hi⟩, hi⟩
    exact ⟨hAll.toFinset, by rw [hU]; exact subset_univ K, fun x hx => by
      rw [hU] at hx
      exact absurd (Set.mem_univ x) hx⟩
  · -- the non-compact case: fill in the relatively compact complementary components
    set C : Set X := ⋃ i ∈ s₀, D i with hCdef
    have hCcl : IsClosed C := isClosed_biUnion_of_locallyFinite hlf hclosed s₀
    have hCsub : C ⊆ ⋃ i ∈ s₀, D i := le_of_eq hCdef
    have hT : {Z : Set X | (∃ x : X, Z = connectedComponentIn Cᶜ x)
        ∧ IsCompact (closure Z)}.Finite :=
      finite_relativelyCompact_components hlf hclosed hcover hdisj hdense hpre hne hcmp hXc s₀
    have hS : {j : ι | ∃ Z ∈ {Z : Set X | (∃ x : X, Z = connectedComponentIn Cᶜ x)
        ∧ IsCompact (closure Z)}, D j ⊆ closure Z}.Finite :=
      finite_setOf_tile_subset_closure hlf hne hT fun Z hZ => hZ.2
    refine ⟨s₀ ∪ hS.toFinset, ?_, ?_⟩
    · exact hs₀.trans fun x hx => by
        obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
        exact Set.mem_iUnion₂.mpr ⟨i, Finset.mem_union_left _ hi, hxi⟩
    · intro x hx
      have hCsub' : C ⊆ ⋃ i ∈ (s₀ ∪ hS.toFinset), D i := by
        intro y hy
        obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp (hCsub hy)
        exact Set.mem_iUnion₂.mpr ⟨i, Finset.mem_union_left _ hi, hyi⟩
      have hxC : x ∉ C := fun hxC => hx (hCsub' hxC)
      set F : Set X := connectedComponentIn Cᶜ x with hFdef
      set P : Set X := connectedComponentIn ((⋃ i ∈ (s₀ ∪ hS.toFinset), D i)ᶜ) x with hPdef
      have hPC : P ⊆ F := connectedComponentIn_mono x fun y hy hyC => hy (hCsub' hyC)
      intro hcomp
      have hFnc : ¬ IsCompact (closure F) := by
        intro hFk
        have hFin : F ∈ {Z : Set X | (∃ x : X, Z = connectedComponentIn Cᶜ x)
            ∧ IsCompact (closure Z)} := ⟨⟨x, hFdef⟩, hFk⟩
        have hsub : F ⊆ ⋃ j ∈ hS.toFinset, D j := by
          intro y hyF
          have hycl : y ∈ closure F := subset_closure hyF
          obtain ⟨j, hj, hyj⟩ := Set.mem_iUnion₂.mp
            (closure_componentIn_subset_biUnion_tiles hlf hclosed hcover hdisj hdense hpre hxC
              (by rwa [hFdef] at hycl))
          exact Set.mem_iUnion₂.mpr ⟨j, (Set.Finite.mem_toFinset hS).mpr ⟨F, hFin, hj⟩, hyj⟩
        have hxP : x ∈ P := mem_connectedComponentIn hx
        obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp (hsub (hPC hxP))
        exact hx (Set.mem_iUnion₂.mpr ⟨j, Finset.mem_union_right _ hj, hxj⟩)
      have hFPsub : F ⊆ (⋃ i ∈ (s₀ ∪ hS.toFinset), D i)ᶜ := by
        intro y hyF hyU
        rcases Set.mem_iUnion₂.mp hyU with ⟨i, hi, hyi⟩
        rcases Finset.mem_union.mp hi with hi0 | hiS
        · exact (connectedComponentIn_subset Cᶜ x (by rwa [hFdef] at hyF))
            (Set.mem_iUnion₂.mpr ⟨i, hi0, hyi⟩ : y ∈ C)
        · obtain ⟨Z, hZT, hZj⟩ := (Set.Finite.mem_toFinset hS).mp hiS
          have hZF : Z ≠ F := fun hEq => hFnc (hEq ▸ hZT.2)
          have hdisj0 : closure Z ∩ F = ∅ :=
            closure_inter_eq_empty_of_ne_componentIn hCcl hZT.1 ⟨x, hFdef⟩ hZF
          exact (Set.eq_empty_iff_forall_notMem.mp hdisj0 y) ⟨hZj hyi, hyF⟩
      have hFP : F ⊆ P := by
        have hpreF : IsPreconnected F := isPreconnected_connectedComponentIn
        exact hpreF.subset_connectedComponentIn (mem_connectedComponentIn hxC) hFPsub
      rw [show P = F from le_antisymm hPC hFP] at hcomp
      exact hFnc hcomp

end Work.Topology.Engulf
