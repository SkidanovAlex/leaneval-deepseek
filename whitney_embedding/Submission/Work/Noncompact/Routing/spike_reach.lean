import Mathlib
import Submission.Work.Noncompact.CompressionTube.spike_removal
import Submission.Work.Noncompact.Canals.arc_interior_empty

/-!
# The spike form of the reach

`Work.Noncompact.CompressionTube.spike_removal` says that deleting a *half-open* straight spike
whose base lies outside the region leaves an open preconnected set preconnected.  The line
construction needs the version in which only a *subset* of the spike is deleted: the trace of the
already drawn chain inside a corridor is a piece of the new piece's straight germ, not the whole
germ.

That form follows from the thinness of arcs, exactly as for `isPreconnected_sdiff_of_subset_arcs`:
the image of an arc has empty interior (`Canals.arc_interior_empty`), which gives the thinness
`C ⊆ closure (C \ spike)`, and then `IsPreconnected.subset_closure` upgrades preconnectedness from
`C \ spike` to `C \ A` for any `A ⊆ spike`.

This is the *slit/spike form of the reach*: a straight chart segment whose base is on the boundary
of the corridor and whose free end is inside does not separate the corridor, and deleting any part
of it does not either.
-/

namespace Work.Noncompact.Routing

open Set Topology

variable {M : Type*} [TopologicalSpace M]

/-- **Thinness of a spike.**  A half-open arc with the base outside an open set `C` is nowhere
dense in `C`: `C` is contained in the closure of `C` minus the spike. -/
theorem subset_closure_sdiff_spike {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {C : Set M} (hC : IsOpen C) {σ : ℝ → M} (hσc : Continuous σ)
    (hσinj : Set.InjOn σ (Set.Icc (0:ℝ) 1)) :
    C ⊆ closure (C \ σ '' Set.Ioc (0:ℝ) 1) := by
  have hint : interior (σ '' Set.Icc (0:ℝ) 1) = ∅ :=
    Work.Noncompact.Canals.arc_interior_empty hn hσc hσinj
  have hint' : interior (σ '' Set.Ioc (0:ℝ) 1) = ∅ := by
    rw [← Set.not_nonempty_iff_eq_empty]
    rintro ⟨x, hx⟩
    have : x ∈ interior (σ '' Set.Icc (0:ℝ) 1) :=
      interior_mono (Set.image_mono Set.Ioc_subset_Icc_self) hx
    rw [hint] at this
    exact this
  intro x hx
  rw [mem_closure_iff_nhds]
  intro N hN
  by_contra hcon
  rw [Set.not_nonempty_iff_eq_empty] at hcon
  have hmem : N ∩ C ∈ 𝓝 x := Filter.inter_mem hN (hC.mem_nhds hx)
  have hxint : x ∈ interior (N ∩ C) := mem_interior_iff_mem_nhds.mpr hmem
  have hsub : interior (N ∩ C) ⊆ σ '' Set.Ioc (0:ℝ) 1 := by
    intro y hy
    by_contra hyZ
    have hy' := interior_subset hy
    have : y ∈ N ∩ (C \ σ '' Set.Ioc (0:ℝ) 1) := ⟨hy'.1, hy'.2, hyZ⟩
    rw [hcon] at this
    exact this
  have hle : interior (N ∩ C) ⊆ interior (σ '' Set.Ioc (0:ℝ) 1) :=
    interior_maximal hsub isOpen_interior
  rw [hint'] at hle
  exact absurd (hle hxint) (Set.notMem_empty x)

/-- **The spike form of the reach.**  If `C` is open preconnected in an `n`-manifold (`n ≥ 2`) and
`σ` is an arc whose half-open image `σ '' Ioc 0 1` lies in `C` while its base `σ 0` does not, then
deleting any *subset* `A` of that half-open image from `C` leaves a preconnected set. -/
theorem isPreconnected_sdiff_of_spike_subset {n : ℕ} (hn : 2 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {C : Set M} (hC : IsOpen C) (hCc : IsPreconnected C)
    {σ : ℝ → M} (hσc : Continuous σ) (hσinj : Set.InjOn σ (Set.Icc (0:ℝ) 1))
    (hσC : σ '' Set.Ioc (0:ℝ) 1 ⊆ C) (hσ0 : σ 0 ∉ C)
    {A : Set M} (hA : A ⊆ σ '' Set.Ioc (0:ℝ) 1) :
    IsPreconnected (C \ A) := by
  have hs : IsPreconnected (C \ σ '' Set.Ioc (0:ℝ) 1) :=
    Work.Noncompact.CompressionTube.spike_removal hn hC hCc hσc hσinj hσC hσ0
  have hsub : (C \ σ '' Set.Ioc (0:ℝ) 1) ⊆ C \ A := by
    intro x hx
    exact ⟨hx.1, fun hxA => hx.2 (hA hxA)⟩
  exact hs.subset_closure hsub (sdiff_subset.trans (subset_closure_sdiff_spike hn hC hσc hσinj))

/-- **The reach, spike form.**  Under the hypotheses of `isPreconnected_sdiff_of_spike_subset`, any
two points of `C \ A` lie in the same component: this is the form in which the line construction
consumes the spike reach (the chain's trace inside a corridor is a piece of the new piece's germ,
whose base lies on the boundary of the corridor). -/
theorem reach_of_spike_subset {n : ℕ} (hn : 2 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {C : Set M} (hC : IsOpen C) (hCc : IsPreconnected C)
    {σ : ℝ → M} (hσc : Continuous σ) (hσinj : Set.InjOn σ (Set.Icc (0:ℝ) 1))
    (hσC : σ '' Set.Ioc (0:ℝ) 1 ⊆ C) (hσ0 : σ 0 ∉ C)
    {A : Set M} (hA : A ⊆ σ '' Set.Ioc (0:ℝ) 1)
    {x y : M} (hx : x ∈ C \ A) (hy : y ∈ C \ A) :
    y ∈ connectedComponentIn (C \ A) x :=
  (isPreconnected_sdiff_of_spike_subset hn hC hCc hσc hσinj hσC hσ0 hA)
    |>.subset_connectedComponentIn hx subset_rfl hy

/-- **Thinness of a spike (mirror form).** -/
theorem subset_closure_sdiff_spike' {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {C : Set M} (hC : IsOpen C) {σ : ℝ → M} (hσc : Continuous σ)
    (hσinj : Set.InjOn σ (Set.Icc (0:ℝ) 1)) :
    C ⊆ closure (C \ σ '' Set.Ico (0:ℝ) 1) := by
  have hset : (fun t : ℝ => σ (1 - t)) '' Set.Ioc (0:ℝ) 1 = σ '' Set.Ico (0:ℝ) 1 := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, by simp⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, by simp⟩
  have hinj : Set.InjOn (fun t : ℝ => σ (1 - t)) (Set.Icc (0:ℝ) 1) := by
    intro s hs t ht hst
    have hs' : 1 - s ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have ht' : 1 - t ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have h1 : 1 - s = 1 - t := hσinj hs' ht' hst
    linarith
  have h := subset_closure_sdiff_spike (n := n) hn (C := C) hC
    (σ := fun t : ℝ => σ (1 - t)) (hσc.comp (continuous_const.sub continuous_id)) hinj
  rwa [hset] at h

/-- **The spike form of the reach (mirror form).**  The spike starts at `σ 0` (which may lie in
`C`) and leaves `C` before `σ 1`: deleting any subset of `σ '' Ico 0 1` leaves `C` preconnected.
This is the geometry of the line construction: the chain's trace inside a corridor is the initial
piece of the new piece's straight germ, from the junction outwards. -/
theorem isPreconnected_sdiff_of_spike_subset' {n : ℕ} (hn : 2 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {C : Set M} (hC : IsOpen C) (hCc : IsPreconnected C)
    {σ : ℝ → M} (hσc : Continuous σ) (hσinj : Set.InjOn σ (Set.Icc (0:ℝ) 1))
    (hσC : σ '' Set.Ico (0:ℝ) 1 ⊆ C) (hσ1 : σ 1 ∉ C)
    {A : Set M} (hA : A ⊆ σ '' Set.Ico (0:ℝ) 1) :
    IsPreconnected (C \ A) := by
  have hσc' : Continuous fun t : ℝ => σ (1 - t) :=
    hσc.comp (continuous_const.sub continuous_id)
  have hσinj' : Set.InjOn (fun t : ℝ => σ (1 - t)) (Set.Icc (0:ℝ) 1) := by
    intro s hs t ht hst
    have hs' : 1 - s ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have ht' : 1 - t ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have h1 : 1 - s = 1 - t := hσinj hs' ht' hst
    linarith
  have hσC' : (fun t : ℝ => σ (1 - t)) '' Set.Ioc (0:ℝ) 1 ⊆ C := by
    rintro x ⟨t, ht, rfl⟩
    exact hσC ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, by simp⟩
  have hσ0' : (fun t : ℝ => σ (1 - t)) 0 ∉ C := by
    simpa using hσ1
  have hA' : A ⊆ (fun t : ℝ => σ (1 - t)) '' Set.Ioc (0:ℝ) 1 := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := hA hx
    exact ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, by simp⟩
  exact isPreconnected_sdiff_of_spike_subset hn hC hCc hσc' hσinj' hσC' hσ0' hA'

/-- **The reach, spike form (mirror).** -/
theorem reach_of_spike_subset' {n : ℕ} (hn : 2 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {C : Set M} (hC : IsOpen C) (hCc : IsPreconnected C)
    {σ : ℝ → M} (hσc : Continuous σ) (hσinj : Set.InjOn σ (Set.Icc (0:ℝ) 1))
    (hσC : σ '' Set.Ico (0:ℝ) 1 ⊆ C) (hσ1 : σ 1 ∉ C)
    {A : Set M} (hA : A ⊆ σ '' Set.Ico (0:ℝ) 1)
    {x y : M} (hx : x ∈ C \ A) (hy : y ∈ C \ A) :
    y ∈ connectedComponentIn (C \ A) x :=
  (isPreconnected_sdiff_of_spike_subset' hn hC hCc hσc hσinj hσC hσ1 hA)
    |>.subset_connectedComponentIn hx subset_rfl hy

end Work.Noncompact.Routing
