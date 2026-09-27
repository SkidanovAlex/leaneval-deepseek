import Mathlib
import Submission.Work.Whitney.PathTools.isPathConnected_compl_finite
import Submission.Work.Whitney.PathTools.isPreconnected_sdiff_of_local_room

/-!
# Removing finitely many points from an open path connected set in a charted space

Main result: `Work.Whitney.PathTools.isPathConnected_sdiff_finite_of_isOpen`.  If `O` is an open
path connected subset of a Hausdorff space locally modelled on `ℝ^n` (`n ≥ 2`), and `F ⊆ O` is
finite, then `O \ F` is again path connected.

The proof has two inputs.

* `room_at_point_manifold`: near every point `p` there are arbitrarily small open neighbourhoods
  `O'` such that `O' \ {p}` is path connected.  Such an `O'` is the inverse chart image of a small
  ball; in dimension `n ≥ 2` a punctured ball is path connected
  (`Work.Whitney.PathTools.isPreconnected_ball_diff_singleton` upgraded by local path
  connectedness).

* the connectedness principle `Work.Whitney.PathTools.isPreconnected_sdiff_of_local_room`, which
  upgrades this pointwise room to preconnectedness of `O \ F`.

Finally `O \ F` is open (a finite set is closed), and an open subset of the locally path connected
space `M` is connected iff it is path connected; nonemptiness follows from `O` being infinite (a
nonempty open subset of a space locally modelled on `ℝ^n` with `n ≥ 2` is infinite).
-/

set_option linter.style.haveILetI false

open Set Metric Filter
open scoped Topology

namespace Work.Whitney.PathTools

/-- **Room at a point.**  For every neighbourhood `N` of a point `p` of a charted space of
dimension `n ≥ 2` there is an open neighbourhood `O ⊆ N` of `p` such that `O \ {p}` is path
connected. -/
theorem room_at_point_manifold {n : ℕ} (hn : 2 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {p : M} {N : Set M} (hN : N ∈ 𝓝 p) :
    ∃ O : Set M, IsOpen O ∧ p ∈ O ∧ O ⊆ N ∧ IsPathConnected (O \ {p}) := by
  haveI : LocallyPathConnectedSpace M := locallyPathConnectedSpace_chartedSpace (n := n)
  obtain ⟨N₀, hN₀N, hN₀open, hpN₀⟩ := mem_nhds_iff.mp hN
  let E := EuclideanSpace ℝ (Fin n)
  let c : OpenPartialHomeomorph M E := chartAt E p
  have hpc : p ∈ c.source := mem_chart_source E p
  have hmem : c '' (N₀ ∩ c.source) ∈ 𝓝 (c p) :=
    c.image_mem_nhds hpc (Filter.inter_mem (hN₀open.mem_nhds hpN₀) (c.open_source.mem_nhds hpc))
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem hmem (c.open_target.mem_nhds (c.map_source hpc)))
  have hball_t : Metric.ball (c p) ε ⊆ c.target := fun z hz => (hεsub hz).2
  refine ⟨c.symm '' Metric.ball (c p) ε, ?_, ?_, ?_, ?_⟩
  · exact c.isOpen_image_symm_of_subset_target Metric.isOpen_ball hball_t
  · exact ⟨c p, Metric.mem_ball_self hε, c.left_inv hpc⟩
  · rintro y ⟨z, hz, rfl⟩
    obtain ⟨w, hw, hwz⟩ := (hεsub hz).1
    rw [← hwz, c.left_inv hw.2]
    exact hN₀N hw.1
  · have heq : c.symm '' (Metric.ball (c p) ε \ {c p})
        = c.symm '' Metric.ball (c p) ε \ {p} := by
      ext y
      constructor
      · rintro ⟨z, ⟨hz, hzcp⟩, rfl⟩
        refine ⟨⟨z, hz, rfl⟩, ?_⟩
        intro h
        exact hzcp (by
          have hz' : z ∈ c.target := hball_t hz
          have h1 : c (c.symm z) = c p := by rw [h]
          rwa [c.right_inv hz'] at h1)
      · rintro ⟨⟨z, hz, rfl⟩, hyp⟩
        refine ⟨z, ⟨hz, ?_⟩, rfl⟩
        intro hzcp
        have hzcp' : z = c p := by simpa using hzcp
        exact hyp (by simp [hzcp', c.left_inv hpc])
    rw [← heq]
    have hrank : 1 < Module.rank ℝ E := one_lt_rank_euclidean hn
    have hnt : Nontrivial E :=
      (rank_pos_iff_nontrivial (R := ℝ)).1 (zero_lt_one.trans hrank)
    have hpre : IsPreconnected (Metric.ball (c p) ε \ {c p}) :=
      isPreconnected_ball_diff_singleton hrank (c p)
    have hne : (Metric.ball (c p) ε \ {c p}).Nonempty :=
      ((infinite_ball_of_nontrivial hnt (c p) hε).sdiff (Set.finite_singleton (c p))).nonempty
    have hpc' : IsPathConnected (Metric.ball (c p) ε \ {c p}) :=
      ((Metric.isOpen_ball (x := c p) (ε := ε)).sdiff isClosed_singleton)
        |>.isConnected_iff_isPathConnected.mp ⟨hne, hpre⟩
    exact hpc'.image' (c.continuousOn_symm.mono (fun z hz => hball_t hz.1))

/-- **A nonempty open subset of a charted space of dimension `n ≥ 2` is infinite.**  A chart ball
around any of its points maps homeomorphically onto an infinite subset. -/
theorem infinite_of_isOpen_nonempty {n : ℕ} (hn : 2 ≤ n) {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {O : Set M} (hO : IsOpen O) (hne : O.Nonempty) : O.Infinite := by
  obtain ⟨p, hp⟩ := hne
  let E := EuclideanSpace ℝ (Fin n)
  let c : OpenPartialHomeomorph M E := chartAt E p
  have hpc : p ∈ c.source := mem_chart_source E p
  have hmem : c '' (O ∩ c.source) ∈ 𝓝 (c p) :=
    c.image_mem_nhds hpc (Filter.inter_mem (hO.mem_nhds hp) (c.open_source.mem_nhds hpc))
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem hmem (c.open_target.mem_nhds (c.map_source hpc)))
  have hball_t : Metric.ball (c p) ε ⊆ c.target := fun z hz => (hεsub hz).2
  have hinj : Set.InjOn c.symm (Metric.ball (c p) ε) := by
    intro a ha b hb hab
    have ha' : a ∈ (c.symm).source := by
      rw [OpenPartialHomeomorph.symm_source]; exact hball_t ha
    have hb' : b ∈ (c.symm).source := by
      rw [OpenPartialHomeomorph.symm_source]; exact hball_t hb
    exact (c.symm).injOn ha' hb' hab
  have hnt : Nontrivial E :=
    (rank_pos_iff_nontrivial (R := ℝ)).1 (zero_lt_one.trans (one_lt_rank_euclidean hn))
  have himg : (c.symm '' Metric.ball (c p) ε).Infinite :=
    (Set.infinite_image_iff hinj).mpr (infinite_ball_of_nontrivial hnt (c p) hε)
  refine himg.mono ?_
  rintro y ⟨z, hz, rfl⟩
  obtain ⟨w, hw, hwz⟩ := (hεsub hz).1
  rw [← hwz, c.left_inv hw.2]
  exact hw.1

theorem isPathConnected_sdiff_finite_of_isOpen {n : ℕ} (hn : 2 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {O : Set M} (hO : IsOpen O) (hOc : IsPathConnected O) {F : Set M} (hF : F.Finite)
    (hFO : F ⊆ O) :
    IsPathConnected (O \ F) := by
  haveI : LocallyPathConnectedSpace M := locallyPathConnectedSpace_chartedSpace (n := n)
  have hclosed : IsClosed F := hF.isClosed
  have hopen : IsOpen (O \ F) := hO.sdiff hclosed
  rw [← hopen.isConnected_iff_isPathConnected]
  refine ⟨?_, ?_⟩
  · exact (infinite_of_isOpen_nonempty hn hO hOc.nonempty).sdiff hF |>.nonempty
  · refine isPreconnected_sdiff_of_local_room hOc.isConnected.2 hO hclosed ?_
    intro y hyF N hN
    have hFy : (F \ {y}).Finite := hF.sdiff
    have hyFy : y ∉ F \ {y} := fun h => h.2 (mem_singleton y)
    have hN' : N ∩ (F \ {y})ᶜ ∩ O ∈ 𝓝 y :=
      Filter.inter_mem (Filter.inter_mem hN ((hFy.isClosed.isOpen_compl).mem_nhds hyFy))
        (hO.mem_nhds (hFO hyF))
    obtain ⟨O', hO'o, hyO', hO'sub, hO'pc⟩ := room_at_point_manifold (n := n) hn hN'
    have hsub : O' \ F = O' \ {y} := by
      ext x
      constructor
      · intro hx
        refine ⟨hx.1, ?_⟩
        intro h
        rw [Set.mem_singleton_iff] at h
        exact hx.2 (h.symm ▸ hyF)
      · intro hx
        refine ⟨hx.1, ?_⟩
        intro hxF
        have hxNotY : x ≠ y := by simpa using hx.2
        exact (hO'sub hx.1).1.2 ⟨hxF, by simpa using hxNotY⟩
    refine ⟨O', hO'o, hyO', fun x hx => (hO'sub hx).1.1, ?_, ?_⟩
    · rw [hsub]
      exact hO'pc.nonempty
    · rw [hsub]
      exact hO'pc.isConnected.2

end Work.Whitney.PathTools
