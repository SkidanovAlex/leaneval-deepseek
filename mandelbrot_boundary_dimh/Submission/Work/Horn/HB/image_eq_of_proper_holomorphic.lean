import Mathlib

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# A proper holomorphic map onto a connected open set is surjective

If `G` is holomorphic on the open set `D`, `W' ⊆ D` is open and nonempty, `G` maps `W'` into the
open connected set `W`, and `G` is proper over `W` (the preimage of a compact subset of `W` is
compact inside `W'`), then `G '' W' = W`.

This is the standard argument:

* `G '' W'` is **open**: by the open mapping theorem at each point of `W'`.  The only case the open
  mapping theorem does not cover is that `G` is constant on a neighbourhood of `x ∈ W'`; then, by
  the identity theorem, `G` is constant on the whole connected component `C` of `W'` through `x`,
  so `C` is contained in the fibre `W' ∩ G ⁻¹' {G x}`, which is compact by properness.  A compact
  set containing the connected component `C` (which is open in `ℂ`, being a component of an open
  set) forces `C` to be closed and bounded, hence clopen; `ℂ` is connected, so `C = univ` or
  `C = ∅`, both absurd.
* `G '' W'` is **closed in `W`**: if `y ∈ W` is a limit point of `G '' W'`, take a closed ball
  `closedBall y r ⊆ W` around it (possible since `W` is open).  By properness the set
  `W' ∩ G ⁻¹' closedBall y r` is compact, and its image under the continuous map `G` is therefore
  compact and contains points of `G '' W'` arbitrarily close to `y`; as a compact set it is closed,
  so `y` lies in it.
* `W'` is nonempty, so `G '' W'` is nonempty, and a nonempty open and closed subset of the
  connected set `W` is all of `W`.

Note that no relation between `W` and the domain of holomorphy `D` is required: `G` is only ever
used on `W' ⊆ D`.
-/

namespace Work.Horn.HB

open Set Filter Metric

open scoped Topology

theorem image_eq_of_proper_holomorphic {G : ℂ → ℂ} {D W W' : Set ℂ}
    (hD : IsOpen D) (hG : DifferentiableOn ℂ G D)
    (hW : IsOpen W) (hWc : IsConnected W)
    (hW'o : IsOpen W') (hW'D : W' ⊆ D) (hW'ne : W'.Nonempty)
    (hmaps : G '' W' ⊆ W)
    (hprop : ∀ L : Set ℂ, L ⊆ W → IsCompact L → IsCompact (W' ∩ G ⁻¹' L)) :
    G '' W' = W := by
  -- `G` is continuous and analytic on `W'` (which is open and contained in the domain `D`).
  have hGcont : ContinuousOn G W' := hG.continuousOn.mono hW'D
  have hGan : AnalyticOnNhd ℂ G W' := (hG.mono hW'D).analyticOnNhd hW'o
  -- Step 1: `G '' W'` is open.
  have hopen : IsOpen (G '' W') := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨x, hx, rfl⟩
    rcases (hGan x hx).eventually_constant_or_nhds_le_map_nhds with hconst | hmap
    · -- `G` is constant near `x`: the connected component of `W'` through `x` lies in a fibre,
      -- which is compact by properness — impossible for an open set.
      exfalso
      let C : Set ℂ := connectedComponentIn W' x
      have hxC : x ∈ C := mem_connectedComponentIn hx
      have hCpre : IsPreconnected C := isPreconnected_connectedComponentIn
      have hCW : C ⊆ W' := connectedComponentIn_subset W' x
      have hCopen : IsOpen C := hW'o.connectedComponentIn
      -- `G` is constant on `C`, by the identity theorem for preconnected sets.
      have hCconst : ∀ z ∈ C, G z = G x :=
        AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (hGan.mono hCW)
          (analyticOnNhd_const (v := G x)) hCpre hxC hconst
      have hGxW : G x ∈ W := hmaps ⟨x, hx, rfl⟩
      -- so `C` is contained in the compact fibre `W' ∩ G ⁻¹' {G x}`.
      have hKc : IsCompact (W' ∩ G ⁻¹' {G x}) :=
        hprop {G x} (Set.singleton_subset_iff.mpr hGxW) isCompact_singleton
      have hCK : C ⊆ W' ∩ G ⁻¹' {G x} := fun z hz =>
        ⟨hCW hz, by simpa using hCconst z hz⟩
      -- hence `closure C` is preconnected, lies in `W'` and contains `x`, so it is inside `C`;
      -- i.e. `C` is closed.
      have hCcl : IsClosed C := by
        rw [← closure_subset_iff_isClosed]
        intro z hz
        exact IsPreconnected.subset_connectedComponentIn hCpre.closure (subset_closure hxC)
          ((IsCompact.isClosed hKc).closure_subset_iff.mpr hCK |>.trans inter_subset_left) hz
      -- `C` cannot be all of `ℂ`, since it is contained in a compact set.
      have hCne : C ≠ univ := fun h =>
        hKc.ne_univ (Set.eq_univ_of_univ_subset (h ▸ hCK))
      -- `C` is nonempty, open and closed in the preconnected space `ℂ`: contradiction.
      rcases (isPreconnected_univ (α := ℂ)).subset_or_subset hCopen hCcl.isOpen_compl
        disjoint_compl_right (by intro z _; rcases Classical.em (z ∈ C) with h | h <;> simp [h])
        with h | h
      · exact hCne (Set.eq_univ_of_univ_subset h)
      · exact (h (mem_univ x)) hxC
    · -- open mapping theorem: a neighbourhood of `x` maps onto a neighbourhood of `G x`
      exact hmap (Filter.image_mem_map (hW'o.mem_nhds hx))
  -- Step 2: `G '' W'` is closed inside the open set `W`.
  have hclosed : closure (G '' W') ∩ W ⊆ G '' W' := by
    rintro y ⟨hycl, hyW⟩
    -- a closed ball around `y` still lies in `W`.
    obtain ⟨r, hr, hrsub⟩ : ∃ r : ℝ, 0 < r ∧ closedBall y r ⊆ W := by
      rw [Metric.isOpen_iff] at hW
      obtain ⟨ε, hε, hεsub⟩ := hW y hyW
      exact ⟨ε / 2, half_pos hε, fun z hz =>
        hεsub (closedBall_subset_ball (by linarith) hz)⟩
    have hKc : IsCompact (W' ∩ G ⁻¹' closedBall y r) :=
      hprop _ hrsub (isCompact_closedBall y r)
    have himg : IsCompact (G '' (W' ∩ G ⁻¹' closedBall y r)) :=
      hKc.image_of_continuousOn (hGcont.mono inter_subset_left)
    have hmem : y ∈ G '' (W' ∩ G ⁻¹' closedBall y r) := by
      rw [← himg.isClosed.closure_eq, mem_closure_iff_nhds]
      intro t ht
      have htU : t ∩ ball y r ∈ 𝓝 y := Filter.inter_mem ht (ball_mem_nhds y hr)
      rw [mem_closure_iff_nhds] at hycl
      obtain ⟨z, ⟨hzt, hzb⟩, hzS⟩ := hycl (t ∩ ball y r) htU
      obtain ⟨w, hw1, rfl⟩ := hzS
      exact ⟨G w, hzt, ⟨w, ⟨hw1, ball_subset_closedBall hzb⟩, rfl⟩⟩
    exact Set.image_mono inter_subset_left hmem
  -- Step 3: a nonempty subset of the connected `W` that is open and closed is all of `W`.
  refine Set.Subset.antisymm hmaps ?_
  refine hWc.isPreconnected.subset_of_closure_inter_subset hopen ?_ hclosed
  obtain ⟨x, hx⟩ := hW'ne
  exact ⟨G x, hmaps ⟨x, hx, rfl⟩, ⟨x, hx, rfl⟩⟩

end Work.Horn.HB
