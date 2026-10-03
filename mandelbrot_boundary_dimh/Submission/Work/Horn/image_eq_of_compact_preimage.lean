import Mathlib
import Submission.Work.Interfaces.Parabolic

namespace Work.Horn

open Set Filter Metric

open scoped Topology

/-- **Surjectivity of a proper self-map onto a connected target** (`NOTES_GERM_F0.md` §51, item 2:
Reviewer 2's suggested route, which *derives* `honto : G '' W (n+1) i = W n i` instead of assuming
it).

`G` is holomorphic on the open `D`; `Wn ⊆ D` is open, connected (hence nonempty); `Wn1 ⊆ D` is
open, nonempty, and mapped by `G` into `Wn`; and `G` is proper over `Wn` in the sense that
preimages of compact subsets of `Wn` are compact inside `Wn1`.

Conclusion: `G '' Wn1 = Wn`.

Proof, with the reviewers' per-component refinement (note `Wn1` is *not* assumed connected):

* `G` is non-constant on every component `C` of `Wn1`: if `G ≡ c` on `C`, then `c = G x ∈ Wn` by
  `hmaps`, so `L = {c} ⊆ Wn` is compact and `hprop` makes `Wn1 ∩ G ⁻¹' {c} ⊇ C` compact — but `C`
  is a nonempty open subset of `ℂ`, and no such set is compact.  Hence `G '' Wn1` is open (open
  mapping principle on the open set `Wn1` at each of its points).
* `G '' Wn1` is closed in `Wn`: for `y ∈ Wn ∩ closure (G '' Wn1)` take `closedBall y r ⊆ Wn`
  (`hWn` open); with `L` that ball, the compact set `G '' (Wn1 ∩ G ⁻¹' L)` (continuous image of
  the set made compact by `hprop`) contains points of `G '' Wn1` arbitrarily close to `y`, so
  `y ∈ G '' (Wn1 ∩ G ⁻¹' L) ⊆ G '' Wn1`.
* Nonempty (`hW1ne`), open and closed in the connected `Wn`, so it equals `Wn`.

Self-contained plane analysis/topology: nothing horn-specific, and it is exactly the tool
`Work.Horn.isCompact_inter_preimage_of_chain` needs without appealing to level-wise injectivity
(which §51 records is incompatible with the `hni` that conjunct 1/2 require).  Once it lands, the
restatement of (1) need not carry `honto` as a hypothesis. -/
theorem image_eq_of_compact_preimage {G : ℂ → ℂ} {D Wn Wn1 : Set ℂ}
    (hD : IsOpen D) (hG : DifferentiableOn ℂ G D)
    (hWn : IsOpen Wn) (hWnD : Wn ⊆ D) (hWnc : IsConnected Wn)
    (hW1o : IsOpen Wn1) (hW1D : Wn1 ⊆ D) (hW1ne : Wn1.Nonempty)
    (hmaps : G '' Wn1 ⊆ Wn)
    (hprop : ∀ L : Set ℂ, L ⊆ Wn → IsCompact L → IsCompact (Wn1 ∩ G ⁻¹' L)) :
    G '' Wn1 = Wn := by
  have hGcont : ContinuousOn G Wn1 := hG.continuousOn.mono hW1D
  have hGan : AnalyticOnNhd ℂ G Wn1 := (hG.mono hW1D).analyticOnNhd hW1o
  -- Step 1: `G '' Wn1` is open.
  -- Each point of `Wn1` either has `G` non-constant nearby (open mapping theorem) or `G` is
  -- constant on a whole component of `Wn1`, which is impossible by compactness of the fibre.
  have hopen : IsOpen (G '' Wn1) := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨x, hx, rfl⟩
    rcases (hGan x hx).eventually_constant_or_nhds_le_map_nhds with hconst | hmap
    · exfalso
      let C : Set ℂ := connectedComponentIn Wn1 x
      have hxC : x ∈ C := mem_connectedComponentIn hx
      have hCpre : IsPreconnected C := isPreconnected_connectedComponentIn
      have hCW : C ⊆ Wn1 := connectedComponentIn_subset Wn1 x
      have hCopen : IsOpen C := hW1o.connectedComponentIn
      -- `G` is constant on the component `C`, by the identity theorem for preconnected sets.
      have hCconst : ∀ z ∈ C, G z = G x :=
        AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (hGan.mono hCW)
          (analyticOnNhd_const (v := G x)) hCpre hxC hconst
      have hGxWn : G x ∈ Wn := hmaps ⟨x, hx, rfl⟩
      -- so `C` is contained in the compact fibre `Wn1 ∩ G ⁻¹' {G x}`.
      have hKc : IsCompact (Wn1 ∩ G ⁻¹' {G x}) :=
        hprop {G x} (Set.singleton_subset_iff.mpr hGxWn) isCompact_singleton
      have hCK : C ⊆ Wn1 ∩ G ⁻¹' {G x} := fun z hz =>
        ⟨hCW hz, by simpa using hCconst z hz⟩
      -- hence `closure C` is preconnected, lies in `Wn1` and contains `x`, so it is inside `C`;
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
        disjoint_compl_right (by rintro z -; by_cases h : z ∈ C <;> simp [h]) with h | h
      · exact hCne (Set.eq_univ_of_univ_subset h)
      · exact (h (mem_univ x)) hxC
    · exact hmap (Filter.image_mem_map (hW1o.mem_nhds hx))
  -- Step 2: `G '' Wn1` is closed inside the open set `Wn`.
  have hclosed : closure (G '' Wn1) ∩ Wn ⊆ G '' Wn1 := by
    rintro y ⟨hycl, hyWn⟩
    -- a closed ball around `y` still lies in `Wn`.
    obtain ⟨r, hr, hrsub⟩ : ∃ r : ℝ, 0 < r ∧ closedBall y r ⊆ Wn := by
      rw [Metric.isOpen_iff] at hWn
      obtain ⟨ε, hε, hεsub⟩ := hWn y hyWn
      exact ⟨ε / 2, half_pos hε, fun z hz =>
        hεsub (closedBall_subset_ball (by linarith) hz)⟩
    have hKc : IsCompact (Wn1 ∩ G ⁻¹' closedBall y r) :=
      hprop _ hrsub (isCompact_closedBall y r)
    have himg : IsCompact (G '' (Wn1 ∩ G ⁻¹' closedBall y r)) :=
      hKc.image_of_continuousOn (hGcont.mono inter_subset_left)
    have hmem : y ∈ G '' (Wn1 ∩ G ⁻¹' closedBall y r) := by
      rw [← himg.isClosed.closure_eq, mem_closure_iff_nhds]
      intro t ht
      have htU : t ∩ ball y r ∈ 𝓝 y := Filter.inter_mem ht (ball_mem_nhds y hr)
      rw [mem_closure_iff_nhds] at hycl
      obtain ⟨z, ⟨hzt, hzb⟩, hzS⟩ := hycl (t ∩ ball y r) htU
      obtain ⟨w, hw1, rfl⟩ := hzS
      exact ⟨G w, hzt, ⟨w, ⟨hw1, ball_subset_closedBall hzb⟩, rfl⟩⟩
    exact Set.image_mono inter_subset_left hmem
  -- Step 3: a nonempty subset of the connected `Wn` that is open and closed is all of `Wn`.
  refine Set.Subset.antisymm hmaps ?_
  refine hWnc.isPreconnected.subset_of_closure_inter_subset hopen ?_ hclosed
  obtain ⟨x, hx⟩ := hW1ne
  exact ⟨G x, hmaps ⟨x, hx, rfl⟩, ⟨x, hx, rfl⟩⟩

end Work.Horn
