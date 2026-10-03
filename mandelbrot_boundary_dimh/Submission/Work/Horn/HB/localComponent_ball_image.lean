import Mathlib

/-!
# The local component over a ball maps onto the ball

Let `g : ℂ → ℂ` be a local homeomorphism on the open set `U = D ∩ g ⁻¹' ball v r`, and let
`C = connectedComponentIn U x` be the connected component of `x` in `U`.  Assume moreover that
`g` is *proper over the ball* on `C`: for every compact `K ⊆ ball v r` the set
`C ∩ g ⁻¹' K` is compact.  Then `g '' C = ball v r`.

This is the abstract topological step (HB4 of the Horn design, `DESIGN.md`) which shows that the
"finite local monodromy over `v`" hypothesis used in Shishikura's Proposition 5.3 / Lemma 5.4
forces every local component over the ball to be a genuine covering of the ball, hence to contain
a (unique) preimage of the critical value `v`.

The proof is elementary plane topology:

* `U` is open.  Indeed, at a point `z ∈ U` the local homeomorphism gives an open partial
  homeomorphism `e` with `g = e` near `z`; the set `(e.source ∩ e ⁻¹' ball v r) ∩ D` is an open
  neighbourhood of `z` contained in `U`.
* Hence `C` is open (connected components of open subsets of the locally connected space `ℂ`),
  and `g '' C` is open: at `z ∈ C` the map `g` sends the neighbourhood filter `𝓝 z` to `𝓝 (g z)`
  (`IsLocalHomeomorphOn.map_nhds_eq`), so `g '' C ∈ 𝓝 (g z)`.
* `g '' C` is *closed* in `ball v r`: if `w ∈ ball v r` is a limit point, take a small closed
  ball `K` around `w` with `K ⊆ ball v r`; the compactness hypothesis makes
  `g '' (C ∩ g ⁻¹' K)` compact hence closed, and `w`, being a limit point of `g '' C` and lying in
  the interior of `K`, is a limit point of `g '' C ∩ K = g '' (C ∩ g ⁻¹' K)`.
* Since `ball v r` is preconnected (it is convex) and `g '' C` is a nonempty subset of it that
  is both open and closed inside it, the two are equal.  This last step is phrased directly with
  `IsPreconnected`, using the two open sets `g '' C` and `(closure (g '' C))ᶜ`.
-/

namespace Work.Horn.HB

open Set Metric Filter Topology

/-- The image under a local homeomorphism `g` of a connected component of an open set `U` is
open.  (This is the `IsLocalHomeomorphOn` version of "a local homeomorphism is an open map",
obtained from `IsLocalHomeomorphOn.map_nhds_eq` and the openness of components of open sets in
the locally connected space `ℂ`.) -/
lemma isOpen_image_connectedComponentIn {g : ℂ → ℂ} {U : Set ℂ} {x : ℂ}
    (hUo : IsOpen U) (hloc : IsLocalHomeomorphOn g U) :
    IsOpen (g '' connectedComponentIn U x) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨z, hzC, rfl⟩
  have hzU : z ∈ U := connectedComponentIn_subset U x hzC
  have hCn : connectedComponentIn U x ∈ 𝓝 z := (hUo.connectedComponentIn).mem_nhds hzC
  have hmap : (𝓝 z).map g = 𝓝 (g z) := hloc.map_nhds_eq hzU
  have h := Filter.image_mem_map (m := g) hCn
  rwa [hmap] at h

theorem localComponent_ball_image {g : ℂ → ℂ} {D : Set ℂ} {v : ℂ} {r : ℝ}
    (hDo : IsOpen D) (hcont : ∀ z ∈ D, ContinuousAt g z)
    (hloc : IsLocalHomeomorphOn g (D ∩ g ⁻¹' Metric.ball v r))
    (hLF : ∀ x ∈ D, g x ∈ Metric.ball v r → ∀ K ⊆ Metric.ball v r, IsCompact K →
      IsCompact (connectedComponentIn (D ∩ g ⁻¹' Metric.ball v r) x ∩ g ⁻¹' K))
    {x : ℂ} (hxD : x ∈ D) (hxr : g x ∈ Metric.ball v r) :
    Metric.ball v r ⊆ g '' connectedComponentIn (D ∩ g ⁻¹' Metric.ball v r) x := by
  set U : Set ℂ := D ∩ g ⁻¹' Metric.ball v r with hUdef
  set C : Set ℂ := connectedComponentIn U x with hCdef
  have hxU : x ∈ U := ⟨hxD, hxr⟩
  -- `U` is open: at each of its points the local homeomorphism provides an open partial
  -- homeomorphism `e` agreeing with `g`, and `(e.source ∩ e ⁻¹' ball v r) ∩ D` is an open
  -- neighbourhood of that point inside `U`.
  have hUo : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    obtain ⟨e, hze, heq⟩ := hloc z hz
    have hez : e z = g z := (congrFun heq z).symm
    have hW : IsOpen ((e.source ∩ e ⁻¹' Metric.ball v r) ∩ D) :=
      (e.continuousOn_toFun.isOpen_inter_preimage e.open_source Metric.isOpen_ball).inter hDo
    have hzW : z ∈ (e.source ∩ e ⁻¹' Metric.ball v r) ∩ D :=
      ⟨⟨hze, by rw [Set.mem_preimage, hez]; exact hz.2⟩, hz.1⟩
    refine Filter.mem_of_superset (hW.mem_nhds hzW) ?_
    rintro y ⟨⟨hys, hyb⟩, hyD⟩
    rw [Set.mem_preimage] at hyb
    exact ⟨hyD, by show g y ∈ Metric.ball v r; rw [congrFun heq y]; exact hyb⟩
  -- `g '' C` is open.
  have hSopen : IsOpen (g '' C) := by
    rw [hCdef]
    exact isOpen_image_connectedComponentIn hUo hloc
  have hmain : Metric.ball v r ⊆ g '' C := by
    -- `g '' C` is closed inside the ball.
    have hSclosed : ∀ w ∈ Metric.ball v r, w ∈ closure (g '' C) → w ∈ g '' C := by
      intro w hw hwcl
      let K : Set ℂ := Metric.closedBall w ((r - dist w v) / 2)
      have hρpos : 0 < (r - dist w v) / 2 := by linarith [mem_ball.mp hw]
      have hKsub : K ⊆ Metric.ball v r := by
        intro y hy
        simp only [K, Metric.mem_ball, Metric.mem_closedBall] at hy ⊢
        linarith [dist_triangle y w v, mem_ball.mp hw]
      have hKc : IsCompact K := by
        simp only [K]; exact isCompact_closedBall w _
      have hA : IsCompact (C ∩ g ⁻¹' K) := hLF x hxD hxr K hKsub hKc
      have hAimg : IsCompact (g '' (C ∩ g ⁻¹' K)) :=
        hA.image_of_continuousOn
          (fun z hz => (hcont z (connectedComponentIn_subset U x hz.1).1).continuousWithinAt)
      have hwint : w ∈ interior K := by
        simp only [K]
        exact mem_interior_iff_mem_nhds.mpr
          (Filter.mem_of_superset (Metric.ball_mem_nhds w hρpos) Metric.ball_subset_closedBall)
      have hwm : w ∈ closure (g '' C ∩ interior K) :=
        (IsOpen.closure_inter isOpen_interior) ⟨hwcl, hwint⟩
      have hsub : g '' C ∩ interior K ⊆ g '' (C ∩ g ⁻¹' K) := by
        rintro _y ⟨⟨z, hzC, rfl⟩, hyint⟩
        exact ⟨z, ⟨hzC, Set.mem_preimage.mpr (interior_subset hyint)⟩, rfl⟩
      have hgot := hAimg.isClosed.closure_subset (closure_mono hsub hwm)
      exact Set.image_mono Set.inter_subset_left hgot
    -- `ball v r` is preconnected (convex), and `g '' C` is both open and closed inside it, so
    -- the two open sets `g '' C` and `(closure (g '' C))ᶜ` cover every point of the ball.
    have hpre : IsPreconnected (Metric.ball v r) := (convex_ball v r).isPreconnected
    intro w hw
    by_contra hwnot
    have hsub_uv : Metric.ball v r ⊆ g '' C ∪ (closure (g '' C))ᶜ := by
      intro z hz
      by_cases h : z ∈ closure (g '' C)
      · exact Or.inl (hSclosed z hz h)
      · exact Or.inr h
    have hne_u : ((Metric.ball v r) ∩ g '' C).Nonempty :=
      ⟨g x, hxr, mem_image_of_mem g (mem_connectedComponentIn hxU)⟩
    have hne_v : ((Metric.ball v r) ∩ (closure (g '' C))ᶜ).Nonempty :=
      ⟨w, hw, fun h => hwnot (hSclosed w hw h)⟩
    obtain ⟨z, hz, hzg, hzcl⟩ := hpre (g '' C) (closure (g '' C))ᶜ hSopen
      isClosed_closure.isOpen_compl hsub_uv hne_u hne_v
    exact hzcl (subset_closure hzg)
  exact hmain

end Work.Horn.HB
