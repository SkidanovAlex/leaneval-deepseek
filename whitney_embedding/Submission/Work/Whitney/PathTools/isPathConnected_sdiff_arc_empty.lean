import Mathlib
import Submission.Work.Whitney.PathTools.room_at_arc_model
import Submission.Work.Whitney.PathTools.isPathConnected_compl_finite
import Submission.Work.Whitney.PathTools.isPreconnected_sdiff_of_local_room

/-!
# Removing an arc from an open path connected set in a topological `n`-manifold (`n ≥ 3`)

The main result is `Work.Whitney.PathTools.isPathConnected_sdiff_arc_empty`: if `W` is an open
path connected subset of a topological `n`-manifold with `n ≥ 3` and `γ : ℝ → M` is a continuous
map which is injective on `[0,1]` and maps `[0,1]` into `W`, then `W \ γ '' [0,1]` is again path
connected.

The proof has two independent inputs.

* **Local room at the arc** (`room_at_arc_manifold` below): near every point `γ s` of the arc there
  is an open neighbourhood `O` (inside any prescribed neighbourhood of `γ s`) such that `O` minus
  the image of the arc is path connected.  Concretely, `O` is chosen so small that its intersection
  with the arc is a *single* compact sub-arc; `O` minus that sub-arc is then the homeomorphic image
  (under the inverse chart) of a Euclidean ball minus the image of a compact subset of `ℝ` under an
  injective continuous map — which is path connected by the model statement
  `Work.Whitney.PathTools.room_at_arc_model`.

* **The general connectedness principle** `isPreconnected_sdiff_of_local_room`, which upgrades the
  pointwise room to `IsPreconnected (W \ γ '' [0,1])`; as `W \ γ '' [0,1]` is open and the manifold
  is locally path connected, preconnectedness of an open set is equivalent to path connectedness.
-/

namespace Work.Whitney.PathTools

open Set Topology Filter

/-- **Local room at a point of an injective arc.**  For a continuous arc `γ` in a topological
`n`-manifold (`n ≥ 3`) which is injective on `[0,1]`, every neighbourhood `N` of a point `γ s` of
the arc contains an open neighbourhood `O` of `γ s` such that `O` minus the image of the arc is
path connected. -/
theorem room_at_arc_manifold {n : ℕ} (hn : 3 ≤ n) {M : Type*} [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {γ : ℝ → M} (hγ : Continuous γ) (hγinj : Set.InjOn γ (Set.Icc (0:ℝ) 1))
    {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1) {N : Set M} (hN : N ∈ nhds (γ s)) :
    ∃ O : Set M, IsOpen O ∧ γ s ∈ O ∧ O ⊆ N ∧ IsPathConnected (O \ γ '' Set.Icc (0:ℝ) 1) := by
  haveI : LocallyPathConnectedSpace M := locallyPathConnectedSpace_chartedSpace (n := n)
  -- Replace `N` by an open neighbourhood of `γ s` contained in it.
  obtain ⟨N₀, hN₀N, hN₀open, hγsN₀⟩ := mem_nhds_iff.mp hN
  let E := EuclideanSpace ℝ (Fin n)
  let c : OpenPartialHomeomorph M E := chartAt E (γ s)
  have hy : γ s ∈ c.source := mem_chart_source E (γ s)
  -- A number `δ > 0` such that `γ (Icc (s-δ) (s+δ)) ⊆ N₀ ∩ c.source`.
  have hmem : γ ⁻¹' (N₀ ∩ c.source) ∈ nhds s :=
    ((hN₀open.inter c.open_source).preimage hγ).mem_nhds ⟨hγsN₀, hy⟩
  obtain ⟨δ₀, hδ₀, hδ₀sub⟩ := Metric.mem_nhds_iff.mp hmem
  set δ : ℝ := δ₀ / 2 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  have hIccsub : Set.Icc (s - δ) (s + δ) ⊆ γ ⁻¹' (N₀ ∩ c.source) := by
    intro t ht
    apply hδ₀sub
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- The "far" part of the arc, that the room will avoid.
  set F : Set ℝ := Set.Icc (0:ℝ) 1 ∩ (Set.Ioo (s - δ) (s + δ))ᶜ with hFdef
  have hFcpt : IsCompact F := isCompact_Icc.of_isClosed_subset
    (isClosed_Icc.inter isOpen_Ioo.isClosed_compl) (fun t ht => ht.1)
  have hyF : γ s ∉ γ '' F := by
    rintro ⟨t, htF, ht⟩
    have hts : t = s := hγinj htF.1 hs ht
    rw [hts] at htF
    exact htF.2 ⟨by linarith [hδpos], by linarith [hδpos]⟩
  -- A chart ball around `γ s` avoiding the far part and contained in `N₀ ∩ c.source`.
  have hnhdsU : (γ '' F)ᶜ ∩ (N₀ ∩ c.source) ∈ nhds (γ s) :=
    Filter.inter_mem ((hFcpt.image hγ).isClosed.isOpen_compl.mem_nhds hyF)
      (Filter.inter_mem (hN₀open.mem_nhds hγsN₀) (c.open_source.mem_nhds hy))
  have hnhdsU' : c '' ((γ '' F)ᶜ ∩ (N₀ ∩ c.source)) ∈ nhds (c (γ s)) :=
    c.image_mem_nhds hy hnhdsU
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hnhdsU'
  -- The local piece of the arc.
  set J : Set ℝ := Set.Icc (0:ℝ) 1 ∩ Set.Icc (s - δ) (s + δ) with hJdef
  have hJcpt : IsCompact J := isCompact_Icc.of_isClosed_subset
    (isClosed_Icc.inter isClosed_Icc) (fun t ht => ht.1)
  have hJsrc : ∀ t ∈ J, γ t ∈ c.source := fun t ht => (hIccsub ht.2).2
  have hsJ : s ∈ J := ⟨hs, ⟨by linarith [hδpos], by linarith [hδpos]⟩⟩
  let hfun : ℝ → E := fun t => c (γ t)
  have hJcont : ContinuousOn hfun J :=
    c.continuousOn.comp hγ.continuousOn (fun t ht => hJsrc t ht)
  have hJinj : Set.InjOn hfun J := by
    intro t₁ ht₁ t₂ ht₂ h
    exact hγinj ht₁.1 ht₂.1 (c.injOn (hJsrc t₁ ht₁) (hJsrc t₂ ht₂) h)
  have hpmem : c (γ s) ∈ hfun '' J := ⟨s, hsJ, rfl⟩
  obtain ⟨r₀, hr₀, hr₀r, hpc⟩ := room_at_arc_model (n := n) hn hJcpt hJcont hJinj hpmem hr
  -- The candidate room.
  set O : Set M := c.symm '' Metric.ball (c (γ s)) r₀ with hOdef
  have hr₀sub : Metric.ball (c (γ s)) r₀ ⊆ c '' ((γ '' F)ᶜ ∩ (N₀ ∩ c.source)) :=
    (Metric.ball_subset_ball (le_of_lt hr₀r)).trans hrsub
  have hOtgt : Metric.ball (c (γ s)) r₀ ⊆ c.target := by
    intro z hz
    obtain ⟨w, hw, hwc⟩ := hr₀sub hz
    rw [← hwc]
    exact c.map_source hw.2.2
  have hOopen : IsOpen O := c.isOpen_image_symm_of_subset_target Metric.isOpen_ball hOtgt
  have hyO : γ s ∈ O := ⟨c (γ s), Metric.mem_ball_self hr₀, c.left_inv hy⟩
  have hOU : O ⊆ (γ '' F)ᶜ := by
    rintro y ⟨z, hz, rfl⟩
    obtain ⟨w, hw, hwc⟩ := hr₀sub hz
    rw [← hwc, c.left_inv hw.2.2]
    exact hw.1
  have hON₀ : O ⊆ N₀ := by
    rintro y ⟨z, hz, rfl⟩
    obtain ⟨w, hw, hwc⟩ := hr₀sub hz
    rw [← hwc, c.left_inv hw.2.2]
    exact hw.2.1
  have hON : O ⊆ N := fun y hy => hN₀N (hON₀ hy)
  have hAclosed : IsClosed (γ '' Set.Icc (0:ℝ) 1) := (isCompact_Icc.image hγ).isClosed
  -- The room is the chart image of the model room.
  have hmain : O \ γ '' Set.Icc (0:ℝ) 1
      = c.symm '' (Metric.ball (c (γ s)) r₀ \ hfun '' J) := by
    ext y; constructor
    · rintro ⟨hyO, hyA⟩
      obtain ⟨z, hz, hzy⟩ := hyO
      have hztgt : z ∈ c.target := hOtgt hz
      refine ⟨z, ⟨hz, ?_⟩, hzy⟩
      rintro ⟨t, htJ, ht⟩
      have hsrc : γ t ∈ c.source := hJsrc t htJ
      have hyγ : γ t = y := by
        rw [← hzy, ← ht]
        exact (c.left_inv hsrc).symm
      exact hyA ⟨t, htJ.1, hyγ⟩
    · rintro ⟨z, ⟨hz, hzJ⟩, hzy⟩
      have hztgt : z ∈ c.target := hOtgt hz
      refine ⟨⟨z, hz, hzy⟩, ?_⟩
      rintro ⟨t, ht, hty⟩
      have hnotF : t ∉ F := by
        intro htF
        exact hOU ⟨z, hz, hzy⟩ ⟨t, htF, hty⟩
      have hIt : t ∈ Set.Ioo (s - δ) (s + δ) := by
        by_contra hcon
        exact hnotF ⟨ht, hcon⟩
      have htJ : t ∈ J := ⟨ht, ⟨le_of_lt hIt.1, le_of_lt hIt.2⟩⟩
      have htz : hfun t = z := by
        have h1 : γ t = c.symm z := by rw [hty, hzy]
        show c (γ t) = z
        rw [h1, c.right_inv hztgt]
      exact hzJ ⟨t, htJ, htz⟩
  have hOp' : IsOpen (c.symm '' (Metric.ball (c (γ s)) r₀ \ hfun '' J)) := by
    rw [← hmain]; exact hOopen.sdiff hAclosed
  have hne : (c.symm '' (Metric.ball (c (γ s)) r₀ \ hfun '' J)).Nonempty :=
    Set.Nonempty.image c.symm hpc.isConnected.1
  have hpre : IsPreconnected (c.symm '' (Metric.ball (c (γ s)) r₀ \ hfun '' J)) :=
    hpc.isConnected.2.image c.symm (c.continuousOn_symm.mono (fun z hz => hOtgt hz.1))
  refine ⟨O, hOopen, hyO, hON, ?_⟩
  rw [hmain]
  exact hOp'.isConnected_iff_isPathConnected.mp ⟨hne, hpre⟩

/-- Removing the image of an injective arc from an open path connected set in an `n`-manifold
(`n ≥ 3`) keeps it path connected. -/
theorem isPathConnected_sdiff_arc_empty {n : ℕ} (hn : 3 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {W : Set M} (hW : IsOpen W) (hWc : IsPathConnected W)
    {γ : ℝ → M} (hγ : Continuous γ) (hγinj : Set.InjOn γ (Set.Icc (0:ℝ) 1))
    (hγW : ∀ t ∈ Set.Icc (0:ℝ) 1, γ t ∈ W) :
    IsPathConnected (W \ γ '' Set.Icc (0:ℝ) 1) := by
  haveI : LocallyPathConnectedSpace M := locallyPathConnectedSpace_chartedSpace (n := n)
  have hclosed : IsClosed (γ '' Set.Icc (0:ℝ) 1) := (isCompact_Icc.image hγ).isClosed
  have hopen : IsOpen (W \ γ '' Set.Icc (0:ℝ) 1) := hW.sdiff hclosed
  rw [← hopen.isConnected_iff_isPathConnected]
  refine ⟨?_, ?_⟩
  · obtain ⟨O, -, hOy, hOW, hOpc⟩ :=
      room_at_arc_manifold (n := n) hn hγ hγinj (s := 0) (by norm_num) (N := W)
        (hW.mem_nhds (hγW 0 (by norm_num)))
    exact hOpc.isConnected.1.mono (fun x hx => ⟨hOW hx.1, hx.2⟩)
  · refine isPreconnected_sdiff_of_local_room hWc.isConnected.2 hW hclosed ?_
    rintro y ⟨s, hs, rfl⟩ N hN
    obtain ⟨O, hOo, hOy, hON, hOpc⟩ := room_at_arc_manifold (n := n) hn hγ hγinj hs hN
    exact ⟨O, hOo, hOy, hON, hOpc.isConnected.1, hOpc.isConnected.2⟩

end Work.Whitney.PathTools
