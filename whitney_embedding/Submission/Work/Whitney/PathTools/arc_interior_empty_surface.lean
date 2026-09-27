import Mathlib
import Submission.Work.Whitney.PathTools.interior_image_arc_empty

/-!
# The image of an arc in a surface has empty interior

Let `M` be a surface (a topological space charted over the plane `ℝ²`) and let `γ : ℝ → M` be a
continuous curve which is injective on `[0,1]`.  Then the image `γ '' [0,1]` has empty interior.

Proof.  Suppose the open set `C = interior (γ '' [0,1])` were nonempty; pick `p ∈ C` and a chart
`e` at `p`.  Then `W = C ∩ e.source` is a nonempty open set, so `U = e '' W` is a nonempty open
subset of the plane and contains a closed ball `D` of positive radius around `e p`.  The set
`T = [0,1] ∩ γ ⁻¹' (e.symm '' D)` of parameters of arc points mapped into that ball is compact;
on it the curve `t ↦ e (γ t)` is continuous and injective, and its image is *exactly* `D`, because
`e.symm '' D ⊆ W ⊆ C ⊆ γ '' [0,1]`.  By `Work.Whitney.PathTools.interior_image_arc_empty` that
image therefore has empty interior, whereas `D` is a closed ball of positive radius and has
nonempty interior.  Contradiction.
-/

open Set Metric Topology

namespace Work.Whitney.PathTools

theorem arc_interior_empty_surface {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    {γ : ℝ → M} (hγ : Continuous γ) (hinj : Set.InjOn γ (Set.Icc (0:ℝ) 1)) :
    interior (γ '' Set.Icc (0:ℝ) 1) = ∅ := by
  classical
  set A : Set M := γ '' Set.Icc (0:ℝ) 1 with hA
  by_contra hne
  have hne' : (interior A).Nonempty := Set.nonempty_iff_ne_empty.mpr hne
  obtain ⟨p, hpint⟩ := hne'
  -- a chart at `p`
  set e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)) :=
    chartAt (EuclideanSpace ℝ (Fin 2)) p with he
  have hp_src : p ∈ e.source := mem_chart_source _ p
  -- the nonempty open set `C = interior A` and its chart piece `W`
  set C : Set M := interior A with hC
  have hCopen : IsOpen C := isOpen_interior
  have hCA : C ⊆ A := interior_subset
  set W : Set M := C ∩ e.source with hW
  have hWopen : IsOpen W := hCopen.inter e.open_source
  have hpW : p ∈ W := ⟨hpint, hp_src⟩
  have hWe : W ⊆ e.source := inter_subset_right
  have hWA : W ⊆ A := (inter_subset_left).trans hCA
  set U : Set (EuclideanSpace ℝ (Fin 2)) := e '' W with hU
  have hUopen : IsOpen U := e.isOpen_image_of_subset_source hWopen hWe
  have hpU : e p ∈ U := ⟨p, hpW, rfl⟩
  have hUtarget : U ⊆ e.target := by
    rw [hU]
    calc e '' W ⊆ e '' e.source := Set.image_mono hWe
      _ = e.target := OpenPartialHomeomorph.image_source_eq_target e
  -- a closed ball inside `U`
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp (hUopen.mem_nhds hpU)
  set ε : ℝ := δ / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  have hball : Metric.closedBall (e p) ε ⊆ U :=
    (Metric.closedBall_subset_ball (show ε < δ by rw [hεdef]; linarith)).trans hδsub
  have hDtarget : Metric.closedBall (e p) ε ⊆ e.target := hball.trans hUtarget
  -- the disc, pulled back to `M`
  set D : Set M := e.symm '' Metric.closedBall (e p) ε with hD
  have hDmem : ∀ x : M, x ∈ D ↔ x ∈ e.source ∧ e x ∈ Metric.closedBall (e p) ε := by
    intro x
    rw [hD]
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzsrc : z ∈ e.symm.source := by
        rw [OpenPartialHomeomorph.symm_source]; exact hDtarget hz
      exact ⟨by rw [← OpenPartialHomeomorph.symm_target]; exact e.symm.map_source hzsrc,
        by rw [e.right_inv hzsrc]; exact hz⟩
    · rintro ⟨hxs, hxe⟩
      exact ⟨e x, hxe, e.left_inv hxs⟩
  have hDsub : D ⊆ e.source := fun x hx => ((hDmem x).1 hx).1
  have hDcompact : IsCompact D := by
    rw [hD]
    refine (isCompact_closedBall (e p) ε).image_of_continuousOn ?_
    exact e.symm.continuousOn.mono
      (by rw [OpenPartialHomeomorph.symm_source]; exact hDtarget)
  have hDclosed : IsClosed D := hDcompact.isClosed
  -- every point of the disc lies on the arc
  have hDA : D ⊆ A := by
    intro x hx
    obtain ⟨hxsrc, hxball⟩ := (hDmem x).1 hx
    have hxU : e x ∈ U := hball hxball
    rw [hU] at hxU
    obtain ⟨w, hwW, hwx⟩ := hxU
    have hxw : x = w := e.injOn hxsrc hwW.2 hwx.symm
    rw [hxw]
    exact hWA hwW
  -- the compact set of parameters of arc points mapped into the disc
  set T : Set ℝ := Set.Icc (0:ℝ) 1 ∩ γ ⁻¹' D with hT
  have hTclosed : IsClosed T := by
    rw [hT]; exact isClosed_Icc.inter (hDclosed.preimage hγ)
  have hTcompact : IsCompact T :=
    IsCompact.of_isClosed_subset isCompact_Icc hTclosed (by rw [hT]; exact inter_subset_left)
  have hTsrc : ∀ t ∈ T, γ t ∈ e.source := fun t ht => by
    rw [hT] at ht
    exact ((hDmem (γ t)).1 ht.2).1
  have hTI : ∀ t ∈ T, t ∈ Set.Icc (0:ℝ) 1 := fun t ht => by
    rw [hT] at ht
    exact ht.1
  have hcont : ContinuousOn (fun t => e (γ t)) T :=
    e.continuousOn.comp hγ.continuousOn hTsrc
  have hinjE : Set.InjOn (fun t => e (γ t)) T := by
    intro t₁ ht₁ t₂ ht₂ h
    exact hinj (hTI t₁ ht₁) (hTI t₂ ht₂) (e.injOn (hTsrc t₁ ht₁) (hTsrc t₂ ht₂) h)
  -- the image of that parameter set is exactly the closed ball
  have hImage : (fun t => e (γ t)) '' T = Metric.closedBall (e p) ε := by
    apply subset_antisymm
    · rintro z ⟨t, ht, rfl⟩
      rw [hT] at ht
      exact ((hDmem (γ t)).1 ht.2).2
    · intro z hz
      have hzU : z ∈ U := hball hz
      rw [hU] at hzU
      obtain ⟨w, hwW, hwz⟩ := hzU
      have hwA : w ∈ A := hWA hwW
      rw [hA] at hwA
      obtain ⟨t, htI, htw⟩ := hwA
      refine ⟨t, ?_, ?_⟩
      · rw [hT]
        refine ⟨htI, ?_⟩
        show γ t ∈ D
        rw [htw]
        exact (hDmem w).2 ⟨hwW.2, by rw [hwz]; exact hz⟩
      · show e (γ t) = z
        rw [htw, hwz]
  -- but a closed ball of positive radius has nonempty interior
  have hempty : interior (Metric.closedBall (e p) ε) = ∅ := by
    rw [← hImage]
    exact interior_image_arc_empty hTcompact hcont hinjE
  have hne'' : (interior (Metric.closedBall (e p) ε)).Nonempty :=
    ⟨e p, Metric.ball_subset_interior_closedBall (Metric.mem_ball_self hε)⟩
  rw [hempty] at hne''
  exact Set.not_nonempty_empty hne''

end Work.Whitney.PathTools
