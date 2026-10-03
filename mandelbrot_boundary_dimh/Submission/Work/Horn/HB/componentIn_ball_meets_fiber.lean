import Mathlib
import Submission.Work.Horn.HB.ambient_local_homeo

namespace Work.Horn.HB

open Set Metric Filter Topology
open scoped Topology

/-- The image of a connected component of an open set under a map which is a local homeomorphism
on a set containing that component is open.  (The point is that the component is a neighbourhood
of each of its points, because components of open subsets of a locally connected space are open,
and a local homeomorphism maps the neighbourhood filter of a point to the neighbourhood filter of
its image.) -/
theorem isOpen_image_connectedComponentIn_of_localHomeo {g : ℂ → ℂ} {W U : Set ℂ} {x : ℂ}
    (hWo : IsOpen W) (hsub : connectedComponentIn W x ⊆ U) (hloc : IsLocalHomeomorphOn g U) :
    IsOpen (g '' connectedComponentIn W x) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨z, hzC, rfl⟩
  have hCn : connectedComponentIn W x ∈ 𝓝 z := (hWo.connectedComponentIn).mem_nhds hzC
  have hmap : (𝓝 z).map g = 𝓝 (g z) := hloc.map_nhds_eq (hsub hzC)
  have h : g '' connectedComponentIn W x ∈ (𝓝 z).map g := Filter.image_mem_map (m := g) hCn
  rwa [hmap] at h

/-- **The local component over a ball contains a preimage of the special value.**

Let `g` be a covering map on the twice punctured plane, restricted to an open set `D`, let
`ball v ρ` be a ball around the special value `v` which does not contain the origin, and let `x ∈ D`
have `g x` in that ball.  If moreover the connected component of `x` in `D ∩ g ⁻¹' ball v ρ` is
proper over every compact subset of the ball (the "finite local monodromy"/LF hypothesis), then
that component meets the fibre `g ⁻¹' {v}`.

Indeed, if the component `C` met no point over `v`, then `g '' C` would be an open subset of the
ball (the covering is a local homeomorphism on the region where `g` avoids `0` and `v`, and `C` is
open) which is also closed in the ball (LF makes `C ∩ g ⁻¹' K` compact for compact `K ⊆ ball`, so
its image is closed).  Since the ball is preconnected and `g '' C` is non-empty, this forces
`ball v ρ ⊆ g '' C`, so `v ∈ g '' C`: a point of `C` maps to `v`, as claimed. -/
theorem componentIn_ball_meets_fiber {g : ℂ → ℂ} {D : Set ℂ} {v : ℂ} {ρ : ℝ} {x : ℂ}
    (hDo : IsOpen D) (hgd : DifferentiableOn ℂ g D)
    (hcov : IsCoveringMapOn (fun z : ↥D => g z) {ζ : ℂ | ζ ≠ 0 ∧ ζ ≠ v})
    (h0ρ : (0 : ℂ) ∉ Metric.ball v ρ)
    (hx : x ∈ D) (hxρ : g x ∈ Metric.ball v ρ)
    (hLF : ∀ y ∈ D, g y ∈ Metric.ball v ρ → ∀ K ⊆ Metric.ball v ρ, IsCompact K →
      IsCompact (connectedComponentIn (D ∩ g ⁻¹' Metric.ball v ρ) y ∩ g ⁻¹' K)) :
    (connectedComponentIn (D ∩ g ⁻¹' Metric.ball v ρ) x ∩ g ⁻¹' {v}).Nonempty := by
  classical
  have hρpos : 0 < ρ := lt_of_le_of_lt dist_nonneg (Metric.mem_ball.mp hxρ)
  by_cases hxv : g x = v
  · exact ⟨x, mem_connectedComponentIn ⟨hx, hxρ⟩, hxv⟩
  -- `g` is continuous on the open set `D`
  have hgcont : ∀ z ∈ D, ContinuousAt g z :=
    fun z hz => (hgd.differentiableAt (hDo.mem_nhds hz)).continuousAt
  set W : Set ℂ := D ∩ g ⁻¹' Metric.ball v ρ with hW
  set C : Set ℂ := connectedComponentIn W x with hC
  have hxW : x ∈ W := by rw [hW]; exact ⟨hx, hxρ⟩
  have hxC : x ∈ C := by rw [hC]; exact mem_connectedComponentIn hxW
  have hCW : C ⊆ W := by rw [hC]; exact connectedComponentIn_subset W x
  have hWopen : IsOpen W := by
    rw [hW, isOpen_iff_mem_nhds]
    rintro z ⟨hzD, hzB⟩
    exact Filter.inter_mem (hDo.mem_nhds hzD)
      ((hgcont z hzD).preimage_mem_nhds (Metric.isOpen_ball.mem_nhds hzB))
  have hCopen : IsOpen C := by rw [hC]; exact hWopen.connectedComponentIn
  -- suppose the component misses the fibre over `v`
  by_contra hnon
  have hCmiss : C ∩ g ⁻¹' {v} = ∅ := Set.not_nonempty_iff_eq_empty.mp hnon
  have hCU : C ⊆ D ∩ g ⁻¹' {ζ : ℂ | ζ ≠ 0 ∧ ζ ≠ v} := by
    intro z hzC
    obtain ⟨hzD, hzB⟩ := hCW hzC
    refine ⟨hzD, ?_, ?_⟩
    · intro hzero
      rw [Set.mem_preimage, hzero] at hzB
      exact h0ρ hzB
    · rintro hzv
      have hmem : z ∈ C ∩ g ⁻¹' {v} := ⟨hzC, hzv⟩
      rw [hCmiss] at hmem
      exact hmem
  have hvnotin : v ∉ g '' C := by
    rintro ⟨z, hzC, hzv⟩
    have hmem : z ∈ C ∩ g ⁻¹' {v} := ⟨hzC, hzv⟩
    rw [hCmiss] at hmem
    exact hmem
  -- the covering gives a local homeomorphism on `D ∩ g ⁻¹' {0, v}ᶜ`
  have hloc : IsLocalHomeomorphOn g (D ∩ g ⁻¹' {ζ : ℂ | ζ ≠ 0 ∧ ζ ≠ v}) :=
    ambient_local_homeo hDo hcov
  -- **`g '' C` is open**
  have hopen_aux : IsOpen (g '' connectedComponentIn W x) :=
    isOpen_image_connectedComponentIn_of_localHomeo hWopen (fun z hz => hCU (hC ▸ hz)) hloc
  have hopen : IsOpen (g '' C) := hC ▸ hopen_aux
  -- **`g '' C` is closed in the ball**: LF makes `C ∩ g ⁻¹' K` compact for compact `K ⊆ ball`
  have hclosedB : ∀ w ∈ Metric.ball v ρ, w ∈ closure (g '' C) → w ∈ g '' C := by
    intro w hw hwcl
    have hd : dist w v < ρ := Metric.mem_ball.mp hw
    let K : Set ℂ := Metric.closedBall w ((ρ - dist w v) / 2)
    have hKpos : 0 < (ρ - dist w v) / 2 := by linarith
    have hKsub : K ⊆ Metric.ball v ρ := by
      intro y hy
      simp only [K, Metric.mem_ball, Metric.mem_closedBall] at hy ⊢
      linarith [dist_triangle y w v]
    have hKc : IsCompact K := by
      simp only [K]
      exact isCompact_closedBall w _
    have hA : IsCompact (C ∩ g ⁻¹' K) := hC ▸ hLF x hx hxρ K hKsub hKc
    have hAcont : ContinuousOn g (C ∩ g ⁻¹' K) := fun z hz =>
      (hgcont z ((hCW hz.1).1)).continuousWithinAt
    have hAimg : IsCompact (g '' (C ∩ g ⁻¹' K)) := hA.image_of_continuousOn hAcont
    have hwint : w ∈ interior K := by
      simp only [K]
      exact mem_interior_iff_mem_nhds.mpr
        (Filter.mem_of_superset (Metric.ball_mem_nhds w hKpos) Metric.ball_subset_closedBall)
    have hwm : w ∈ closure (g '' C ∩ interior K) :=
      (IsOpen.closure_inter isOpen_interior) ⟨hwcl, hwint⟩
    have hsub : g '' C ∩ interior K ⊆ g '' (C ∩ g ⁻¹' K) := by
      rintro y ⟨⟨z, hzC, rfl⟩, hyint⟩
      exact ⟨z, ⟨hzC, Set.mem_preimage.mpr (interior_subset hyint)⟩, rfl⟩
    exact Set.image_mono Set.inter_subset_left
      (hAimg.isClosed.closure_subset (closure_mono hsub hwm))
  -- **conclusion**: a non-empty clopen subset of the preconnected ball is the whole ball, but it
  -- cannot contain `v`
  have hball_pre : IsPreconnected (Metric.ball v ρ) := (convex_ball v ρ).isPreconnected
  have hsub_uv : Metric.ball v ρ ⊆ g '' C ∪ (closure (g '' C))ᶜ := by
    intro z hz
    by_cases h : z ∈ closure (g '' C)
    · exact Or.inl (hclosedB z hz h)
    · exact Or.inr h
  have hne_u : ((Metric.ball v ρ) ∩ g '' C).Nonempty :=
    ⟨g x, hxρ, ⟨x, hxC, rfl⟩⟩
  have hne_v : ((Metric.ball v ρ) ∩ (closure (g '' C))ᶜ).Nonempty :=
    ⟨v, Metric.mem_ball_self hρpos,
      fun hcl => hvnotin (hclosedB v (Metric.mem_ball_self hρpos) hcl)⟩
  obtain ⟨z, hz, hzg, hzcl⟩ := hball_pre (g '' C) (closure (g '' C))ᶜ hopen
    isClosed_closure.isOpen_compl hsub_uv hne_u hne_v
  exact hzcl (subset_closure hzg)

end Work.Horn.HB
