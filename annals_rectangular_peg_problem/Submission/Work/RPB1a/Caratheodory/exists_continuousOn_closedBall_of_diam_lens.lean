import Mathlib

namespace Work.RPB1a.Caratheodory

open Complex Set Metric Filter
open scoped ContDiff Real Topology

/-- Every point of the unit sphere lies in the closure of the open unit disc. -/
private lemma sphere_subset_closure_ball : sphere (0 : ℂ) 1 ⊆ closure (ball (0 : ℂ) 1) := by
  intro ζ hζ
  rw [closure_ball (0 : ℂ) one_ne_zero, mem_closedBall]
  rw [mem_sphere] at hζ
  rw [hζ]

/-- A point of the closed disc is a limit point of the open disc. -/
private lemma neBot_nhdsWithin_ball_of_mem_closedBall {u : ℂ} (hu : u ∈ closedBall (0 : ℂ) 1) :
    (𝓝[ball (0 : ℂ) 1] u).NeBot := by
  rw [← Metric.ball_union_sphere] at hu
  rcases hu with h | h
  · exact nhdsWithin_neBot_of_mem h
  · exact mem_closure_iff_nhdsWithin_neBot.mp (sphere_subset_closure_ball h)

/-- The boundary step: if the images of all circular lenses through a boundary point of the disc
have arbitrarily small diameter, then `f` has a limit at that point along the open disc. -/
private lemma exists_tendsto_nhdsWithin_ball {f : ℂ → ℂ}
    (hb : Bornology.IsBounded (f '' ball (0 : ℂ) 1))
    (h : ∀ ζ ∈ sphere (0 : ℂ) 1, ∀ ε > 0, ∃ r > 0,
      Metric.diam (f '' (ball ζ r ∩ ball (0 : ℂ) 1)) ≤ ε)
    {ζ : ℂ} (hζ : ζ ∈ sphere (0 : ℂ) 1) :
    ∃ L, Tendsto f (𝓝[ball (0 : ℂ) 1] ζ) (𝓝 L) := by
  haveI hne : (𝓝[ball (0 : ℂ) 1] ζ).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp (sphere_subset_closure_ball hζ)
  have hcauchy : Cauchy (map f (𝓝[ball (0 : ℂ) 1] ζ)) := by
    rw [Metric.cauchy_iff]
    refine ⟨hne.map f, ?_⟩
    intro ε hε
    obtain ⟨r, hr, hdiam⟩ := h ζ hζ (ε / 2) (by linarith)
    refine ⟨f '' (ball ζ r ∩ ball (0 : ℂ) 1), ?_, ?_⟩
    · rw [Filter.mem_map]
      exact Filter.mem_of_superset (mem_nhdsWithin_iff.mpr ⟨r, hr, Subset.rfl⟩)
        (subset_preimage_image f _)
    · intro x hx y hy
      have hbS : Bornology.IsBounded (f '' (ball ζ r ∩ ball (0 : ℂ) 1)) :=
        hb.subset (image_mono inter_subset_right)
      have hle := Metric.dist_le_diam_of_mem hbS hx hy
      linarith
  obtain ⟨L, hL⟩ := CompleteSpace.complete hcauchy
  exact ⟨L, hL⟩

/-- The candidate extension: assign to every point of the closed disc the limit of `f` along the
open disc at that point (with an arbitrary value outside the closed disc). -/
private noncomputable def discExt (f : ℂ → ℂ)
    (hex : ∀ z ∈ closedBall (0 : ℂ) 1, ∃ L, Tendsto f (𝓝[ball (0 : ℂ) 1] z) (𝓝 L)) : ℂ → ℂ := by
  classical
  exact fun z => if hz : z ∈ closedBall (0 : ℂ) 1 then Classical.choose (hex z hz) else 0

private lemma discExt_spec {f : ℂ → ℂ}
    (hex : ∀ z ∈ closedBall (0 : ℂ) 1, ∃ L, Tendsto f (𝓝[ball (0 : ℂ) 1] z) (𝓝 L))
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    Tendsto f (𝓝[ball (0 : ℂ) 1] z) (𝓝 (discExt f hex z)) := by
  simp only [discExt, dif_pos hz]
  exact Classical.choose_spec (hex z hz)

/-- The value of the extension at a point of the closed disc lies in the closure of the image of
any lens through that point. -/
private lemma discExt_mem_closure_lens {f : ℂ → ℂ}
    (hex : ∀ z ∈ closedBall (0 : ℂ) 1, ∃ L, Tendsto f (𝓝[ball (0 : ℂ) 1] z) (𝓝 L))
    {u : ℂ} (hu : u ∈ closedBall (0 : ℂ) 1) {r : ℝ} (hr : 0 < r)
    (hne : (𝓝[ball (0 : ℂ) 1] u).NeBot) :
    discExt f hex u ∈ closure (f '' (ball u r ∩ ball (0 : ℂ) 1)) := by
  refine Metric.mem_closure_iff.mpr ?_
  intro δ hδ
  have hT : f ⁻¹' (ball (discExt f hex u) δ) ∈ 𝓝[ball (0 : ℂ) 1] u :=
    (Metric.tendsto_nhds.mp (discExt_spec hex hu)) δ hδ
  rw [mem_nhdsWithin_iff] at hT
  obtain ⟨ε, hε, hεT⟩ := hT
  have hmin : (0 : ℝ) < min ε r := lt_min hε hr
  have hmem : ball u (min ε r) ∩ ball (0 : ℂ) 1 ∈ 𝓝[ball (0 : ℂ) 1] u :=
    mem_nhdsWithin_iff.mpr ⟨min ε r, hmin, Subset.rfl⟩
  obtain ⟨w, hw⟩ := hne.nonempty_of_mem hmem
  refine ⟨f w, ?_, ?_⟩
  · refine ⟨w, ?_, rfl⟩
    exact ⟨lt_of_lt_of_le (mem_ball.mp hw.1) (min_le_right _ _), hw.2⟩
  · have hw' : w ∈ ball u ε ∩ ball (0 : ℂ) 1 :=
      ⟨lt_of_lt_of_le (mem_ball.mp hw.1) (min_le_left _ _), hw.2⟩
    have : f w ∈ ball (discExt f hex u) δ := hεT hw'
    rwa [mem_ball, dist_comm] at this

/-- Extension criterion: a continuous map on the open unit disc with bounded image, whose images of
the crosscut lenses `ball ζ r ∩ ball 0 1` have arbitrarily small diameter at every boundary point
`ζ` of the disc, extends continuously to the closed disc. -/
theorem exists_continuousOn_closedBall_of_diam_lens {f : ℂ → ℂ}
    (hf : ContinuousOn f (ball 0 1)) (hb : Bornology.IsBounded (f '' ball 0 1))
    (h : ∀ ζ ∈ sphere 0 1, ∀ ε > 0, ∃ r > 0, Metric.diam (f '' (ball ζ r ∩ ball 0 1)) ≤ ε) :
    ∃ F : ℂ → ℂ, ContinuousOn F (closedBall 0 1) ∧ EqOn F f (ball 0 1) := by
  have hex : ∀ z ∈ closedBall (0 : ℂ) 1, ∃ L, Tendsto f (𝓝[ball (0 : ℂ) 1] z) (𝓝 L) := by
    intro z hz
    rw [← Metric.ball_union_sphere] at hz
    rcases hz with hzb | hzs
    · exact ⟨f z, hf z hzb⟩
    · exact exists_tendsto_nhdsWithin_ball hb h hzs
  refine ⟨discExt f hex, ?_, ?_⟩
  · refine Metric.continuousOn_iff'.mpr ?_
    intro z hz ε hε
    rw [← Metric.ball_union_sphere] at hz
    rcases hz with hzb | hzs
    · -- interior point of the disc
      have hFf : ∀ w ∈ ball (0 : ℂ) 1, discExt f hex w = f w := by
        intro w hw
        haveI : (𝓝[ball (0 : ℂ) 1] w).NeBot := nhdsWithin_neBot_of_mem hw
        exact tendsto_nhds_unique (discExt_spec hex (ball_subset_closedBall hw)) (hf w hw)
      have hcontAt : ContinuousAt f z := hf.continuousAt (isOpen_ball.mem_nhds hzb)
      have hA : ∀ᶠ w in 𝓝[closedBall (0 : ℂ) 1] z, w ∈ ball (0 : ℂ) 1 :=
        nhdsWithin_le_nhds (isOpen_ball.mem_nhds hzb)
      have hB : ∀ᶠ w in 𝓝[closedBall (0 : ℂ) 1] z, dist (f w) (f z) < ε :=
        (Metric.continuousAt_iff'.mp hcontAt ε hε).filter_mono nhdsWithin_le_nhds
      exact (hA.and hB).mono (fun w hw => by rw [hFf w hw.1, hFf z hzb]; exact hw.2)
    · -- boundary point of the disc
      have hne : (𝓝[ball (0 : ℂ) 1] z).NeBot :=
        neBot_nhdsWithin_ball_of_mem_closedBall (Metric.sphere_subset_closedBall hzs)
      obtain ⟨r, hr, hdiam⟩ := h z hzs (ε / 2) (by linarith)
      have hFz : discExt f hex z ∈ closure (f '' (ball z r ∩ ball (0 : ℂ) 1)) :=
        discExt_mem_closure_lens hex (Metric.sphere_subset_closedBall hzs) hr hne
      have hmem : ball z (r / 2) ∩ closedBall (0 : ℂ) 1 ∈ 𝓝[closedBall (0 : ℂ) 1] z :=
        mem_nhdsWithin_iff.mpr ⟨r / 2, by linarith, subset_refl _⟩
      refine Filter.mem_of_superset hmem ?_
      intro w hw
      show dist (discExt f hex w) (discExt f hex z) < ε
      have hwcb : w ∈ closedBall (0 : ℂ) 1 := hw.2
      have hwd : dist w z < r / 2 := mem_ball.mp hw.1
      have hne' : (𝓝[ball (0 : ℂ) 1] w).NeBot := neBot_nhdsWithin_ball_of_mem_closedBall hwcb
      have hFw : discExt f hex w ∈ closure (f '' (ball w (r / 2) ∩ ball (0 : ℂ) 1)) :=
        discExt_mem_closure_lens hex hwcb (by linarith) hne'
      have hsub : ball w (r / 2) ∩ ball (0 : ℂ) 1 ⊆ ball z r ∩ ball (0 : ℂ) 1 := by
        intro y hy
        refine ⟨?_, hy.2⟩
        have hyw : dist y w < r / 2 := mem_ball.mp hy.1
        calc dist y z ≤ dist y w + dist w z := dist_triangle y w z
          _ < r / 2 + r / 2 := by linarith
          _ = r := by ring
      have hFwS : discExt f hex w ∈ closure (f '' (ball z r ∩ ball (0 : ℂ) 1)) :=
        closure_mono (image_mono hsub) hFw
      have hine : ediam (closure (f '' (ball z r ∩ ball (0 : ℂ) 1))) ≠ ⊤ :=
        Metric.isBounded_iff_ediam_ne_top.mp
          ((hb.subset (image_mono inter_subset_right)).closure)
      have hle := Metric.dist_le_diam_of_mem' hine hFwS hFz
      rw [Metric.diam_closure] at hle
      linarith
  · intro z hz
    haveI : (𝓝[ball (0 : ℂ) 1] z).NeBot := nhdsWithin_neBot_of_mem hz
    exact tendsto_nhds_unique (discExt_spec hex (ball_subset_closedBall hz)) (hf z hz)

end Work.RPB1a.Caratheodory
