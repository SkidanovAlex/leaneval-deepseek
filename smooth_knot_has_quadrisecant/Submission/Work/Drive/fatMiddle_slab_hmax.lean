import Mathlib
import Submission.Work.Drive.fatMiddle_slab

set_option maxHeartbeats 1000000

noncomputable section

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-- **`E3a` with the maximiser exported.**  `Work.Drive.fatMiddle_slab` with the extra clause
`∀ t, ‖r' t‖ ≤ ‖r' t₀‖`: the slab centre produced by the argument is a *farthest point of `r'`*
(this is `harg` inside that proof, not currently exported).  The consumer
`Work.Drive.components_bounded_of_no_spreadQuadS` needs it, since the brick
`Work.Drive.noMiddle_near_farthest` is stated at the maximisers of `‖r'‖` and must be applied at the
slab centres `t₀ + k·period`.  (`Work.Drive.fatMiddle_slab` must remain available for
`Work.Drive.crosscut_of_close`; this is a strengthening of it, proved by reusing its proof body.) -/
theorem fatMiddle_slab_hmax {r₀ : ℝ → Space} (hr₀ : IsSmoothKnot r₀) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧
      ∀ ρ : ℝ, 0 < ρ → ∃ η : ℝ, 0 < η ∧
        ∀ r' : ℝ → Space, IsSmoothKnot r' →
          (∀ t : ℝ, ‖r' t - r₀ t‖ < ε₁ ∧ ‖velocity r' t - velocity r₀ t‖ < ε₁) →
          ∃ t₀ : ℝ, (∀ t : ℝ, ‖r' t‖ ≤ ‖r' t₀‖) ∧
            ∀ u : ℝ, Work.Drive.FatMiddle r' ρ u → ∀ k : ℤ,
              η < |u - (t₀ + (k : ℝ) * period)| := by
  obtain ⟨εs, hεspos, hsep⟩ := separation_of_far_parameters hr₀
  obtain ⟨M₀, hM₀nn, hM₀⟩ := exists_periodic_norm_bound hr₀.continuous hr₀.periodic
  obtain ⟨L₀, hL₀nn, hL₀⟩ :=
    exists_periodic_norm_bound (hr₀.smooth.continuous_deriv (by simp)) (velocity_periodic_of hr₀)
  refine ⟨min (εs / 2) (1 / 2), lt_min (by linarith) (by norm_num), ?_⟩
  intro ρ hρ
  obtain ⟨δ, hδpos, hδ⟩ := hsep ρ hρ
  set Mbar : ℝ := M₀ + 1 with hMbardef
  set L : ℝ := L₀ + 1 with hLdef
  have hMbarpos : 0 < Mbar := by rw [hMbardef]; linarith
  have hLpos : 0 < L := by rw [hLdef]; linarith
  refine ⟨δ ^ 2 / (4 * (Mbar * L)), by positivity, ?_⟩
  intro r' hr' hclose
  have he₁ : min (εs / 2) (1 / 2) ≤ εs := by
    have := min_le_left (εs / 2) (1 / 2); linarith
  have he₂ : min (εs / 2) (1 / 2) ≤ 1 / 2 := min_le_right _ _
  have hclose' : ∀ t : ℝ, ‖r' t - r₀ t‖ < εs ∧ ‖velocity r' t - velocity r₀ t‖ < εs := fun t =>
    ⟨lt_of_lt_of_le (hclose t).1 he₁, lt_of_lt_of_le (hclose t).2 he₁⟩
  have hsepr := hδ r' hr' hclose'
  -- global velocity bound for `r'`
  have hvel : ∀ t : ℝ, ‖velocity r' t‖ ≤ L := by
    intro t
    have h1 : ‖velocity r' t - velocity r₀ t‖ < 1 / 2 := lt_of_lt_of_le (hclose t).2 he₂
    have h2 : ‖velocity r₀ t‖ ≤ L₀ := hL₀ t
    have h3 : ‖velocity r' t‖ ≤ ‖velocity r₀ t‖ + ‖velocity r' t - velocity r₀ t‖ := by
      have h := norm_add_le (velocity r₀ t) (velocity r' t - velocity r₀ t)
      rwa [add_sub_cancel] at h
    rw [hLdef]; linarith
  have hlip : ∀ s t : ℝ, ‖r' t - r' s‖ ≤ L * |t - s| :=
    norm_sub_le_of_velocity_bound hr'.smooth hvel
  -- the farthest point
  obtain ⟨t₀, ht₀, hmax⟩ := isCompact_Icc.exists_isMaxOn (s := Set.Icc (0 : ℝ) period)
    ⟨0, le_rfl, period_pos.le⟩ (hr'.continuous.norm.continuousOn)
  set Mx : ℝ := ‖r' t₀‖ with hMxdef
  have hMxnn : 0 ≤ Mx := by rw [hMxdef]; exact norm_nonneg _
  have hMxle : Mx ≤ Mbar := by
    have h1 : ‖r' t₀‖ ≤ ‖r₀ t₀‖ + ‖r' t₀ - r₀ t₀‖ := by
      have h := norm_add_le (r₀ t₀) (r' t₀ - r₀ t₀)
      rwa [add_sub_cancel] at h
    have h2 : ‖r' t₀ - r₀ t₀‖ < 1 / 2 := lt_of_lt_of_le (hclose t₀).1 he₂
    have h3 : ‖r₀ t₀‖ ≤ M₀ := hM₀ t₀
    rw [hMxdef, hMbardef]; linarith
  -- every knot point is at distance at most `Mx`
  have harg : ∀ z : ℝ, ‖r' z‖ ≤ Mx := by
    intro z
    obtain ⟨z', hz', hze⟩ := hr'.periodic.exists_mem_Ico period_pos z 0
    have hmem : z' ∈ Set.Icc (0 : ℝ) period := ⟨hz'.1, by linarith [hz'.2]⟩
    calc ‖r' z‖ = ‖r' z'‖ := by rw [hze]
      _ ≤ ‖r' t₀‖ := hmax hmem
      _ = Mx := rfl
  have hmax' : ∀ z : ℝ, ‖r' z‖ ≤ Mx := harg
  have hmain : ∀ u : ℝ, FatMiddle r' ρ u → ∀ k : ℤ,
      δ ^ 2 / (4 * (Mbar * L)) < |u - (t₀ + (k : ℝ) * period)| := by
    intro u hu k
    obtain ⟨a, y, hy0, hyP, hu1, hu2, hu3⟩ := hu
    rw [openSegment_eq_image'] at hu3
    obtain ⟨θ, hθ, hθeq⟩ := hu3
    have hθeq' : r' a + θ • (r' (a + y) - r' a) = r' u := hθeq
    have hθ0 : 0 < θ := hθ.1
    have hθ1 : θ < 1 := hθ.2
    -- the two chord distances are bounded below by `δ(ρ)`
    have hsepA : δ ≤ ‖r' u - r' a‖ := by
      have hcirc : ρ ≤ circSep u a := by
        refine circSep_ge_of_abs_sub hρ ?_ ?_
        · rw [abs_of_nonneg (by linarith [hu1])]; linarith [hu1]
        · rw [abs_of_nonneg (by linarith [hu1])]; linarith [hyP]
      have h := hsepr (u : AddCircle period) (a : AddCircle period) hcirc
      rwa [knotMap_eq_of_periodic hr'.periodic u, knotMap_eq_of_periodic hr'.periodic a] at h
    have hsepB : δ ≤ ‖r' u - r' (a + y)‖ := by
      have hcirc : ρ ≤ circSep u (a + y) := by
        refine circSep_ge_of_abs_sub hρ ?_ ?_
        · rw [abs_of_nonpos (by linarith [hu2])]; linarith [hu2]
        · rw [abs_of_nonpos (by linarith [hu2])]; linarith [hyP]
      have h := hsepr (u : AddCircle period) ((a + y) : AddCircle period) hcirc
      simp only [← AddCircle.coe_add] at h
      rwa [knotMap_eq_of_periodic hr'.periodic u, knotMap_eq_of_periodic hr'.periodic (a + y)] at h
    have hsepA' : δ ≤ ‖r' a - r' u‖ := by rwa [norm_sub_rev] at hsepA
    -- the chord point is strictly inside the ball of radius `Mx`
    have hbound : ‖r' u‖ ^ 2 ≤ Mx ^ 2 - δ ^ 2 :=
      chord_deficit hθ0 hθ1 hδpos hθeq' (harg a) (harg (a + y)) hsepA' hsepB
    have hMxpos : 0 < Mx := by
      have h1 : δ ^ 2 ≤ Mx ^ 2 := by nlinarith [hbound, norm_nonneg (r' u)]
      nlinarith [h1, hδpos, hMxnn]
    -- the deficit is controlled by the distance to `t₀`
    have hdef2 : Mx ^ 2 - ‖r' u‖ ^ 2 ≤ 2 * Mx * ‖r' t₀ - r' u‖ := by
      have h := norm_sq_sub_sq_le (x := r' t₀) (y := r' u) (by have := harg u; rwa [hMxdef] at this)
      rw [hMxdef]
      exact h
    have hdef : δ ^ 2 ≤ Mx ^ 2 - ‖r' u‖ ^ 2 := by linarith
    have hdef3 : δ ^ 2 ≤ 2 * Mx * ‖r' t₀ - r' u‖ := le_trans hdef hdef2
    -- periodicity and the Lipschitz bound
    have hperk : r' (t₀ + (k : ℝ) * period) = r' t₀ := by
      have h := hr'.periodic.int_mul k t₀
      simpa [zsmul_eq_mul] using h
    have hlipk : ‖r' t₀ - r' u‖ ≤ L * |u - (t₀ + (k : ℝ) * period)| := by
      have h := hlip (t₀ + (k : ℝ) * period) u
      rw [hperk, norm_sub_rev] at h
      exact h
    have hfin : δ ^ 2 ≤ (2 * (Mx * L)) * |u - (t₀ + (k : ℝ) * period)| := by
      have hstep : (2 * Mx) * ‖r' t₀ - r' u‖
          ≤ (2 * Mx) * (L * |u - (t₀ + (k : ℝ) * period)|) :=
        mul_le_mul_of_nonneg_left hlipk (by positivity)
      have h2 : δ ^ 2 ≤ (2 * Mx) * (L * |u - (t₀ + (k : ℝ) * period)|) := le_trans hdef3 hstep
      have h3 : (2 * Mx) * (L * |u - (t₀ + (k : ℝ) * period)|)
          = (2 * (Mx * L)) * |u - (t₀ + (k : ℝ) * period)| := by ring
      rwa [h3] at h2
    exact slab_estimate hδpos hMxpos hMbarpos hMxle hLpos hfin
  exact ⟨t₀, fun z => by rw [← hMxdef]; exact hmax' z, hmain⟩

end Work.Drive
