import Mathlib
import Submission.Work.Pert.pert2v2.EfFloorDiffV2.Prelim
import Submission.Work.Pert.MaxDom

/-!
# `Work.Pert.pert2v2.EfFloorDiffV2.seedP_germ_add_one`

The level-one structure `hlvl` of the gate,

`Φp (invOn Φm Q (w - ⌊Re w⌋ + 1)) = Φp (invOn Φm Q (w - ⌊Re w⌋)) + 1   (y ≤ Im w)`,

is *local*: it holds, for a whole ball around `u`, for every shift `τ` and not only for the
canonical representative.  This is what makes the floor extension `EfFloor` holomorphic on the
band `{y ≤ Im}` (see `EfFloor_sub_id_differentiableOn`).

The two ingredients:

* the gate image `Φm '' Q` is **open** (`isOpen_image_of_deriv_ne_zero`), so both `z` and `z + 1`
  remain gate values near `u` (giving a holomorphic domain);
* the *window* form of `hlvl` (`EfFloorDiffV2.seedP_add_one_of_re_Ico`): on the closed window
  `Re z ∈ [0,1)`, `Im z ≥ y`, the seed value of `z + 1` is that of `z` plus `1`.

The function `G z = seedP (z+1) - seedP z - 1` is holomorphic on the open set
`U = {z | z ∈ Φm '' Q, z + 1 ∈ Φm '' Q}` and vanishes on the *open* piece
`{0 < Re z < 1, y < Im z} ∩ U` of it.  Since `Re u ∈ [0,1)` and `y ≤ Im u`, the small
north-east shift `u + t + i t` (`t > 0`) lies in that piece and in the same ball `B(u,r) ⊆ U`;
the identity theorem on the preconnected ball `B(u,r)` then gives `G = 0` on all of it.
-/

namespace Work.Pert.pert2v2.EfFloorDiffV2

open Complex Set Filter
open scoped Topology

noncomputable section

/-- **The gate image is open**: the image of an open set under a holomorphic map with
nowhere-vanishing derivative is a neighbourhood of each of its points, hence open. -/
theorem isOpen_image_of_deriv_ne_zero {Φ : ℂ → ℂ} {Q : Set ℂ} (hQ : IsOpen Q)
    (hΦ : DifferentiableOn ℂ Φ Q) (hder : ∀ z ∈ Q, deriv Φ z ≠ 0) : IsOpen (Φ '' Q) := by
  rw [isOpen_iff_mem_nhds]
  rintro w ⟨ζ, hζ, rfl⟩
  exact mem_nhds_image_of_deriv_ne_zero hQ hΦ hζ (hder ζ hζ)

theorem seedP_germ_add_one {Φm Φp : ℂ → ℂ} {Q : Set ℂ} {y : ℝ}
    (hQopen : IsOpen Q) (hΦm : DifferentiableOn ℂ Φm Q) (hder : ∀ z ∈ Q, deriv Φm z ≠ 0)
    (hInj : Set.InjOn Φm Q) (hΦp : DifferentiableOn ℂ Φp Q)
    (hlvl : ∀ w : ℂ, y ≤ w.im → w - (((Int.floor w.re : ℤ)) : ℂ) + 1 ∈ Φm '' Q →
      Φp (Work.Pert.invOn Φm Q (w - (((Int.floor w.re : ℤ)) : ℂ) + 1))
        = Φp (Work.Pert.invOn Φm Q (w - (((Int.floor w.re : ℤ)) : ℂ))) + 1)
    {u : ℂ} (hu : u ∈ Φm '' Q) (hu1 : u + 1 ∈ Φm '' Q) (him : y ≤ u.im)
    (hre : u.re ∈ Set.Ico 0 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ τ : ℂ, ‖τ‖ < δ →
      Work.Pert.seedP Φp Φm Q (u + 1 + τ) = Work.Pert.seedP Φp Φm Q (u + τ) + 1 := by
  classical
  -- the gate image is open and the seed value is holomorphic on it
  have hVopen : IsOpen (Φm '' Q) := isOpen_image_of_deriv_ne_zero hQopen hΦm hder
  have hseed : DifferentiableOn ℂ (Work.Pert.seedP Φp Φm Q) (Φm '' Q) :=
    Work.Pert.seedP_holo hQopen hΦm hΦp hInj hder
  -- the open set on which the two-point relation makes sense
  set U : Set ℂ := (Φm '' Q) ∩ {z : ℂ | z + 1 ∈ Φm '' Q} with hU
  set G : ℂ → ℂ := fun z => Work.Pert.seedP Φp Φm Q (z + 1) - Work.Pert.seedP Φp Φm Q z - 1
    with hG
  have hUopen : IsOpen U := by
    rw [hU]
    exact hVopen.inter (hVopen.preimage (continuous_id.add continuous_const))
  have huU : u ∈ U := by
    rw [hU]; exact ⟨hu, by simpa using hu1⟩
  have hGdiff : DifferentiableOn ℂ G U := by
    rw [hG, hU]
    have hplus : DifferentiableOn ℂ (fun z : ℂ => z + 1)
        ((Φm '' Q) ∩ {z : ℂ | z + 1 ∈ Φm '' Q}) :=
      fun z _ => (differentiableAt_id.add_const 1).differentiableWithinAt
    have h1 : DifferentiableOn ℂ (fun z : ℂ => Work.Pert.seedP Φp Φm Q (z + 1))
        ((Φm '' Q) ∩ {z : ℂ | z + 1 ∈ Φm '' Q}) :=
      hseed.comp hplus (fun z hz => hz.2)
    exact (h1.sub (hseed.mono Set.inter_subset_left)).sub_const 1
  -- the window form of the level-one structure
  have hzero : ∀ z : ℂ, z + 1 ∈ Φm '' Q → y ≤ z.im → z.re ∈ Set.Ico 0 1 → G z = 0 := by
    intro z hz1 hzim hzre
    have h := seedP_add_one_of_re_Ico hlvl hzim hzre hz1
    rw [hG]
    show Work.Pert.seedP Φp Φm Q (z + 1) - Work.Pert.seedP Φp Φm Q z - 1 = 0
    rw [h]; ring
  -- a ball around `u` contained in `U`
  obtain ⟨r, hrpos, hrball⟩ : ∃ r : ℝ, 0 < r ∧ Metric.ball u r ⊆ U := by
    have hmem : U ∈ 𝓝 u := hUopen.mem_nhds huU
    rwa [Metric.mem_nhds_iff] at hmem
  -- the north-east shift `z₀ = u + t + i t`, which lies in the open piece `{0 < Re, y < Im}`
  set t : ℝ := min (r / 4) ((1 - u.re) / 2) with ht
  have htpos : 0 < t := by
    rw [ht]; exact lt_min (by linarith) (by linarith [hre.2])
  have ht4 : t ≤ r / 4 := by rw [ht]; exact min_le_left _ _
  have ht1 : u.re + t < 1 := by
    have h : min (r / 4) ((1 - u.re) / 2) ≤ (1 - u.re) / 2 := min_le_right _ _
    rw [← ht] at h; linarith
  have ht0 : 0 < u.re + t := by linarith [hre.1]
  have hty : y < u.im + t := by linarith [him]
  set z₀ : ℂ := u + (t : ℂ) + (t : ℂ) * I with hz0
  have hz0re : z₀.re = u.re + t := by rw [hz0]; simp
  have hz0im : z₀.im = u.im + t := by rw [hz0]; simp
  have hz0ball : z₀ ∈ Metric.ball u r := by
    rw [Metric.mem_ball, Complex.dist_eq]
    have hsub : z₀ - u = (t : ℂ) + (t : ℂ) * I := by rw [hz0]; ring
    rw [hsub]
    have h1 : ‖(t : ℂ) + (t : ℂ) * I‖ ≤ ‖(t : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
    have h2 : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
    have h3 : ‖(t : ℂ) * I‖ = t := by rw [norm_mul, Complex.norm_I, mul_one, h2]
    rw [h2, h3] at h1
    linarith
  -- the open set on which `G` is known to vanish
  set W : Set ℂ := {z : ℂ | z.re ∈ Set.Ioo 0 1} ∩ {z : ℂ | y < z.im} ∩ Metric.ball u r with hW
  have hWopen : IsOpen W := by
    rw [hW]
    exact ((isOpen_Ioo.preimage Complex.continuous_re).inter
      (isOpen_Ioi.preimage Complex.continuous_im)).inter Metric.isOpen_ball
  have hz0W : z₀ ∈ W := by
    rw [hW]
    refine ⟨⟨?_, ?_⟩, hz0ball⟩
    · change z₀.re ∈ Set.Ioo 0 1
      rw [hz0re]; exact ⟨ht0, ht1⟩
    · change y < z₀.im
      rw [hz0im]; exact hty
  have hev : G =ᶠ[𝓝 z₀] 0 := by
    filter_upwards [hWopen.mem_nhds hz0W] with z hz
    rw [hW] at hz
    obtain ⟨⟨hzre, hzim⟩, hzball⟩ := hz
    have hUz : z ∈ U := hrball hzball
    rw [hU] at hUz
    exact hzero z hUz.2 (le_of_lt hzim) ⟨le_of_lt hzre.1, hzre.2⟩
  -- identity theorem on the preconnected ball
  have hGan : AnalyticOnNhd ℂ G (Metric.ball u r) :=
    (hGdiff.mono hrball).analyticOnNhd Metric.isOpen_ball
  have hball0 : ∀ z ∈ Metric.ball u r, G z = 0 :=
    hGan.eqOn_zero_of_preconnected_of_eventuallyEq_zero Metric.isPreconnected_ball hz0ball hev
  refine ⟨r, hrpos, fun τ hτ => ?_⟩
  have hmemτ : u + τ ∈ Metric.ball u r := by
    rw [Metric.mem_ball, Complex.dist_eq]
    have hsub : u + τ - u = τ := by ring
    rw [hsub]; exact hτ
  have hz := hball0 (u + τ) hmemτ
  rw [hG] at hz
  change Work.Pert.seedP Φp Φm Q (u + τ + 1) - Work.Pert.seedP Φp Φm Q (u + τ) - 1 = 0 at hz
  have harg : u + τ + 1 = u + 1 + τ := by ring
  rw [harg] at hz
  linear_combination hz

end

end Work.Pert.pert2v2.EfFloorDiffV2
