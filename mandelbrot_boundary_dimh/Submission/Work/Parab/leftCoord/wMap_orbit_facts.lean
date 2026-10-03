import Mathlib
import Submission.Work.FatouCoord.Setup
import Submission.Work.FatouCoord.Estimate.wMap_iterate_deriv_bound
import Submission.Work.Parab.leftCoord.wMap_large_estimates
import Submission.Work.Parab.leftCoord.wMap_orbit_estimates

/-!
# Orbit facts for the chart dynamics `wMap`

For a parabolic germ `f z = z + z ^ 2 h z` collected in `ParabolicBounds f h a r A A'` this
file packages, at a single level `N`, the facts about the chart dynamics
`wMap f w = -1 / f (-1/w)` that the construction of the left chart coordinate uses:

* `wMap f` moves every point with `x.re > N` strictly to the right;
* `wMap f` is complex differentiable at every point with `‖w‖ > N`;
* `wMap f` is injective on `{w | N < ‖w‖}`;
* the real part never decreases along an orbit through `{‖w‖ > N}`.

The first and the last are immediate from `wMap_step_bound_norm` (companion file
`wMap_orbit_estimates`: the orbit moves right by at least `1/2` per step), differentiability is
`differentiableAt_wMap` (`FatouCoord/Estimate/wMap_iterate_deriv_bound`), and injectivity is
obtained from the injectivity of the germ `f` near `0` (`injOn_ball_of_parabolicBounds` below),
transported through the chart `w ↦ -1/w`, which is injective on `ℂ \ {0}`.

The injectivity of the germ is the mean value inequality on a small convex disc applied to
`G u = f u - u` (with `deriv_f`): on `ball 0 ρ` one has `‖deriv G u‖ = ‖2 u h u + u² h' u‖ ≤
4ρ + A'ρ² ≤ 1/2`, so `‖(f z - z) - (f w - w)‖ ≤ ‖z - w‖/2`; if `f z = f w` with `z ≠ w` this
reads `‖z - w‖ ≤ ‖z - w‖/2`, a contradiction.
-/

namespace Work.Parab.leftCoord

open Work.FatouCoord
open scoped Topology
open Set Filter Metric Function

noncomputable section

variable {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}

/-! ## Injectivity of the germ near the parabolic point -/

/-- **The parabolic germ is injective near `0`.**  There is `ρ ∈ (0, r]` such that `f` is
injective on the disc `ball 0 ρ`: on that disc `f z = z + z² h z` and the correction `z ↦ z² h z`
has derivative `2 z h z + z² h' z`, of norm at most `4ρ + A' ρ² ≤ 1/2` there. -/
theorem injOn_ball_of_parabolicBounds (hb : ParabolicBounds f h a r A A') :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ r ∧ Set.InjOn f (ball 0 ρ) := by
  have hA'0 : 0 ≤ A' := hb.hA'
  set ρ : ℝ := min (r / 2) (1 / (16 * (1 + A'))) with hρdef
  have hρpos : 0 < ρ := by
    rw [hρdef]
    exact lt_min (by linarith [hb.hr]) (one_div_pos.mpr (by linarith))
  have hρr : ρ ≤ r := by
    rw [hρdef]
    exact le_trans (min_le_left _ _) (by linarith [hb.hr])
  have hρ16 : ρ ≤ 1 / (16 * (1 + A')) := by rw [hρdef]; exact min_le_right _ _
  have hρkey : 4 * ρ + A' * ρ ^ 2 ≤ 1 / 2 := by
    have h1 : 4 * ρ ≤ 4 * (1 / (16 * (1 + A'))) := by linarith [hρ16]
    have h2 : ρ ≤ 1 := by
      have h3 : 1 / (16 * (1 + A')) ≤ 1 := by
        rw [div_le_one (by linarith)]; linarith
      linarith [hρ16]
    have h3 : ρ ^ 2 ≤ ρ := by nlinarith [hρpos, h2]
    have h4 : A' * ρ ^ 2 ≤ A' * ρ := mul_le_mul_of_nonneg_left h3 hA'0
    have h5 : A' * ρ ≤ A' * (1 / (16 * (1 + A'))) := mul_le_mul_of_nonneg_left hρ16 hA'0
    have h6 : A' * (1 / (16 * (1 + A'))) ≤ 1 / 16 := by
      rw [mul_one_div, div_le_iff₀ (by linarith)]
      linarith
    have h7 : 4 * (1 / (16 * (1 + A'))) ≤ 1 / 4 := by
      rw [mul_one_div, div_le_iff₀ (by linarith)]
      linarith
    linarith
  refine ⟨ρ, hρpos, hρr, ?_⟩
  intro z hz w hw hzw
  have hconv : Convex ℝ (ball (0 : ℂ) ρ) := convex_ball 0 ρ
  have hsub : ball (0 : ℂ) ρ ⊆ ball (0 : ℂ) r := by
    intro u hu; rw [mem_ball_zero_iff] at *; linarith
  have hdiff : ∀ u ∈ ball (0 : ℂ) ρ, DifferentiableAt ℂ (fun u : ℂ => f u - u) u := by
    intro u hu
    exact (Work.FatouCoord.Estimate.differentiableAt_f hb (hsub hu)).sub differentiableAt_id
  have hbound : ∀ u ∈ ball (0 : ℂ) ρ, ‖deriv (fun u : ℂ => f u - u) u‖ ≤ 1 / 2 := by
    intro u hu
    have hur : u ∈ ball (0 : ℂ) r := hsub hu
    have hun : ‖u‖ < ρ := by rwa [mem_ball_zero_iff] at hu
    have hder : deriv (fun u : ℂ => f u - u) u = deriv f u - 1 := by
      change deriv (f - id) u = deriv f u - 1
      rw [deriv_sub (Work.FatouCoord.Estimate.differentiableAt_f hb hur) differentiableAt_id,
        deriv_id]
    rw [hder, Work.FatouCoord.Estimate.deriv_f hb hur,
      show 1 + 2 * u * h u + u ^ 2 * deriv h u - 1 = 2 * u * h u + u ^ 2 * deriv h u by ring]
    have h1 : ‖2 * u * h u‖ ≤ 4 * ρ := by
      have hbnd := hb.h_bound u hur
      have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [norm_mul, norm_mul, htwo]
      calc (2 : ℝ) * ‖u‖ * ‖h u‖ ≤ (2 * ρ) * 2 :=
            mul_le_mul (by linarith [hun.le]) hbnd (norm_nonneg _) (by positivity)
        _ = 4 * ρ := by ring
    have h3 : ‖u ^ 2 * deriv h u‖ ≤ A' * ρ ^ 2 := by
      rw [norm_mul, norm_pow]
      calc ‖u‖ ^ 2 * ‖deriv h u‖ ≤ ρ ^ 2 * A' :=
            mul_le_mul (by nlinarith [hun.le, norm_nonneg u])
              (hb.h_deriv_bound u hur) (norm_nonneg _) (by positivity)
        _ = A' * ρ ^ 2 := by ring
    calc ‖2 * u * h u + u ^ 2 * deriv h u‖ ≤ ‖2 * u * h u‖ + ‖u ^ 2 * deriv h u‖ :=
          norm_add_le _ _
      _ ≤ 4 * ρ + A' * ρ ^ 2 := by linarith
      _ ≤ 1 / 2 := hρkey
  have hmvt := hconv.norm_image_sub_le_of_norm_deriv_le hdiff hbound hz hw
  have heq : (f w - w) - (f z - z) = z - w := by rw [hzw]; ring
  have h2 : ‖z - w‖ ≤ (1 / 2) * ‖z - w‖ := by
    rw [heq, norm_sub_rev w z] at hmvt
    exact hmvt
  have h0 : ‖z - w‖ = 0 := by nlinarith [norm_nonneg (z - w)]
  have hzw0 : z - w = 0 := norm_eq_zero.mp h0
  exact sub_eq_zero.mp hzw0

/-! ## Transport through the chart -/

/-- Transporting injectivity through the chart: if `f` is injective on the disc `ball 0 ρ` and
every point of `S` has its chart image in that disc, then `wMap f` is injective on `S`. -/
theorem injOn_wMap_of_injOn_ball {ρ : ℝ} (hinj : Set.InjOn f (ball 0 ρ)) {S : Set ℂ}
    (hS : ∀ x ∈ S, x ≠ 0 ∧ chart x ∈ ball 0 ρ) : Set.InjOn (wMap f) S := by
  intro x hx y hy hxy
  obtain ⟨hx0, hxc⟩ := hS x hx
  obtain ⟨hy0, hyc⟩ := hS y hy
  have hf : f (chart x) = f (chart y) := chart_injective hxy
  have hcc : chart x = chart y := hinj hxc hyc hf
  rw [← chart_chart hx0, hcc, chart_chart hy0]

/-! ## The orbit facts -/

theorem wMap_orbit_facts {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}
    (hb : Work.FatouCoord.ParabolicBounds f h a r A A') :
    ∃ N : ℝ, 0 < N ∧ 1 / r < N ∧
      (∀ x : ℂ, N < x.re → N < (Work.FatouCoord.wMap f x).re) ∧
      (∀ x : ℂ, N < ‖x‖ → DifferentiableAt ℂ (Work.FatouCoord.wMap f) x) ∧
      (Set.InjOn (Work.FatouCoord.wMap f) {x : ℂ | N < ‖x‖}) ∧
      (∀ x : ℂ, N < ‖x‖ → x.re ≤ (Work.FatouCoord.wMap f x).re) := by
  obtain ⟨N₀, K, hN₀pos, hN₀r, hK, hstep⟩ := wMap_step_bound_norm hb
  obtain ⟨ρ, hρpos, hρr, hinj⟩ := injOn_ball_of_parabolicBounds hb
  have hρpos' : 0 < 1 / ρ := one_div_pos.mpr hρpos
  -- the level of the estimates
  set N : ℝ := max (max N₀ (1 / ρ)) 4 + 1 with hNdef
  have hmaxN : max (max N₀ (1 / ρ)) 4 < N := by rw [hNdef]; linarith
  have hN₀N : N₀ < N :=
    lt_of_le_of_lt (le_trans (le_max_left N₀ (1 / ρ)) (le_max_left (max N₀ (1 / ρ)) 4)) hmaxN
  have h1ρN : 1 / ρ < N :=
    lt_of_le_of_lt (le_trans (le_max_right N₀ (1 / ρ)) (le_max_left (max N₀ (1 / ρ)) 4)) hmaxN
  have h4N : (4 : ℝ) < N := lt_of_le_of_lt (le_max_right (max N₀ (1 / ρ)) 4) hmaxN
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4) h4N.le
  have hNr : 1 / r < N := lt_trans hN₀r hN₀N
  refine ⟨N, hNpos, hNr, ?_, ?_, ?_, ?_⟩
  · -- `wMap f` moves large points strictly to the right
    intro x hx
    have hxnorm : N < ‖x‖ := lt_of_lt_of_le hx (Complex.re_le_norm x)
    have h := (hstep x (lt_trans hN₀N hxnorm)).2
    linarith
  · -- differentiability on `{N < ‖·‖}`
    intro x hx
    exact Work.FatouCoord.Estimate.differentiableAt_wMap hb (lt_trans hNr hx)
      (le_of_lt (lt_trans h4N hx))
  · -- injectivity on `{N < ‖·‖}`
    refine injOn_wMap_of_injOn_ball hinj ?_
    intro x hx
    have hxn : 0 < ‖x‖ := lt_trans hNpos hx
    have hx0 : x ≠ 0 := norm_pos_iff.mp hxn
    refine ⟨hx0, ?_⟩
    have hgoal : 1 / ‖x‖ < ρ := by
      rw [div_lt_iff₀ hxn]
      have h := (div_lt_iff₀ hρpos).mp (lt_trans h1ρN hx)
      linarith
    simpa only [mem_ball_zero_iff, norm_chart hx0, one_div] using hgoal
  · -- the real part is nondecreasing along large orbits
    intro x hx
    have h := (hstep x (lt_trans hN₀N hx)).2
    linarith

end

end Work.Parab.leftCoord
